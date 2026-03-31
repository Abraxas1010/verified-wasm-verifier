import Lean
import HeytingLean.CLI.EnvBootstrap
import HeytingLean.Util.ModuleOwner

namespace HeytingLean
namespace LoF
namespace ICC
namespace Encoder

open Lean

structure DeclSummary where
  declName : Name
  moduleName : Name
  declKind : String
  proofBodyVisible : Bool
  directRefs : Array Name
  closure : Array Name
  missingDeps : Array Name
  closureOverflow : Bool
  deriving Repr

def constKind : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def constantValueExpr? : ConstantInfo → Option Expr
  | .defnInfo info => some info.value
  | .opaqueInfo info => some info.value
  | .thmInfo info => some info.value
  | _ => none

def isCheckableDecl : ConstantInfo → Bool
  | .defnInfo _ | .opaqueInfo _ | .thmInfo _ => true
  | _ => false

private def declSelectionPriority (env : Environment) (declName : Name) : Nat :=
  if declName.isInternal || declName.isInternalDetail || Lean.isPrivateName declName then
    2
  else if env.isProjectionFn declName then
    1
  else
    0

def isSurfaceDecl (env : Environment) (declName : Name) (ci : ConstantInfo) : Bool :=
  isCheckableDecl ci &&
    !(declName.isInternal || declName.isInternalDetail || Lean.isPrivateName declName || env.isProjectionFn declName)

partial def collectConstRefs (e : Expr) (acc : Std.HashSet Name := {}) : Std.HashSet Name :=
  match e with
  | .const n _ => acc.insert n
  | .app f a => collectConstRefs a (collectConstRefs f acc)
  | .lam _ ty body _ => collectConstRefs body (collectConstRefs ty acc)
  | .forallE _ ty body _ => collectConstRefs body (collectConstRefs ty acc)
  | .letE _ ty val body _ => collectConstRefs body (collectConstRefs val (collectConstRefs ty acc))
  | .mdata _ body => collectConstRefs body acc
  | .proj _ _ body => collectConstRefs body acc
  | _ => acc

def directRefsOfConstInfo (ci : ConstantInfo) : Array Name :=
  let typeRefs := collectConstRefs ci.type
  let refs :=
    match constantValueExpr? ci with
    | some value => collectConstRefs value typeRefs
    | none => typeRefs
  refs.toList.toArray.qsort (·.toString < ·.toString)

private def closureRefsOfConstInfo (ci : ConstantInfo) : Array Name :=
  let typeRefs := collectConstRefs ci.type
  let refs :=
    match ci with
    | .defnInfo info => collectConstRefs info.value typeRefs
    | _ => typeRefs
  refs.toList.toArray.qsort (·.toString < ·.toString)

def moduleNameOfDecl (env : Environment) (declName : Name) : Name :=
  HeytingLean.Util.moduleOwnerOf env declName

def moduleDecls (env : Environment) (moduleName : Name) : Array (Name × ConstantInfo) :=
  let raw := env.constants.fold (init := #[]) fun acc name info =>
    if moduleNameOfDecl env name == moduleName then
      acc.push (name, info)
    else
      acc
  raw.qsort (fun a b =>
    let pa := declSelectionPriority env a.1
    let pb := declSelectionPriority env b.1
    if pa == pb then
      a.1.toString < b.1.toString
    else
      pa < pb)

def computeClosure (env : Environment) (targetName : Name) (maxConsts : Nat := 512) :
    Array Name × Bool × Array Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut queue : List Name := [targetName]
  let mut out : Array Name := #[]
  let mut missing : Std.HashSet Name := {}
  let mut overflow := false
  while !queue.isEmpty && !overflow do
    match queue with
    | [] => pure ()
    | name :: rest =>
        queue := rest
        if seen.contains name then
          pure ()
        else if out.size >= maxConsts then
          overflow := true
        else
          seen := seen.insert name
          out := out.push name
          match env.find? name with
          | none =>
              missing := missing.insert name
          | some ci =>
              for dep in closureRefsOfConstInfo ci do
                if !seen.contains dep then
                  queue := dep :: queue
  (out, overflow, missing.toList.toArray.qsort (·.toString < ·.toString))

def summarizeDecl (env : Environment) (declName : Name) (ci : ConstantInfo) (maxConsts : Nat := 512) :
    DeclSummary :=
  let directRefs := directRefsOfConstInfo ci
  let (closure, closureOverflow, missingDeps) := computeClosure env declName maxConsts
  { declName := declName
    moduleName := moduleNameOfDecl env declName
    declKind := constKind ci
    proofBodyVisible := (constantValueExpr? ci).isSome
    directRefs := directRefs
    closure := closure
    missingDeps := missingDeps
    closureOverflow := closureOverflow }

def nameOfDotted (text : String) : Name :=
  HeytingLean.CLI.EnvBootstrap.moduleNameFromString text

def ownerModuleOfDeclString (declText : String) : Name :=
  let parts := declText.splitOn "."
  match parts.reverse.drop 1 |>.reverse with
  | [] => nameOfDotted declText
  | xs => nameOfDotted (String.intercalate "." xs)

end Encoder
end ICC
end LoF
end HeytingLean
