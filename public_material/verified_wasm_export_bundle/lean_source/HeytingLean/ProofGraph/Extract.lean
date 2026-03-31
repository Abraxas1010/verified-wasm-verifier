import Lean
import HeytingLean.CLI.EnvBootstrap
import HeytingLean.ProofGraph.Core
import HeytingLean.ProofGraph.ExprDAG
import HeytingLean.ProofGraph.InfoTreeExtract
import HeytingLean.ProofGraph.VerifierWitness

namespace HeytingLean.ProofGraph

open Lean

def nameOfDotted (s : String) : Name :=
  s.splitOn "." |>.foldl (fun n part => Name.str n part) Name.anonymous

private def moduleCandidatesOfConst (constName : String) : List Name :=
  let parts := constName.splitOn "."
  let rec go : Nat → List Name
    | 0 => []
    | n + 1 =>
        if 2 ≤ n + 1 then
          let prefixText := String.intercalate "." (parts.take (n + 1))
          HeytingLean.CLI.EnvBootstrap.moduleNameFromString prefixText :: go n
        else
          []
  go (parts.length - 1)

private def tryImportModules : List Name → IO (Option Environment)
  | [] => pure none
  | moduleName :: rest => do
      try
        let env ← importModules #[{ module := `Init }, { module := moduleName }] {}
        pure (some env)
      catch _ =>
        tryImportModules rest

def importProject (extraModules : List String) (constName? : Option String := none) : IO Environment := do
  HeytingLean.CLI.EnvBootstrap.bootstrapSearchPath
  let extras : Array Import := extraModules.toArray.map (fun s => { module := nameOfDotted s })
  if !extras.isEmpty then
    importModules (#[{ module := `Init }] ++ extras) {}
  else
    let candidates := constName?.map moduleCandidatesOfConst |>.getD []
    match ← tryImportModules candidates with
    | some env => pure env
    | none => importModules #[{ module := `Init }, { module := `HeytingLean }] {}

def findConst (env : Environment) (full : String) : Option Name :=
  env.constants.toList.findSome? fun (n, _) => if n.toString = full then some n else none

def constantValueExpr? : ConstantInfo → Option Expr
  | .thmInfo _ => none
  | .opaqueInfo info => some info.value
  | .defnInfo info => some info.value
  | _ => none

def declKindStr : ConstantInfo → String
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def proofSourceOf : ConstantInfo → ProofSource
  | .defnInfo _ => .kernelValue
  | .opaqueInfo _ => .kernelValue
  | .thmInfo _ => .erased
  | .axiomInfo _ => .unavailable
  | .quotInfo _ => .unavailable
  | .inductInfo _ => .unavailable
  | .ctorInfo _ => .unavailable
  | .recInfo _ => .unavailable

def extractGraph (declName : Name) (ci : ConstantInfo) (fuel : Nat) : ProofGraph :=
  let proofExpr? := constantValueExpr? ci
  let extracted := extractDeclGraph declName ci.type proofExpr? fuel
  let info := emptyInfoTreeAttachment
  let verifier := emptyVerifierAttachment
  let graph : ProofGraph :=
    { targetDecl := declName
    , moduleName := moduleOfDecl declName
    , declKind := declKindStr ci
    , proofSource := proofSourceOf ci
    , infotreeSource := info.source
    , roots :=
        { typeRoot := extracted.typeRoot
        , proofRoot? := extracted.proofRoot?
        , infotreeRoot? := info.root?
        , verifierRoot? := verifier.root?
        }
    , nodes := extracted.nodes ++ info.nodes ++ verifier.nodes
    , edges := extracted.edges ++ info.edges ++ verifier.edges
    , witnesses := verifier.witnesses
    , metrics := { sharedExprNodes := extracted.sharedExprNodes }
    }
  withFreshMetrics graph

end HeytingLean.ProofGraph
