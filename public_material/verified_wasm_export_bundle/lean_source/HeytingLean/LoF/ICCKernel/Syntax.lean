import Lean
import Lean.Data.Json

/-!
# ICCKernel.Syntax

Kernel-facing ICC syntax for direct `Lean.Expr` lowering.

This is intentionally broader than the small additive `LoF.ICC` lane: it must carry
the structural information present in elaborated Lean kernel expressions without
hiding unsupported structure behind opaque atoms or hashes.
-/

namespace HeytingLean
namespace LoF
namespace ICCKernel

inductive Name where
  | anonymous
  | str (parent : Name) (value : String)
  | num (parent : Name) (value : Nat)
  deriving Repr, Inhabited, BEq, Lean.ToJson, Lean.FromJson

def Name.ofLean : Lean.Name → Name
  | .anonymous => .anonymous
  | .str p s => .str (ofLean p) s
  | .num p n => .num (ofLean p) n

def Name.structuralKey : Name → String
  | .anonymous => "anonymous"
  | .str p s => "str(" ++ p.structuralKey ++ "," ++ s ++ ")"
  | .num p n => "num(" ++ p.structuralKey ++ "," ++ toString n ++ ")"

inductive Level where
  | zero
  | succ (u : Level)
  | max (a b : Level)
  | imax (a b : Level)
  | param (name : Name)
  | mvar (name : Name)
  deriving Repr, Inhabited, BEq, Lean.ToJson, Lean.FromJson

def Level.structuralKey : Level → String
  | .zero => "zero"
  | .succ u => "succ(" ++ u.structuralKey ++ ")"
  | .max a b => "max(" ++ a.structuralKey ++ "," ++ b.structuralKey ++ ")"
  | .imax a b => "imax(" ++ a.structuralKey ++ "," ++ b.structuralKey ++ ")"
  | .param n => "param(" ++ n.structuralKey ++ ")"
  | .mvar n => "mvar(" ++ n.structuralKey ++ ")"

inductive BinderStyle where
  | default
  | implicit
  | strictImplicit
  | instImplicit
  deriving Repr, Inhabited, BEq, Lean.ToJson, Lean.FromJson

def BinderStyle.structuralKey : BinderStyle → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

inductive Literal where
  | nat (value : Nat)
  | str (value : String)
  deriving Repr, Inhabited, BEq, Lean.ToJson, Lean.FromJson

def Literal.structuralKey : Literal → String
  | .nat n => "nat(" ++ toString n ++ ")"
  | .str s => "str(" ++ s ++ ")"

structure Slice where
  source : String
  text : String
  startByte : Nat
  stopByte : Nat
  deriving Repr, Inhabited, BEq, Lean.ToJson, Lean.FromJson

def Slice.structuralKey (s : Slice) : String :=
  "slice(" ++ s.source ++ ";" ++ toString s.startByte ++ "," ++ toString s.stopByte ++ "," ++ s.text ++ ")"

inductive SourceInfoView where
  | original (leading : Slice) (posByte : Nat) (trailing : Slice) (endPosByte : Nat)
  | synthetic (posByte : Nat) (endPosByte : Nat) (canonical : Bool)
  | none
  deriving Repr, Inhabited, BEq, Lean.ToJson, Lean.FromJson

def SourceInfoView.structuralKey : SourceInfoView → String
  | .original leading pos trailing stop =>
      "original(" ++ leading.structuralKey ++ ";" ++ toString pos ++ ";" ++
        trailing.structuralKey ++ ";" ++ toString stop ++ ")"
  | .synthetic pos stop canonical =>
      "synthetic(" ++ toString pos ++ ";" ++ toString stop ++ ";" ++ toString canonical ++ ")"
  | .none => "none"

inductive PreresolvedView where
  | namespace (ns : Name)
  | decl (name : Name) (fields : List String)
  deriving Repr, Inhabited, BEq, Lean.ToJson, Lean.FromJson

def PreresolvedView.structuralKey : PreresolvedView → String
  | .namespace ns => "namespace(" ++ ns.structuralKey ++ ")"
  | .decl n fields =>
      "decl(" ++ n.structuralKey ++ ";[" ++ String.intercalate "," fields ++ "])"

inductive SyntaxView where
  | missing
  | node (info : SourceInfoView) (kind : Name) (args : List SyntaxView)
  | atom (info : SourceInfoView) (val : String)
  | ident (info : SourceInfoView) (rawVal : Slice) (val : Name) (preresolved : List PreresolvedView)
  deriving Repr, Inhabited, BEq

partial def SyntaxView.toJson : SyntaxView → Lean.Json
  | .missing =>
      Lean.Json.mkObj [("ctor", Lean.Json.str "missing")]
  | .node info kind args =>
      Lean.Json.mkObj
        [ ("ctor", Lean.Json.str "node")
        , ("info", Lean.toJson info)
        , ("kind", Lean.toJson kind)
        , ("args", Lean.Json.arr (args.map SyntaxView.toJson).toArray)
        ]
  | .atom info val =>
      Lean.Json.mkObj
        [ ("ctor", Lean.Json.str "atom")
        , ("info", Lean.toJson info)
        , ("val", Lean.Json.str val)
        ]
  | .ident info rawVal val preresolved =>
      Lean.Json.mkObj
        [ ("ctor", Lean.Json.str "ident")
        , ("info", Lean.toJson info)
        , ("rawVal", Lean.toJson rawVal)
        , ("val", Lean.toJson val)
        , ("preresolved", Lean.Json.arr (preresolved.map Lean.toJson).toArray)
        ]

instance : Lean.ToJson SyntaxView where
  toJson := SyntaxView.toJson

partial def SyntaxView.fromJson? : Lean.Json → Except String SyntaxView
  | json@(.obj _) => do
      let ctor ← Lean.Json.getObjValAs? json String "ctor"
      match ctor with
      | "missing" =>
          pure .missing
      | "node" =>
          let info : SourceInfoView ← Lean.fromJson? (← json.getObjVal? "info")
          let kind : Name ← Lean.fromJson? (← json.getObjVal? "kind")
          let argsJson ← json.getObjVal? "args"
          let args ←
            match argsJson with
            | .arr arr => arr.toList.mapM SyntaxView.fromJson?
            | _ => throw "SyntaxView.node args must be a JSON array"
          pure (.node info kind args)
      | "atom" =>
          let info : SourceInfoView ← Lean.fromJson? (← json.getObjVal? "info")
          let val ← Lean.Json.getObjValAs? json String "val"
          pure (.atom info val)
      | "ident" =>
          let info : SourceInfoView ← Lean.fromJson? (← json.getObjVal? "info")
          let rawVal : Slice ← Lean.fromJson? (← json.getObjVal? "rawVal")
          let val : Name ← Lean.fromJson? (← json.getObjVal? "val")
          let preresolvedJson ← json.getObjVal? "preresolved"
          let preresolved ←
            match preresolvedJson with
            | .arr arr => arr.toList.mapM Lean.fromJson?
            | _ => throw "SyntaxView.ident preresolved must be a JSON array"
          pure (.ident info rawVal val preresolved)
      | other =>
          throw s!"unknown SyntaxView ctor: {other}"
  | _ => throw "SyntaxView must be a JSON object"

instance : Lean.FromJson SyntaxView where
  fromJson? := SyntaxView.fromJson?

def SyntaxView.structuralKey : SyntaxView → String
  | .missing => "missing"
  | .node info kind args =>
      "node(" ++ info.structuralKey ++ ";" ++ kind.structuralKey ++ ";[" ++
        String.intercalate "," (args.map SyntaxView.structuralKey) ++ "])"
  | .atom info val =>
      "atom(" ++ info.structuralKey ++ ";" ++ val ++ ")"
  | .ident info rawVal val preresolved =>
      "ident(" ++ info.structuralKey ++ ";" ++ rawVal.structuralKey ++ ";" ++
        val.structuralKey ++ ";[" ++
        String.intercalate "," (preresolved.map PreresolvedView.structuralKey) ++ "])"

/--
`Lean.DataValue.ofSyntax` is preserved as a structural syntax tree rather than silently
flattened to display text. This keeps the metadata lane machine-visible and avoids a
hidden lossy escape hatch inside otherwise structural lowering.
-/
inductive MetaValue where
  | string (value : String)
  | bool (value : Bool)
  | name (value : Name)
  | nat (value : Nat)
  | int (value : Int)
  | syntax (value : SyntaxView)
  deriving Repr, Inhabited, BEq, Lean.ToJson, Lean.FromJson

def MetaValue.structuralKey : MetaValue → String
  | .string s => "string(" ++ s ++ ")"
  | .bool b => "bool(" ++ toString b ++ ")"
  | .name n => "name(" ++ n.structuralKey ++ ")"
  | .nat n => "nat(" ++ toString n ++ ")"
  | .int n => "int(" ++ toString n ++ ")"
  | .syntax stx => "syntax(" ++ stx.structuralKey ++ ")"

structure MetadataEntry where
  key : Name
  value : MetaValue
  deriving Repr, Inhabited, BEq, Lean.ToJson, Lean.FromJson

def MetadataEntry.structuralKey (e : MetadataEntry) : String :=
  e.key.structuralKey ++ "=" ++ e.value.structuralKey

inductive Term where
  | bvar (idx : Nat)
  | fvar (name : Name)
  | mvar (name : Name)
  | sort (level : Level)
  | const (name : Name) (levels : List Level)
  | app (fn arg : Term)
  | lam (binder : Name) (binderInfo : BinderStyle) (type body : Term)
  | forallE (binder : Name) (binderInfo : BinderStyle) (type body : Term)
  | letE (binder : Name) (type value body : Term) (nonDep : Bool)
  | lit (value : Literal)
  | mdata (entries : List MetadataEntry) (body : Term)
  | proj (structName : Name) (idx : Nat) (expr : Term)
  | bridge (body : Term)
  | ann (val typ : Term)
  deriving Repr, Inhabited, BEq, Lean.ToJson, Lean.FromJson

def Term.structuralKey : Term → String
  | .bvar idx => "bvar(" ++ toString idx ++ ")"
  | .fvar n => "fvar(" ++ n.structuralKey ++ ")"
  | .mvar n => "mvar(" ++ n.structuralKey ++ ")"
  | .sort u => "sort(" ++ u.structuralKey ++ ")"
  | .const n us =>
      "const(" ++ n.structuralKey ++ ";[" ++ String.intercalate "," (us.map Level.structuralKey) ++ "])"
  | .app f a => "app(" ++ f.structuralKey ++ "," ++ a.structuralKey ++ ")"
  | .lam n bi ty body =>
      "lam(" ++ n.structuralKey ++ ";" ++ bi.structuralKey ++ ";" ++ ty.structuralKey ++ ";" ++ body.structuralKey ++ ")"
  | .forallE n bi ty body =>
      "forall(" ++ n.structuralKey ++ ";" ++ bi.structuralKey ++ ";" ++ ty.structuralKey ++ ";" ++ body.structuralKey ++ ")"
  | .letE n ty val body nonDep =>
      "let(" ++ n.structuralKey ++ ";" ++ ty.structuralKey ++ ";" ++ val.structuralKey ++ ";" ++ body.structuralKey ++ ";" ++ toString nonDep ++ ")"
  | .lit v => "lit(" ++ v.structuralKey ++ ")"
  | .mdata entries body =>
      "mdata([" ++ String.intercalate "," (entries.map MetadataEntry.structuralKey) ++ "];" ++ body.structuralKey ++ ")"
  | .proj s idx body =>
      "proj(" ++ s.structuralKey ++ ";" ++ toString idx ++ ";" ++ body.structuralKey ++ ")"
  | .bridge body => "bridge(" ++ body.structuralKey ++ ")"
  | .ann val typ => "ann(" ++ val.structuralKey ++ ";" ++ typ.structuralKey ++ ")"

end ICCKernel
end LoF
end HeytingLean
