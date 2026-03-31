import Lean

open Lean Meta

namespace HeytingLean.Embedding

def binderInfoToString (bi : BinderInfo) : String :=
  match bi with
  | BinderInfo.default => "default"
  | BinderInfo.implicit => "implicit"
  | BinderInfo.strictImplicit => "strictImplicit"
  | BinderInfo.instImplicit => "instImplicit"

structure BinderJson where
  binderInfo : String
  name : String
  typePretty : String
  deriving Inhabited

structure TelescopeJson where
  decl : String
  binders : Array BinderJson
  targetPretty : String
  isProp : Bool
  deriving Inhabited

private def ppExprNoUniverses (e : Expr) : MetaM String := do
  withOptions (fun opts => opts.setBool `pp.universes false) do
    return (← ppExpr e).pretty

def getTelescopeJson (declName : Name) : MetaM TelescopeJson := do
  let info ← getConstInfo declName
  let type := info.type
  forallTelescopeReducing type fun xs body => do
    let mut out : Array BinderJson := #[]
    for x in xs do
      let ldecl ← getFVarLocalDecl x
      let bi := binderInfoToString ldecl.binderInfo
      let nm := if ldecl.userName.isAnonymous then s!"x{out.size}" else ldecl.userName.toString
      let tp ← ppExprNoUniverses ldecl.type
      out := out.push { binderInfo := bi, name := nm, typePretty := tp }
    let tgt ← ppExprNoUniverses body
    let isP ← isProp body
    return {
      decl := declName.toString
      binders := out
      targetPretty := tgt
      isProp := isP
    }

end HeytingLean.Embedding

