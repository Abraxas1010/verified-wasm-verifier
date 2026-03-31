import Lean.Data.Json
import HeytingLean.LoF.ICCKernel.Env

/-!
# ICCKernel.Corpus

Export/corpus payloads for ICCKernel memory construction.
-/

namespace HeytingLean
namespace LoF
namespace ICCKernel

structure CountEntry where
  label : String
  count : Nat
  deriving Repr, Inhabited, BEq, Lean.ToJson, Lean.FromJson

def bumpCount (label : String) (counts : Array CountEntry) : Array CountEntry :=
  let idx? := counts.findIdx? (fun e => e.label = label)
  match idx? with
  | some idx =>
      counts.set! idx { label := label, count := counts[idx]!.count + 1 }
  | none =>
      counts.push { label := label, count := 1 }

def bumpCountN (label : String) : Nat → Array CountEntry → Array CountEntry
  | 0, counts => counts
  | n + 1, counts => bumpCountN label n (bumpCount label counts)

def mergeCountArrays (src : Array CountEntry) (dst : Array CountEntry) : Array CountEntry :=
  src.foldl (fun acc entry => bumpCountN entry.label entry.count acc) dst

def termCtorTag : Term → String
  | .bvar _ => "bvar"
  | .fvar _ => "fvar"
  | .mvar _ => "mvar"
  | .sort _ => "sort"
  | .const _ _ => "const"
  | .app _ _ => "app"
  | .lam _ _ _ _ => "lam"
  | .forallE _ _ _ _ => "forallE"
  | .letE _ _ _ _ _ => "letE"
  | .lit _ => "lit"
  | .mdata _ _ => "mdata"
  | .proj _ _ _ => "proj"
  | .bridge _ => "bridge"
  | .ann _ _ => "ann"

def collectTermCounts : Term → Array CountEntry → Array CountEntry
  | t, acc =>
      let acc := bumpCount (termCtorTag t) acc
      match t with
      | .app f a => collectTermCounts a (collectTermCounts f acc)
      | .lam _ _ ty body => collectTermCounts body (collectTermCounts ty acc)
      | .forallE _ _ ty body => collectTermCounts body (collectTermCounts ty acc)
      | .letE _ ty val body _ => collectTermCounts body (collectTermCounts val (collectTermCounts ty acc))
      | .mdata _ body => collectTermCounts body acc
      | .proj _ _ body => collectTermCounts body acc
      | .bridge body => collectTermCounts body acc
      | .ann val typ => collectTermCounts typ (collectTermCounts val acc)
      | _ => acc

structure ExportedDecl where
  moduleName : HeytingLean.LoF.ICCKernel.Name
  decl : HeytingLean.LoF.ICCKernel.ConstantInfo
  deriving Repr, Inhabited, BEq, Lean.ToJson

private def exportedDeclConstName : HeytingLean.LoF.ICCKernel.ConstantInfo → HeytingLean.LoF.ICCKernel.Name
  | .axiomInfo v => v.name
  | .defnInfo v => v.name
  | .thmInfo v => v.name
  | .opaqueInfo v => v.name
  | .quotInfo v => v.name
  | .inductInfo v => v.name
  | .ctorInfo v => v.name
  | .recInfo v => v.name

private def exportedDeclKindTag : HeytingLean.LoF.ICCKernel.ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "defn"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def exportedDeclTypeTerm : HeytingLean.LoF.ICCKernel.ConstantInfo → HeytingLean.LoF.ICCKernel.Term
  | .axiomInfo v => v.type
  | .defnInfo v => v.type
  | .thmInfo v => v.type
  | .opaqueInfo v => v.type
  | .quotInfo v => v.type
  | .inductInfo v => v.type
  | .ctorInfo v => v.type
  | .recInfo v => v.type

private def exportedDeclValueTerm? : HeytingLean.LoF.ICCKernel.ConstantInfo → Option HeytingLean.LoF.ICCKernel.Term
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

def ExportedDecl.name (d : ExportedDecl) : HeytingLean.LoF.ICCKernel.Name :=
  exportedDeclConstName d.decl

def ExportedDecl.kindTag (d : ExportedDecl) : String :=
  exportedDeclKindTag d.decl

def ExportedDecl.termCounts (d : ExportedDecl) : Array CountEntry :=
  let counts := collectTermCounts (exportedDeclTypeTerm d.decl) #[]
  match exportedDeclValueTerm? d.decl with
  | none => counts
  | some v => collectTermCounts v counts

structure ExportSummary where
  moduleRoots : Array String
  declsTotal : Nat
  declsSupported : Nat
  declsUnsupported : Nat
  declsUnclassified : Nat
  exprConstructorCounts : Array CountEntry
  constantKindCounts : Array CountEntry
  deriving Repr, Inhabited, BEq, Lean.ToJson

structure ExportBundle where
  moduleRoots : Array String
  declarations : Array ExportedDecl
  summary : ExportSummary
  deriving Repr, Inhabited, BEq, Lean.ToJson

structure CorpusRow where
  rowId : String
  declName : String
  moduleName : String
  declKind : String
  supported : Bool
  typeTerm : HeytingLean.LoF.ICCKernel.Term
  valueTerm : Option HeytingLean.LoF.ICCKernel.Term
  deriving Repr, Inhabited, BEq, Lean.ToJson

def CorpusRow.ofExportedDecl (d : ExportedDecl) : CorpusRow :=
  let declName := Name.structuralKey d.name
  let moduleName := Name.structuralKey d.moduleName
  let declKind := d.kindTag
  let rowId := moduleName ++ "::" ++ declName
  {
    rowId := rowId
    declName := declName
    moduleName := moduleName
    declKind := declKind
    supported := true
    typeTerm := exportedDeclTypeTerm d.decl
    valueTerm := exportedDeclValueTerm? d.decl
  }

structure CorpusBundle where
  moduleRoots : Array String
  rows : Array CorpusRow
  summary : ExportSummary
  deriving Repr, Inhabited, BEq, Lean.ToJson

def exportSummaryOf (moduleRoots : Array String) (declsTotal : Nat) (decls : Array ExportedDecl) : ExportSummary :=
  let exprCounts := decls.foldl (fun acc d => mergeCountArrays (d.termCounts) acc) #[]
  let kindCounts := decls.foldl (fun acc d => bumpCount d.kindTag acc) #[]
  {
    moduleRoots := moduleRoots
    declsTotal := declsTotal
    declsSupported := decls.size
    declsUnsupported := declsTotal - decls.size
    declsUnclassified := 0
    exprConstructorCounts := exprCounts
    constantKindCounts := kindCounts
  }

end ICCKernel
end LoF
end HeytingLean
