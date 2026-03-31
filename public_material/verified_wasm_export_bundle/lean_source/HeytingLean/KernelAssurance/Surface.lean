import Lean.Data.Json
import HeytingLean.LoF.ICCKernel.Corpus

namespace HeytingLean.KernelAssurance

open Lean
open HeytingLean.LoF.ICCKernel

inductive FamilyId where
  | theorem
  | definition
  | opaque
  | axiom
  | inductive
  | constructor
  | recursor
  | quot
  | unknown
  deriving Repr, Inhabited, BEq, DecidableEq, ToJson, FromJson

instance : ToString FamilyId where
  toString
    | .theorem => "theorem"
    | .definition => "definition"
    | .opaque => "opaque"
    | .axiom => "axiom"
    | .inductive => "inductive"
    | .constructor => "constructor"
    | .recursor => "recursor"
    | .quot => "quot"
    | .unknown => "unknown"

inductive SupportStatus where
  | supported
  | blocked
  | unclassified
  deriving Repr, Inhabited, BEq, DecidableEq, ToJson, FromJson

instance : ToString SupportStatus where
  toString
    | .supported => "supported"
    | .blocked => "blocked"
    | .unclassified => "unclassified"

structure SliceDescriptor where
  version : String := "kernel-assurance-v1"
  moduleRoots : Array String
  claimBoundary : String :=
    "Explicit kernel-slice assurance only; not a proof of Lean's full kernel."
  deriving Repr, Inhabited, BEq, ToJson, FromJson

def allFamilies : Array FamilyId :=
  #[.theorem, .definition, .opaque, .axiom, .inductive, .constructor, .recursor, .quot, .unknown]

def FamilyId.ofKindTag : String → FamilyId
  | "theorem" => .theorem
  | "defn" => .definition
  | "opaque" => .opaque
  | "axiom" => .axiom
  | "inductive" => .inductive
  | "constructor" => .constructor
  | "recursor" => .recursor
  | "quot" => .quot
  | _ => .unknown

def FamilyId.kindTag : FamilyId → String
  | .theorem => "theorem"
  | .definition => "defn"
  | .opaque => "opaque"
  | .axiom => "axiom"
  | .inductive => "inductive"
  | .constructor => "constructor"
  | .recursor => "recursor"
  | .quot => "quot"
  | .unknown => "unknown"

def statusOfFamily : FamilyId → SupportStatus
  | .theorem => .supported
  | .definition => .supported
  | .opaque => .supported
  | .axiom => .blocked
  | .inductive => .blocked
  | .constructor => .blocked
  | .recursor => .blocked
  | .quot => .blocked
  | .unknown => .unclassified

def familyOfDecl (d : ExportedDecl) : FamilyId :=
  FamilyId.ofKindTag d.kindTag

def statusOfDecl (d : ExportedDecl) : SupportStatus :=
  statusOfFamily (familyOfDecl d)

end HeytingLean.KernelAssurance
