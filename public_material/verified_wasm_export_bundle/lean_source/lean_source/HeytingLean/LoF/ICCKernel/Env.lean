import Lean
import Lean.Data.Json
import HeytingLean.LoF.ICCKernel.Syntax

/-!
# ICCKernel.Env

Kernel-declaration environment objects for ICC export.
-/

namespace HeytingLean
namespace LoF
namespace ICCKernel

abbrev KName := HeytingLean.LoF.ICCKernel.Name
abbrev KTerm := HeytingLean.LoF.ICCKernel.Term

inductive ReducibilityHints where
  | opaque
  | abbrev
  | regular (height : Nat)
  deriving Repr, Inhabited, BEq, Lean.ToJson

inductive DefinitionSafety where
  | «unsafe»
  | safe
  | «partial»
  deriving Repr, Inhabited, BEq, Lean.ToJson

inductive QuotKind where
  | type
  | ctor
  | lift
  | ind
  deriving Repr, Inhabited, BEq, Lean.ToJson

structure ConstantVal where
  name : KName
  levelParams : List KName
  type : KTerm
  deriving Repr, Inhabited, BEq, Lean.ToJson

structure AxiomVal extends ConstantVal where
  isUnsafe : Bool
  deriving Repr, Inhabited, BEq, Lean.ToJson

structure DefinitionVal extends ConstantVal where
  value : KTerm
  hints : ReducibilityHints
  safety : DefinitionSafety
  all : List KName
  deriving Repr, Inhabited, BEq, Lean.ToJson

structure TheoremVal extends ConstantVal where
  value : KTerm
  all : List KName
  deriving Repr, Inhabited, BEq, Lean.ToJson

structure OpaqueVal extends ConstantVal where
  value : KTerm
  isUnsafe : Bool
  all : List KName
  deriving Repr, Inhabited, BEq, Lean.ToJson

structure InductiveVal extends ConstantVal where
  numParams : Nat
  numIndices : Nat
  all : List KName
  ctors : List KName
  numNested : Nat
  isRec : Bool
  isUnsafe : Bool
  isReflexive : Bool
  deriving Repr, Inhabited, BEq, Lean.ToJson

structure ConstructorVal extends ConstantVal where
  induct : KName
  cidx : Nat
  numParams : Nat
  numFields : Nat
  isUnsafe : Bool
  deriving Repr, Inhabited, BEq, Lean.ToJson

structure RecursorRule where
  ctor : KName
  nfields : Nat
  rhs : KTerm
  deriving Repr, Inhabited, BEq, Lean.ToJson

structure RecursorVal extends ConstantVal where
  all : List KName
  numParams : Nat
  numIndices : Nat
  numMotives : Nat
  numMinors : Nat
  rules : List RecursorRule
  k : Bool
  isUnsafe : Bool
  deriving Repr, Inhabited, BEq, Lean.ToJson

structure QuotVal extends ConstantVal where
  kind : QuotKind
  deriving Repr, Inhabited, BEq, Lean.ToJson

inductive ConstantInfo where
  | axiomInfo (val : AxiomVal)
  | defnInfo (val : DefinitionVal)
  | thmInfo (val : TheoremVal)
  | opaqueInfo (val : OpaqueVal)
  | quotInfo (val : QuotVal)
  | inductInfo (val : InductiveVal)
  | ctorInfo (val : ConstructorVal)
  | recInfo (val : RecursorVal)
  deriving Repr, Inhabited, BEq, Lean.ToJson

def ConstantInfo.kindTag : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "defn"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def ConstantInfo.name : ConstantInfo → KName
  | .axiomInfo v => v.name
  | .defnInfo v => v.name
  | .thmInfo v => v.name
  | .opaqueInfo v => v.name
  | .quotInfo v => v.name
  | .inductInfo v => v.name
  | .ctorInfo v => v.name
  | .recInfo v => v.name

def ConstantInfo.typeTerm : ConstantInfo → KTerm
  | .axiomInfo v => v.type
  | .defnInfo v => v.type
  | .thmInfo v => v.type
  | .opaqueInfo v => v.type
  | .quotInfo v => v.type
  | .inductInfo v => v.type
  | .ctorInfo v => v.type
  | .recInfo v => v.type

def ConstantInfo.valueTerm? : ConstantInfo → Option KTerm
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

structure ModuleBundle where
  moduleName : KName
  constants : List ConstantInfo
  deriving Repr, Inhabited, BEq, Lean.ToJson

end ICCKernel
end LoF
end HeytingLean
