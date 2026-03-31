import HeytingLean.LeanCP.Core.SProp
import HeytingLean.LeanCP.VCG.SFunSpec
import HeytingLean.LeanCP.VCG.SymExec

/-!
# LeanCP Structured Annotation Language

Phase 7 adds a typed front-end for structured assertions and annotation bundles.
This module defines the semantic core only. Parsing and macro lowering live in
`Parser.lean` and `Elaborate.lean`.
-/

namespace HeytingLean.LeanCP

/-- Terms admissible in the `SEP[...]` fragment. -/
class ToAssertionAtom (α : Type) where
  toSProp : α → SProp

export ToAssertionAtom (toSProp)

instance : ToAssertionAtom SProp where
  toSProp := id

instance : ToAssertionAtom HProp where
  toSProp := SProp.ofHProp

/-- A structured `LOCAL` binding records a variable name together with the
expression whose value it should hold in the current state. -/
structure LocalBinding where
  name : String
  value : CExpr

/-- Conjoin a list of state assertions over the same state. -/
def handList : List SProp → SProp
  | [] => SProp.strue
  | p :: ps => SProp.hand p (handList ps)

/-- Separate-conjoin a list of state assertions. -/
def sepList : List SProp → SProp
  | [] => SProp.emp
  | p :: ps => SProp.sep p (sepList ps)

/-- A VST-style structured assertion. Pure clauses and local clauses are
conjoined over the same state; spatial clauses are joined by separation. -/
structure Assertion where
  pure : List SProp := []
  locals : List LocalBinding := []
  spatial : List SProp := []

namespace LocalBinding

/-- Interpret a local binding as a state assertion. -/
def toSProp (binding : LocalBinding) : SProp := fun st =>
  match evalExpr binding.value st with
  | some v => st.lookupVar binding.name = some v
  | none => False

end LocalBinding

namespace Assertion

/-- Empty structured assertion. -/
def empty : Assertion := {}

/-- Materialize the `LOCAL[...]` fragment as state assertions. -/
def localFacts (ann : Assertion) : List SProp :=
  ann.locals.map LocalBinding.toSProp

/-- Lower a structured assertion into the state-sensitive assertion language. -/
def toSProp (ann : Assertion) : SProp :=
  SProp.hand (handList (ann.pure ++ ann.localFacts)) (sepList ann.spatial)

end Assertion

instance : ToAssertionAtom Assertion where
  toSProp := Assertion.toSProp

/-- A QCP-style partial assertion patch. Unmentioned locals are preserved by
name; spatial clauses are framed; pure clauses are treated conservatively as a
fresh set because purity preservation across modified locals requires dependency
analysis this layer does not yet perform. -/
structure PartialAssertion where
  modifies : List String := []
  pure : List SProp := []
  locals : List LocalBinding := []
  spatial : List SProp := []

namespace PartialAssertion

def empty : PartialAssertion := {}

private def touchedLocals (patch : PartialAssertion) : List String :=
  patch.modifies ++ patch.locals.map (·.name)

/-- Apply a partial assertion patch to a base structured assertion. -/
def applyTo (patch : PartialAssertion) (base : Assertion) : Assertion :=
  let touched := patch.touchedLocals
  let keptLocals := base.locals.filter (fun binding => binding.name ∉ touched)
  { pure := patch.pure
    locals := keptLocals ++ patch.locals
    spatial := base.spatial ++ patch.spatial }

/-- Lower a partial assertion relative to a base assertion. -/
def toSPropFrom (patch : PartialAssertion) (base : Assertion) : SProp :=
  (patch.applyTo base).toSProp

end PartialAssertion

/-- Parameter metadata for a structured function annotation. -/
structure AnnotatedParam where
  name : String
  ty : CType

/-- Typed function annotation surface for LeanCP. -/
structure FuncAnnotation where
  name : String
  params : List AnnotatedParam
  retType : CType
  requires : Assertion
  ensures : CVal → Assertion
  body : CStmt
  modifies : List String := []

namespace FuncAnnotation

def paramPairs (ann : FuncAnnotation) : List (String × CType) :=
  ann.params.map (fun p => (p.name, p.ty))

def toSFunSpec (ann : FuncAnnotation) : SFunSpec :=
  { name := ann.name
    params := ann.paramPairs
    retType := ann.retType
    pre := ann.requires.toSProp
    post := fun ret => (ann.ensures ret).toSProp
    body := ann.body }

def toVerifyInput (ann : FuncAnnotation) (mode : VerifyMode)
    (loops : List LoopHint := []) (funEnv : FunEnv := fun _ => none) : VerifyInput :=
  { name := ann.name
    mode := mode
    body := ann.body
    pre := ann.requires.toSProp
    post := fun ret => (ann.ensures ret).toSProp
    funEnv := funEnv
    loops := loops }

end FuncAnnotation

/-- Structured loop annotation lowering to the Phase 4 loop-hint surface. -/
structure LoopAnnotation where
  path : List Nat
  invariant : Assertion
  fuelHint : Nat
  variant : Option CExpr := none

namespace LoopAnnotation

def toLoopHint (ann : LoopAnnotation) : LoopHint :=
  { path := ann.path
    inv := ann.invariant.toSProp
    fuelHint := ann.fuelHint }

end LoopAnnotation

@[simp] theorem FuncAnnotation_toSFunSpec_name (ann : FuncAnnotation) :
    ann.toSFunSpec.name = ann.name := by
  rfl

@[simp] theorem LoopAnnotation_toLoopHint_path (ann : LoopAnnotation) :
    ann.toLoopHint.path = ann.path := by
  rfl

end HeytingLean.LeanCP
