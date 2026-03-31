/-
  Certified Artifact Infrastructure

  MLTT-style dependent pair where:
  - `val` is runtime data (compiles to code)
  - `ok`  is a proof obligation (erased at runtime)
-/

namespace HeytingLean
namespace Certified

universe u

/-- Core certified value: pairs a value with a proof it satisfies a spec. -/
structure Certified (α : Type u) (Spec : α → Prop) where
  val : α
  ok : Spec val

/-- Certified with decidable spec (allows optional runtime checks in debug tooling). -/
structure CertifiedDec (α : Type u) (Spec : α → Prop) [DecidablePred Spec] where
  val : α
  ok : Spec val

namespace Certified

/-- Extract the executable component (this is what compiles to runtime code). -/
@[inline] def extract {α : Type u} {Spec : α → Prop} (c : Certified α Spec) : α :=
  c.val

/-- Proof accessor (erased at runtime). -/
def proof {α : Type u} {Spec : α → Prop} (c : Certified α Spec) : Spec c.val :=
  c.ok

/-- Functor map over certified values. -/
def map {α β : Type u} {SpecA : α → Prop} {SpecB : β → Prop}
    (f : α → β)
    (pf : ∀ a, SpecA a → SpecB (f a))
    (c : Certified α SpecA) : Certified β SpecB :=
  ⟨f c.val, pf c.val c.ok⟩

/-- Compose certified computations. -/
def bind {α β : Type u} {SpecA : α → Prop} {SpecB : β → Prop}
    (c : Certified α SpecA)
    (f : (a : α) → SpecA a → Certified β SpecB) : Certified β SpecB :=
  f c.val c.ok

/-- Lift a proven value into `Certified`. -/
def mk' {α : Type u} {Spec : α → Prop} (a : α) (h : Spec a) : Certified α Spec :=
  ⟨a, h⟩

end Certified

end Certified
end HeytingLean

