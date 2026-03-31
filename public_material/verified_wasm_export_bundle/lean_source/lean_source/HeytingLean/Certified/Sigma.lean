/-
  Dependent-pair (`Sigma`) helpers for certified artifacts.
-/

import HeytingLean.Certified.Basic

namespace HeytingLean
namespace Certified

universe u v

/-- Certified with a dependent witness type (`Type`-valued spec). -/
structure CertifiedDep (α : Type u) (Spec : α → Type v) where
  val : α
  witness : Spec val

namespace CertifiedDep

/-- Convert to standard `Sigma`. -/
def toSigma {α : Type u} {Spec : α → Type v} (c : CertifiedDep α Spec) : Σ a : α, Spec a :=
  ⟨c.val, c.witness⟩

/-- Squash: package a witness into a `Prop`-valued existential spec. -/
def squash {α : Type u} {Spec : α → Type v}
    (c : CertifiedDep α Spec)
    (forget : ∀ a, Spec a → Prop)
    (h : forget c.val c.witness) :
    Certified α (fun a => ∃ w : Spec a, forget a w) :=
  ⟨c.val, ⟨c.witness, h⟩⟩

end CertifiedDep

/-- Proof-irrelevant existential wrapper (alias). -/
abbrev CertifiedEx (α : Type u) (Spec : α → Prop) : Type u := Certified α Spec

end Certified
end HeytingLean

