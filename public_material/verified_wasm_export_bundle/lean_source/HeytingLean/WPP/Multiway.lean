import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Nucleus

/-!
# WPP.Multiway — interior nucleus from multiway semantics

This module defines a small interface for Wolfram‑style multiway evolution and
packages:

- a **kernel-style** operator `JR` on `Set State` capturing forward invariance
  `JR(U) = { s | forward‑cone(s) ⊆ U }` (contractive, idempotent, meet-preserving),
- and a small **inflationary nucleus** constructor `reachabilityNucleus` (LoF convention),
  which unions a fixed set of “unreachable” states into every predicate.

It provides:
- `WppRule` structure with a nondeterministic one‑step function `step`.
- Reflexive‑transitive closure `StepStar` of the step relation.
- Forward-invariance kernel `JR` on `Set State` with basic properties.
- Inflationary `Nucleus` packaging via `reachabilityNucleus`.
-/

namespace HeytingLean
namespace WPP

open Set

structure WppRule (State : Type u) where
  step : State → Finset State

namespace WppRule

variable {State : Type u} (R : WppRule State)

/-- One‑step relation induced by the rule's finset step. -/
def stepRel (s t : State) : Prop := t ∈ (R.step s)

inductive StepStar : State → State → Prop
| refl (s : State) : StepStar s s
| tail {s t u : State} : stepRel R s t → StepStar t u → StepStar s u

namespace StepStar

variable {R}

theorem trans {s t u : State} :
    StepStar (R := R) s t → StepStar (R := R) t u → StepStar (R := R) s u := by
  intro hst htu
  induction hst with
  | refl =>
      simpa using htu
  | tail hstep hmid ih =>
      exact StepStar.tail hstep (ih htu)

end StepStar

/-- Forward cone of a state under the rule. -/
def cone (s : State) : Set State := fun t => StepStar (R := R) s t

/-- Interior view: `JR U s` means the forward cone of `s` is contained in `U`. -/
def JR (U : Set State) : Set State := fun s => ∀ t, cone (R := R) s t → U t

@[simp] lemma JR_mem_iff {U : Set State} {s : State} :
    JR (R := R) U s ↔ (∀ t, StepStar (R := R) s t → U t) := Iff.rfl

namespace JR

variable {R}

lemma mono : Monotone (JR (R := R)) := by
  intro U V hUV s hs t hst
  exact hUV (hs _ hst)

lemma contractive (U : Set State) : JR (R := R) U ⊆ U := by
  intro s hs
  exact hs s (StepStar.refl s)

lemma idem (U : Set State) : JR (R := R) (JR (R := R) U) = JR (R := R) U := by
  ext s
  constructor
  · intro hs t hst
    exact (contractive (R := R) (U := U)) (hs t hst)
  · intro hs t hst u htu
    exact hs u (StepStar.trans (R := R) hst htu)

lemma inf (U V : Set State) :
    JR (R := R) (U ∩ V) = JR (R := R) U ∩ JR (R := R) V := by
  ext s
  constructor
  · intro hs
    refine And.intro ?_ ?_
    · intro t hst
      exact (hs t hst).1
    · intro t hst
      exact (hs t hst).2
  · rintro ⟨hsU, hsV⟩ t hst
    exact And.intro (hsU t hst) (hsV t hst)

end JR

/-! ## Inflationary nucleus packaging (LoF convention) -/

section Nucleus

open Set

variable {R} (s₀ : State)

/-- States unreachable from the chosen base state `s₀`. -/
def unreachableFrom : Set State :=
  {s | ¬ StepStar (R := R) s₀ s}

/-- Inflationary nucleus on predicates: “treat unreachable states as vacuously admissible”
by unioning them into every predicate. -/
def reachabilityNucleus : Nucleus (Set State) where
  toFun U := U ∪ unreachableFrom (R := R) s₀
  map_inf' U V := by
    ext s
    constructor
    · intro hs
      rcases hs with hs | hunr
      · exact ⟨Or.inl hs.1, Or.inl hs.2⟩
      · exact ⟨Or.inr hunr, Or.inr hunr⟩
    · rintro ⟨hsU, hsV⟩
      cases hsU with
      | inl hsU =>
          cases hsV with
          | inl hsV => exact Or.inl ⟨hsU, hsV⟩
          | inr hunr => exact Or.inr hunr
      | inr hunr =>
          exact Or.inr hunr
  idempotent' U := by
    intro s hs
    rcases hs with hs | hunr
    · exact hs
    · exact Or.inr hunr
  le_apply' U := by
    intro s hs
    exact Or.inl hs

@[simp] lemma reachabilityNucleus_apply (U : Set State) :
    reachabilityNucleus (R := R) s₀ U = U ∪ unreachableFrom (R := R) s₀ := rfl

end Nucleus

end WppRule

end WPP
end HeytingLean
