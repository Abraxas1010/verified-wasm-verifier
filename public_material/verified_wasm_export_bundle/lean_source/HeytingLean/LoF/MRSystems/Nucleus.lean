import HeytingLean.ClosingTheLoop.MR.ClosureOperator
import HeytingLean.LoF.Bauer.SyntheticComputability
import HeytingLean.LoF.MRSystems.Truncation

/-!
# (M,R) closure as a nucleus/modality on predicates (Phase E.1)

Tier 1 gives an idempotent endomap on selectors:

`closeSelector : Selector S → Selector S`

and its fixed points `IsClosed` (the “closed” selectors at `b`).

This module promotes that *subset of closed selectors* to a **locale-theoretic nucleus**
on the discrete predicate frame `Set (Selector S)`:

* define the core `K := {Φ | ¬ IsClosed Φ}` of “non-closed” selectors,
* define the nucleus `J(U) := U ∪ K`,
* observe that `J`-closed truth values correspond exactly to predicates on closed selectors.

Objective boundary:
* This is a discrete-locale / subspace construction.  It does **not** claim to encode the full
  admissibility story of Tier 1, nor any SKY/Y correspondence.
-/

namespace HeytingLean
namespace LoF
namespace MRSystems

open scoped Classical

open HeytingLean.ClosingTheLoop.MR

universe u v

variable {S : MRSystem.{u, v}} {b : S.B} (RI : RightInverseAt S b)

/-! ## Core: the non-closed selectors -/

/-- The subset of selectors that are **not** closed at `b`. -/
def nonClosedCore : Set (Selector S) :=
  {Φ | ¬ IsClosed S b RI Φ}

@[simp] lemma mem_nonClosedCore_iff (Φ : Selector S) :
    Φ ∈ nonClosedCore (S := S) (b := b) RI ↔ ¬ IsClosed S b RI Φ := Iff.rfl

/-! ## A nucleus selecting the closed selectors as a sublocale -/

/-- A nucleus on `Set (Selector S)` whose closed truth values are “predicates on closed selectors”.

It is the discrete-locale subspace nucleus for the subset `{Φ | IsClosed Φ}`. -/
def closedSelectorNucleus : Nucleus (Set (Selector S)) :=
  HeytingLean.LoF.Bauer.SyntheticComputability.Predicate.adjoinNucleus (ι := Selector S)
    (K := nonClosedCore (S := S) (b := b) RI)

@[simp] lemma closedSelectorNucleus_apply (U : Set (Selector S)) :
    closedSelectorNucleus (S := S) (b := b) RI U =
      U ∪ nonClosedCore (S := S) (b := b) RI := rfl

lemma closedSelectorNucleus_fixed_iff (U : Set (Selector S)) :
    closedSelectorNucleus (S := S) (b := b) RI U = U ↔
      nonClosedCore (S := S) (b := b) RI ⊆ U := by
  change
    HeytingLean.LoF.Bauer.SyntheticComputability.Predicate.adjoinNucleus (ι := Selector S)
        (K := nonClosedCore (S := S) (b := b) RI) U =
        U ↔ nonClosedCore (S := S) (b := b) RI ⊆ U
  exact
    HeytingLean.LoF.Bauer.SyntheticComputability.Predicate.adjoinNucleus_fixed_iff (ι := Selector S)
      (K := nonClosedCore (S := S) (b := b) RI) (U := U)

lemma mem_closedSelectorNucleus_toSublocale_iff (U : Set (Selector S)) :
    U ∈ (closedSelectorNucleus (S := S) (b := b) RI).toSublocale ↔
      nonClosedCore (S := S) (b := b) RI ⊆ U := by
  change
    U ∈
        (HeytingLean.LoF.Bauer.SyntheticComputability.Predicate.adjoinNucleus (ι := Selector S)
              (K := nonClosedCore (S := S) (b := b) RI)).toSublocale ↔
      nonClosedCore (S := S) (b := b) RI ⊆ U
  exact
    HeytingLean.LoF.Bauer.SyntheticComputability.Predicate.mem_toSublocale_iff (ι := Selector S)
      (K := nonClosedCore (S := S) (b := b) RI) (U := U)

/-! ## Closed truth values and restriction/extension -/

/-- Closed truth values for `closedSelectorNucleus`. -/
abbrev ΩClosed : Type _ :=
  (closedSelectorNucleus (S := S) (b := b) RI).toSublocale

namespace ΩClosed

/-- Restrict a closed truth value to the closed selectors. -/
def restrict (U : ΩClosed (S := S) (b := b) RI) :
    Set (ClosedSelectorFixed (S := S) (b := b) RI) :=
  fun Φc => Φc.1 ∈ (U : Set (Selector S))

/-- Extend a predicate on closed selectors to a `closedSelectorNucleus`-closed truth value by
adjoining all non-closed selectors. -/
noncomputable def extend (V : Set (ClosedSelectorFixed (S := S) (b := b) RI)) :
    ΩClosed (S := S) (b := b) RI := by
  classical
  let U : Set (Selector S) :=
    fun Φ =>
      Φ ∈ nonClosedCore (S := S) (b := b) RI ∨
        ∃ h : IsClosed S b RI Φ, (⟨Φ, h⟩ : ClosedSelectorFixed (S := S) (b := b) RI) ∈ V
  refine ⟨U, (mem_closedSelectorNucleus_toSublocale_iff (S := S) (b := b) (RI := RI) (U := U)).2 ?_⟩
  intro Φ hΦ
  exact Or.inl hΦ

@[simp] theorem restrict_extend (V : Set (ClosedSelectorFixed (S := S) (b := b) RI)) :
    restrict (S := S) (b := b) RI (extend (S := S) (b := b) RI V) = V := by
  classical
  ext Φc
  constructor
  · intro h
    -- A closed selector cannot land in the non-closed core.
    have hnot : ¬ Φc.1 ∈ nonClosedCore (S := S) (b := b) RI := by
      simpa [nonClosedCore, IsClosed] using (not_not_intro Φc.2)
    -- So membership comes from the existential branch, and proof irrelevance identifies the witness.
    rcases h with h | h
    · exact (hnot h).elim
    · rcases h with ⟨hClosed, hV⟩
      have : (⟨Φc.1, hClosed⟩ : ClosedSelectorFixed (S := S) (b := b) RI) = Φc := by
        apply Subtype.ext
        rfl
      simpa [restrict, extend] using (this ▸ hV)
  · intro hV
    -- Choose the closedness proof carried by `Φc`.
    right
    refine ⟨Φc.2, ?_⟩
    simpa [restrict, extend] using hV

@[simp] theorem extend_restrict (U : ΩClosed (S := S) (b := b) RI) :
    extend (S := S) (b := b) RI (restrict (S := S) (b := b) RI U) = U := by
  classical
  apply Subtype.ext
  ext Φ
  -- From `U ∈ J.toSublocale`, obtain the required core containment `nonClosedCore ⊆ U`.
  have hcore : nonClosedCore (S := S) (b := b) RI ⊆ (U : Set (Selector S)) :=
    (mem_closedSelectorNucleus_toSublocale_iff (S := S) (b := b) (RI := RI) (U := (U : Set (Selector S)))).1
      U.2
  by_cases hClosed : IsClosed S b RI Φ
  · constructor
    · intro h
      -- In the closed case, the disjunction reduces to membership of the restricted predicate.
      rcases h with h | h
      · have hNot : ¬ IsClosed S b RI Φ := by
          simpa [nonClosedCore] using h
        exact (hNot hClosed).elim
      · rcases h with ⟨_h, hU⟩
        -- `hU` is exactly membership of `Φ` in `U`.
        simpa [restrict, extend] using hU
    · intro hU
      right
      refine ⟨hClosed, ?_⟩
      simpa [restrict, extend] using hU
  · constructor
    · intro _h
      -- Non-closed selectors are forced in by core containment.
      exact hcore (by simpa [nonClosedCore] using hClosed)
    · intro _hU
      -- Non-closed selectors are always in the extended truth value (left disjunct).
      left
      simpa [nonClosedCore] using hClosed

/-- Closed truth values for the `closedSelectorNucleus` are equivalent to predicates on closed selectors. -/
noncomputable def equivClosedSubsets :
    ΩClosed (S := S) (b := b) RI ≃ Set (ClosedSelectorFixed (S := S) (b := b) RI) :=
  { toFun := restrict (S := S) (b := b) RI
    invFun := fun V => extend (S := S) (b := b) RI V
    left_inv := by
      intro U
      exact extend_restrict (S := S) (b := b) (RI := RI) U
    right_inv := by
      intro V
      exact restrict_extend (S := S) (b := b) (RI := RI) V }

end ΩClosed

end MRSystems
end LoF
end HeytingLean
