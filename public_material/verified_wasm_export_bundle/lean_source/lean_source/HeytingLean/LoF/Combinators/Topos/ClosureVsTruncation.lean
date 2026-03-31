import HeytingLean.LoF.Combinators.Category.PathTruncation
import HeytingLean.LoF.Combinators.Topos.ClosedSievesHeyting
import HeytingLean.LoF.Combinators.Topos.NucleusFunctor
import HeytingLean.LoF.Combinators.Topos.StepsSite

import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Quot

/-!
# ClosureVsTruncation — Phase C boundary lemmas

This file provides the formal “objectivity boundary” statements needed to resolve Phase C:

1. The **thin** reachability morphism type `t ⟶ u` (in the preorder category on terms) is the
   propositional truncation of the **non-thin** labeled path type `LSteps t u`:

   `Trunc (LSteps t u) ≃ (t ⟶ u)`.

2. The spec’s informal slogan “Ω\_J is (-1)-truncation” is false externally: the type of
   `J`-closed sieves is generally **not** subsingleton (already for the dense topology).

We keep all statements Lean-verifiable and avoid HoTT/HIT overclaims.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Topos

open CategoryTheory
open HeytingLean.LoF.Combinators.Category

/-! ## 1) (-1)-truncation boundary for path spaces -/

namespace TruncationBoundary

/-- Propositional truncation of labeled paths agrees with the thin morphism type in `StepsCat`. -/
noncomputable def truncLStepsEquivStepsHom (t u : StepsCat) :
    Trunc (LSteps t u) ≃ (t ⟶ u) := by
  classical
  refine
    { toFun := fun q =>
        Trunc.liftOn q
          (fun p => CategoryTheory.homOfLE (LSteps.toSteps p))
          (by intro _ _; apply Subsingleton.elim _ _)
      invFun := fun f =>
        PathTruncation.trunc_lsteps_of_steps (t := t) (u := u) (CategoryTheory.leOfHom f)
      left_inv := by
        intro q
        -- `Trunc _` is subsingleton.
        apply Subsingleton.elim _ _
      right_inv := by
        intro f
        -- `t ⟶ u` in a preorder category is subsingleton.
        apply Subsingleton.elim _ _ }

end TruncationBoundary

/-! ## 2) Dense topology: closed sieves are nontrivial (so Ω\_J is not a `Trunc`) -/

namespace DenseTopology

universe v u

variable {C : Type u} [Category.{v} C]

open Order

/-- Pseudocomplement membership for sieves: `f ∈ Sᶜ` iff `S` is empty after pullback along `f`. -/
lemma compl_apply_iff {X Y : C} (S : Sieve X) (f : Y ⟶ X) :
    (Sᶜ) f ↔ (∀ (Z : C) (g : Z ⟶ Y), ¬ S (g ≫ f)) := by
  classical
  let P : Sieve X := Sieve.generate (Presieve.singleton f)

  have P_iff {Z : C} (g : Z ⟶ X) : P g ↔ ∃ h : Z ⟶ Y, h ≫ f = g := by
    constructor
    · intro hg
      rcases hg with ⟨Y', h, g', hg', rfl⟩
      cases hg'
      refine ⟨h, ?_⟩
      simp
    · rintro ⟨h, rfl⟩
      refine ⟨Y, h, f, Presieve.singleton_self f, rfl⟩

  have hmem : (Sᶜ) f ↔ P ≤ Sᶜ := by
    constructor
    · intro hf Z g hgP
      rcases (P_iff (Z := Z) g).1 hgP with ⟨h, rfl⟩
      exact (Sᶜ).downward_closed hf h
    · intro hP
      have hfP : P f := by
        refine (P_iff (Z := Y) f).2 ?_
        exact ⟨𝟙 Y, by simp⟩
      exact hP _ hfP

  have hdisj : P ≤ Sᶜ ↔ Disjoint P S := by
    simpa [P] using (le_compl_iff_disjoint_right (a := P) (b := S))

  constructor
  · intro hf
    have hPdisj : Disjoint P S := (hdisj.mp (hmem.mp hf))
    intro Z g hS
    have hgP : P (g ≫ f) := (P_iff (Z := Z) (g ≫ f)).2 ⟨g, rfl⟩
    have : (P ⊓ S) (g ≫ f) := ⟨hgP, hS⟩
    have hb : P ⊓ S = (⊥ : Sieve X) := (disjoint_iff.mp hPdisj)
    have : (⊥ : Sieve X) (g ≫ f) := by simpa [hb] using this
    cases this
  · intro hforall
    have hPdisj : Disjoint P S := by
      apply (disjoint_iff.mpr)
      ext Z g
      constructor
      · rintro ⟨hgP, hgS⟩
        rcases (P_iff (Z := Z) g).1 hgP with ⟨h, rfl⟩
        exact False.elim (hforall _ h hgS)
      · intro hg
        cases hg
    have : P ≤ Sᶜ := (hdisj.mpr hPdisj)
    exact (hmem.mpr this)

/-- For the dense topology, `J.close` is the double-negation nucleus on `Sieve X`. -/
lemma close_eq_doubleNeg {X : C} (S : Sieve X) :
    (GrothendieckTopology.dense : GrothendieckTopology C).close S = Sᶜᶜ := by
  classical
  ext Y f
  constructor
  · intro hf
    refine (compl_apply_iff (S := Sᶜ) (f := f)).2 ?_
    intro Z g hcomp
    have hnot : ∀ {W : C} (h : W ⟶ Z), ¬ S (h ≫ g ≫ f) := by
      intro W h
      have := (compl_apply_iff (S := S) (f := g ≫ f)).1 hcomp W h
      simpa [Category.assoc] using this
    change (S.pullback f) ∈ (GrothendieckTopology.dense : GrothendieckTopology C) Y at hf
    rcases hf g with ⟨W, h, hg⟩
    have : S (h ≫ g ≫ f) := by
      simpa [Sieve.pullback_apply, Category.assoc] using hg
    exact (hnot h) this
  · intro hf
    have hf' : ∀ (Z : C) (g : Z ⟶ Y), ¬ (Sᶜ) (g ≫ f) :=
      (compl_apply_iff (S := Sᶜ) (f := f)).1 hf
    change (S.pullback f) ∈ (GrothendieckTopology.dense : GrothendieckTopology C) Y
    intro Z g
    classical
    by_contra hex
    have hall : ∀ (W : C) (h : W ⟶ Z), ¬ S (h ≫ g ≫ f) := by
      intro W h hS
      apply hex
      refine ⟨W, h, ?_⟩
      simpa [Sieve.pullback_apply, Category.assoc] using hS
    have : (Sᶜ) (g ≫ f) :=
      (compl_apply_iff (S := S) (f := g ≫ f)).2 (by
        intro W h
        have := hall W h
        simpa [Category.assoc] using this)
    exact (hf' _ g) this

/-- The empty sieve is never covering for the dense topology. -/
lemma bot_not_mem_dense (X : C) :
    (⊥ : Sieve X) ∉ (GrothendieckTopology.dense : GrothendieckTopology C) X := by
  intro h
  rcases h (Y := X) (f := 𝟙 X) with ⟨Z, g, hg⟩
  cases hg

/-- For the dense topology, closing the empty sieve yields the empty sieve. -/
lemma close_bot (X : C) :
    (GrothendieckTopology.dense : GrothendieckTopology C).close (⊥ : Sieve X) = (⊥ : Sieve X) := by
  ext Y f
  constructor
  · intro hf
    -- `hf` means `(⊥.pullback f) ∈ dense Y`, hence it would contain some arrow; contradiction.
    rcases
        (show ((⊥ : Sieve X).pullback f) ∈
              (GrothendieckTopology.dense : GrothendieckTopology C) Y from hf)
          (𝟙 Y) with ⟨Z, g, hg⟩
    cases hg
  · intro hf
    cases hf

/-- For the dense topology, closing the top sieve yields the top sieve. -/
lemma close_top (X : C) :
    (GrothendieckTopology.dense : GrothendieckTopology C).close (⊤ : Sieve X) = (⊤ : Sieve X) := by
  -- Use the characterisation `close S = ⊤ ↔ S ∈ J`.
  apply
    (GrothendieckTopology.close_eq_top_iff_mem
        (J₁ := (GrothendieckTopology.dense : GrothendieckTopology C)) (S := (⊤ : Sieve X))).2
  exact (GrothendieckTopology.dense : GrothendieckTopology C).top_mem X

/-- The closed sieve corresponding to `⊥` in the dense topology (as an element of the range). -/
noncomputable def closedBot (X : C) :
    ClosedSieve (C := C) (GrothendieckTopology.dense) X := by
  classical
  refine ⟨(⊥ : Sieve X), ?_⟩
  refine ⟨(⊥ : Sieve X), ?_⟩
  -- `sieveNucleus` is closure, and `close ⊥ = ⊥` for the dense topology.
  simp [close_bot (C := C) (X := X)]

/-- The closed sieve corresponding to `⊤` in the dense topology (as an element of the range). -/
noncomputable def closedTop (X : C) :
    ClosedSieve (C := C) (GrothendieckTopology.dense) X := by
  classical
  refine ⟨(⊤ : Sieve X), ?_⟩
  refine ⟨(⊤ : Sieve X), ?_⟩
  -- `sieveNucleus` is closure, and `close ⊤ = ⊤` for the dense topology.
  simp

theorem closedBot_ne_closedTop (X : C) : closedBot (C := C) X ≠ closedTop (C := C) X := by
  intro h
  have h' : ((closedBot (C := C) X : ClosedSieve (C := C) (GrothendieckTopology.dense) X) : Sieve X) =
      ((closedTop (C := C) X : ClosedSieve (C := C) (GrothendieckTopology.dense) X) : Sieve X) := by
    exact congrArg (fun (S : ClosedSieve (C := C) (GrothendieckTopology.dense) X) => (S : Sieve X)) h
  have hS : (⊥ : Sieve X) = (⊤ : Sieve X) := by
    simpa using h'
  have : (⊥ : Sieve X) (𝟙 X) := by
    have ht : (⊤ : Sieve X) (𝟙 X) := by simp
    -- Rewrite the goal using `hS : ⊥ = ⊤`, then discharge with `ht`.
    rw [hS]
    exact ht
  simpa using this

theorem not_subsingleton_closedSieve_dense (X : C) :
    ¬ Subsingleton (ClosedSieve (C := C) (GrothendieckTopology.dense) X) := by
  intro h
  haveI : Subsingleton (ClosedSieve (C := C) (GrothendieckTopology.dense) X) := h
  exact closedBot_ne_closedTop (C := C) X (Subsingleton.elim _ _)

end DenseTopology

end Topos
end Combinators
end LoF
end HeytingLean
