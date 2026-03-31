import HeytingLean.ModalCategorySets.Framework.InfiniteButtons

namespace HeytingLean.ModalCategorySets.Framework

open scoped Classical
open HeytingLean.ModalCategorySets.Framework.Equality

namespace Buttons

def buttonZero : Fin 2 := Fin.mk 0 (by decide)
def buttonOne : Fin 2 := Fin.mk 1 (by decide)

/-- A concrete reachable world where the two button gadgets are cross-coupled:
`0` and `2` agree, `1` and `3` agree, but neither button is currently pushed. -/
def crossCoupledNatValuation : Valuation Nat
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 1
  | n + 4 => n + 2

theorem crossCoupledNat_surjective : Function.Surjective crossCoupledNatValuation := by
  intro y
  cases y with
  | zero =>
      exact Exists.intro 0 rfl
  | succ y =>
      cases y with
      | zero =>
          exact Exists.intro 1 rfl
      | succ y =>
          exact Exists.intro (y + 4) (by simp [crossCoupledNatValuation])

theorem crossCoupledNat_pair0_false_all :
    ¬ HoldsInfAll crossCoupledNatValuation (pairEq 0) := by
  rw [holdsInfAll_pure_iff_holds (ρ := crossCoupledNatValuation) (φ := pairEq 0) (by trivial)]
  change ¬ (crossCoupledNatValuation 0 = crossCoupledNatValuation 1)
  decide

theorem crossCoupledNat_pair1_false_all :
    ¬ HoldsInfAll crossCoupledNatValuation (pairEq 1) := by
  rw [holdsInfAll_pure_iff_holds (ρ := crossCoupledNatValuation) (φ := pairEq 1) (by trivial)]
  change ¬ (crossCoupledNatValuation 2 = crossCoupledNatValuation 3)
  decide

theorem crossCoupledNat_pair0_false_surj :
    ¬ HoldsInfSurj crossCoupledNatValuation (pairEq 0) := by
  rw [holdsInfSurj_pure_iff_holds (ρ := crossCoupledNatValuation) (φ := pairEq 0) (by trivial)]
  change ¬ (crossCoupledNatValuation 0 = crossCoupledNatValuation 1)
  decide

theorem crossCoupledNat_pair1_false_surj :
    ¬ HoldsInfSurj crossCoupledNatValuation (pairEq 1) := by
  rw [holdsInfSurj_pure_iff_holds (ρ := crossCoupledNatValuation) (φ := pairEq 1) (by trivial)]
  change ¬ (crossCoupledNatValuation 2 = crossCoupledNatValuation 3)
  decide

theorem crossCoupledNat_pattern_empty_all :
    ButtonPatternAll (σ := crossCoupledNatValuation) (n := 2) (∅ : Finset (Fin 2)) := by
  intro i
  fin_cases i
  · constructor
    · exact False.elim ∘ crossCoupledNat_pair0_false_all
    · intro h
      simp at h
  · constructor
    · exact False.elim ∘ crossCoupledNat_pair1_false_all
    · intro h
      simp at h

theorem crossCoupledNat_pattern_empty_surj :
    ButtonPatternSurj (σ := crossCoupledNatValuation) (n := 2) (∅ : Finset (Fin 2)) := by
  intro i
  fin_cases i
  · constructor
    · exact False.elim ∘ crossCoupledNat_pair0_false_surj
    · intro h
      simp at h
  · constructor
    · exact False.elim ∘ crossCoupledNat_pair1_false_surj
    · intro h
      simp at h

theorem crossCoupledNat_pair0_implies_pair1_all {β : Type} [Infinite β] (f : Nat → β)
    (h0 : HoldsInfAll (fun k => f (crossCoupledNatValuation k)) (pairEq 0)) :
    HoldsInfAll (fun k => f (crossCoupledNatValuation k)) (pairEq 1) := by
  rw [holdsInfAll_pure_iff_holds
    (ρ := fun k => f (crossCoupledNatValuation k))
    (φ := pairEq 0)
    (by trivial)] at h0
  rw [holdsInfAll_pure_iff_holds
    (ρ := fun k => f (crossCoupledNatValuation k))
    (φ := pairEq 1)
    (by trivial)]
  change f (crossCoupledNatValuation 2) = f (crossCoupledNatValuation 3)
  change f (crossCoupledNatValuation 0) = f (crossCoupledNatValuation 1) at h0
  simpa [crossCoupledNatValuation] using h0

theorem crossCoupledNat_pair0_implies_pair1_surj {β : Type} [Infinite β] (f : Nat → β)
    (h0 : HoldsInfSurj (fun k => f (crossCoupledNatValuation k)) (pairEq 0)) :
    HoldsInfSurj (fun k => f (crossCoupledNatValuation k)) (pairEq 1) := by
  rw [holdsInfSurj_pure_iff_holds
    (ρ := fun k => f (crossCoupledNatValuation k))
    (φ := pairEq 0)
    (by trivial)] at h0
  rw [holdsInfSurj_pure_iff_holds
    (ρ := fun k => f (crossCoupledNatValuation k))
    (φ := pairEq 1)
    (by trivial)]
  change f (crossCoupledNatValuation 2) = f (crossCoupledNatValuation 3)
  change f (crossCoupledNatValuation 0) = f (crossCoupledNatValuation 1) at h0
  simpa [crossCoupledNatValuation] using h0

theorem crossCoupledNat_no_singleton_zero_extension_all :
    ¬ Nonempty (AllButtonPatternWitness
      (ρ := crossCoupledNatValuation)
      (s := ({buttonZero} : Finset (Fin 2)))) := by
  intro h
  rcases h with ⟨w⟩
  letI := w.hβ
  have h0 : HoldsInfAll (fun k => w.f (crossCoupledNatValuation k)) (pairEq 0) := by
    simpa [buttonZero] using (w.pattern buttonZero).2 (by simp [buttonZero])
  have h1 : HoldsInfAll (fun k => w.f (crossCoupledNatValuation k)) (pairEq 1) :=
    crossCoupledNat_pair0_implies_pair1_all w.f h0
  have hNot1 : ¬ HoldsInfAll (fun k => w.f (crossCoupledNatValuation k)) (pairEq 1) := by
    intro hPair
    have : buttonOne ∈ ({buttonZero} : Finset (Fin 2)) := by
      exact (w.pattern buttonOne).1 (by simpa [buttonOne] using hPair)
    have hEq : buttonOne = buttonZero := by simpa using this
    exact (by decide : buttonOne ≠ buttonZero) hEq
  exact hNot1 h1

theorem crossCoupledNat_no_singleton_zero_extension_surj :
    ¬ Nonempty (SurjButtonPatternWitness
      (ρ := crossCoupledNatValuation)
      (s := ({buttonZero} : Finset (Fin 2)))) := by
  intro h
  rcases h with ⟨w⟩
  letI := w.hβ
  have h0 : HoldsInfSurj (fun k => w.f (crossCoupledNatValuation k)) (pairEq 0) := by
    simpa [buttonZero] using (w.pattern buttonZero).2 (by simp [buttonZero])
  have h1 : HoldsInfSurj (fun k => w.f (crossCoupledNatValuation k)) (pairEq 1) :=
    crossCoupledNat_pair0_implies_pair1_surj w.f h0
  have hNot1 : ¬ HoldsInfSurj (fun k => w.f (crossCoupledNatValuation k)) (pairEq 1) := by
    intro hPair
    have : buttonOne ∈ ({buttonZero} : Finset (Fin 2)) := by
      exact (w.pattern buttonOne).1 (by simpa [buttonOne] using hPair)
    have hEq : buttonOne = buttonZero := by simpa using this
    exact (by decide : buttonOne ≠ buttonZero) hEq
  exact hNot1 h1

end Buttons

end HeytingLean.ModalCategorySets.Framework
