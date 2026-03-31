import HeytingLean.Frankl.Defs

/-
- source_type: test infrastructure
- attribution_status: n/a
- claim_status: n/a
- proof_status: proved
-/

namespace HeytingLean
namespace Frankl
namespace TestGoals

set_option linter.unnecessarySeqFocus false

/-- Test family 1: `{∅, {0}, {0,1}}`. -/
def F1 : Finset (Finset (Fin 2)) :=
  [ (∅ : Finset (Fin 2))
  , ({0} : Finset (Fin 2))
  , ({0, 1} : Finset (Fin 2))
  ].toFinset

theorem F1_uc : Frankl.UnionClosed F1 := by
  intro A B hA hB
  simp [F1] at hA hB ⊢
  rcases hA with rfl | rfl | rfl <;>
    rcases hB with rfl | rfl | rfl <;>
    simp
  all_goals native_decide

theorem F1_frankl : ∃ x, Frankl.Abundant F1 x := by
  refine ⟨(0 : Fin 2), ?_⟩
  simp [Frankl.Abundant, Frankl.frequency, F1]
  native_decide

/-- Test family 2: powerset of `{0,1}`. -/
def F2 : Finset (Finset (Fin 2)) :=
  [ (∅ : Finset (Fin 2))
  , ({0} : Finset (Fin 2))
  , ({1} : Finset (Fin 2))
  , ({0, 1} : Finset (Fin 2))
  ].toFinset

theorem F2_uc : Frankl.UnionClosed F2 := by
  intro A B hA hB
  simp [F2] at hA hB ⊢
  rcases hA with rfl | rfl | rfl | rfl <;>
    rcases hB with rfl | rfl | rfl | rfl <;>
    simp
  all_goals native_decide

theorem F2_frankl : ∃ x, Frankl.Abundant F2 x := by
  refine ⟨(0 : Fin 2), ?_⟩
  simp [Frankl.Abundant, Frankl.frequency, F2]
  native_decide

/-- Test family 3: `{{0}, {1}, {0,1}}` (no empty set). -/
def F3 : Finset (Finset (Fin 2)) :=
  [ ({0} : Finset (Fin 2))
  , ({1} : Finset (Fin 2))
  , ({0, 1} : Finset (Fin 2))
  ].toFinset

theorem F3_uc : Frankl.UnionClosed F3 := by
  intro A B hA hB
  simp [F3] at hA hB ⊢
  rcases hA with rfl | rfl | rfl <;>
    rcases hB with rfl | rfl | rfl <;>
    simp
  all_goals native_decide

theorem F3_frankl : ∃ x, Frankl.Abundant F3 x := by
  refine ⟨(0 : Fin 2), ?_⟩
  simp [Frankl.Abundant, Frankl.frequency, F3]
  native_decide

/-- Test family 4: `{{0,1}, {1,2}, {0,1,2}}`. -/
def F4 : Finset (Finset (Fin 3)) :=
  [ ({0, 1} : Finset (Fin 3))
  , ({1, 2} : Finset (Fin 3))
  , ({0, 1, 2} : Finset (Fin 3))
  ].toFinset

theorem F4_uc : Frankl.UnionClosed F4 := by
  intro A B hA hB
  simp [F4] at hA hB ⊢
  rcases hA with rfl | rfl | rfl <;>
    rcases hB with rfl | rfl | rfl <;>
    simp
  all_goals native_decide

theorem F4_frankl : ∃ x, Frankl.Abundant F4 x := by
  refine ⟨(1 : Fin 3), ?_⟩
  simp [Frankl.Abundant, Frankl.frequency, F4]
  native_decide

/-- Test family 5: powerset of `{0,1,2}` inside `Fin 5` (8 sets). -/
def F5 : Finset (Finset (Fin 5)) :=
  ({0, 1, 2} : Finset (Fin 5)).powerset

theorem F5_uc : Frankl.UnionClosed F5 := by
  intro A B hA hB
  simp [F5, Finset.mem_powerset] at hA hB ⊢
  exact Finset.union_subset hA hB

theorem F5_frankl : ∃ x, Frankl.Abundant F5 x := by
  refine ⟨(0 : Fin 5), ?_⟩
  have hfreq : Frankl.frequency F5 (0 : Fin 5) = 4 := by
    native_decide
  have hcard : F5.card = 8 := by
    simp [F5]
  unfold Frankl.Abundant
  rw [hfreq, hcard]

end TestGoals
end Frankl
end HeytingLean
