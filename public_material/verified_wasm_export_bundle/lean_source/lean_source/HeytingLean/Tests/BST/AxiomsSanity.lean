import HeytingLean.BST.Foundation

namespace HeytingLean.Tests.BST.AxiomsSanity

open HeytingLean.BST

def U : UniverseBound := ⟨4, by decide⟩

def s012 : BoundedFinset U ℕ := ⟨{0, 1, 2}, by decide⟩
def s1 : BoundedFinset U ℕ := BoundedFinset.singleton U 1
def s2 : BoundedFinset U ℕ := BoundedFinset.singleton U 2
def family : Finset (BoundedFinset U ℕ) := {s1, s2}

lemma family_nonempty :
    ∀ s ∈ family, ((s : BoundedFinset U ℕ) : Finset ℕ).Nonempty := by
  intro s hs
  simp [family, s1, s2] at hs
  rcases hs with rfl | rfl
  · simp [BoundedFinset.singleton]
  · simp [BoundedFinset.singleton]

example : ((s012 : Finset ℕ).card ≤ U.nM) := by
  exact afb s012

example :
    ∃ t : BoundedFinset U ℕ, ∀ x, x ∈ (t : Finset ℕ) ↔ x ∈ (s012 : Finset ℕ) ∧ x % 2 = 0 := by
  exact bounded_separation s012 (fun x => x % 2 = 0)

example :
    ∃ s : BoundedFinset U ℕ, 1 ∈ (s : Finset ℕ) ∧ 2 ∈ (s : Finset ℕ) := by
  exact bounded_pairing (U := U) 1 2 (by decide)

example : (BoundedFinset.pair? U 1 2).isSome = true := by
  native_decide

example : bst_choice family family_nonempty s1 (by simp [family]) = 1 := by
  native_decide

example : bst_choice family family_nonempty s2 (by simp [family]) = 2 := by
  native_decide

example :
    bst_choice family family_nonempty s1 (by simp [family]) ∈
      ((s1 : BoundedFinset U ℕ) : Finset ℕ) := by
  exact bst_choice_mem family family_nonempty s1 (by simp [family])

end HeytingLean.Tests.BST.AxiomsSanity
