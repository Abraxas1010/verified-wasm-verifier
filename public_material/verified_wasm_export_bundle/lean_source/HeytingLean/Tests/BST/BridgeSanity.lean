import HeytingLean.BST.Bridge

namespace HeytingLean.Tests.BST.Bridge

open HeytingLean.BST
open HeytingLean.BST.Bridge

def U : UniverseBound := ⟨3, by decide⟩
def carrier : BoundedFinset U ℕ := ⟨{0, 1, 2}, by decide⟩
def gens : CarrierSlice carrier := ⟨{0, 1}, by simp [carrier]⟩
def whole : CarrierSlice carrier := CarrierSlice.whole carrier
def topOnly : CarrierSlice carrier := ⟨{2}, by simp [carrier]⟩

example :
    gens ≤ whole := by
  intro x hx
  simp [gens, whole, CarrierSlice.whole, carrier] at hx ⊢
  omega

example :
    whole ∈ (generatedNucleus gens).fixedPoints := by
  rw [mem_fixedPoints_iff]
  intro x hx
  simp [gens, whole, CarrierSlice.whole, carrier] at hx ⊢
  omega

example :
    topOnly ∉ (generatedNucleus gens).fixedPoints := by
  intro h
  have hsubset : gens ≤ topOnly := (mem_fixedPoints_iff.mp h)
  have : 0 ∈ (topOnly : Finset ℕ) := hsubset (by simp [gens])
  simp [topOnly] at this

end HeytingLean.Tests.BST.Bridge
