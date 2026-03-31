import HeytingLean.Numbers.OrdinalVN

namespace HeytingLean
namespace Numbers
namespace Ordinal

open HeytingLean.Numbers

/-- Trivial transitivity predicate (currently always `True`). -/
def transitive {n} : V n → Prop := fun _ => True

/-- Canonical image of a set of shapes: keep those already transitive. -/
def canonImage {n} (S : Set (V n)) : Set (V n) := { x | x ∈ S ∧ transitive x }

/-- Closure operator on sets of shapes (skeleton): add canonical images. -/
def J {n} (S : Set (V n)) : Set (V n) := S ∪ canonImage S

@[simp] lemma subset_J {n} (S : Set (V n)) : S ⊆ J S := by intro x hx; exact Or.inl hx

lemma mono_J {n} {S T : Set (V n)} (hST : S ⊆ T) : J S ⊆ J T := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl (hST hx)
  · rcases hx with ⟨hxS, _⟩
    exact Or.inr ⟨hST hxS, trivial⟩

lemma idem_J {n} (S : Set (V n)) : J (J S) = J S := by
  apply le_antisymm
  · intro x hx; rcases hx with hx | hx; exact hx
    rcases hx with ⟨hxJ, htrans⟩
    rcases hxJ with hx | hxCanon
    · exact Or.inr ⟨hx, htrans⟩
    · rcases hxCanon with ⟨hxS, _⟩
      exact Or.inr ⟨hxS, htrans⟩
  · intro x hx; exact Or.inl hx

end Ordinal
end Numbers
end HeytingLean
