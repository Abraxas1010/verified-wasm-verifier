import Mathlib.Data.Set.Lattice

/-!
# Causal Lens — Ancestral Hull

Minimal bridge for a causal DAG/SCM‑style lens. We model a predecessor map
`preds : V → Set V` and define the reachability relation along forward edges
(`u → v` iff `u ∈ preds v`). The ancestral hull of a set `S` is
`Hull S = { u | ∃ s ∈ S, u ↠ s }`.

Properties provided:
- `extensive : S ⊆ Hull S`
- `monotone  : S ⊆ T → Hull S ⊆ Hull T`
- `idempotent : Hull (Hull S) = Hull S`
- `inter_subset : Hull (S ∩ T) ⊆ Hull S ∩ Hull T`

This operator is an (extensive) closure under the ancestor preorder; it need
not preserve binary meets as equality, but we include the useful subset lemma.
-/

namespace HeytingLean
namespace Bridges
namespace Causal

open Set

structure Model (V : Type u) where
  preds : V → Set V

namespace Model

variable {V : Type u}

def stepRel (M : Model V) (u v : V) : Prop := u ∈ M.preds v

inductive Reach (M : Model V) : V → V → Prop
| refl (v : V) : Reach M v v
| tail {u v w} : stepRel M u v → Reach M v w → Reach M u w

/-- Ancestral hull: all ancestors of elements of `S`. -/
def Hull (M : Model V) (S : Set V) : Set V := fun u => ∃ s, s ∈ S ∧ Reach M u s

@[simp] lemma extensive (M : Model V) (S : Set V) : S ⊆ Hull M S := by
  intro s hs; exact ⟨s, hs, Reach.refl _⟩

lemma monotone (M : Model V) {S T : Set V} (hST : S ⊆ T) : Hull M S ⊆ Hull M T := by
  intro u hu; rcases hu with ⟨s, hs, hrs⟩; exact ⟨s, hST hs, hrs⟩

/-- Reachability is transitive within the causal graph. -/
lemma reach_trans (M : Model V) {a b c : V} (hab : Reach M a b) (hbc : Reach M b c) : Reach M a c := by
  revert c
  induction hab with
  | refl a => intro c hbc; simpa using hbc
  | @tail a v b hstep hvb ih =>
      intro c hbc
      have : Reach M v c := ih hbc
      exact Reach.tail hstep this

/-- Taking the hull twice does not add new elements (idempotence). -/
lemma idempotent (M : Model V) (S : Set V) : Hull M (Hull M S) = Hull M S := by
  apply le_antisymm
  · intro u hu; rcases hu with ⟨x, hx, hux⟩; rcases hx with ⟨s, hs, hxs⟩; exact ⟨s, hs, reach_trans M hux hxs⟩
  · exact monotone (M := M) (S := S) (T := Hull M S) (extensive (M := M) S)

/-- The hull of an intersection sits inside the intersection of hulls. -/
lemma inter_subset (M : Model V) {S T : Set V} : Hull M (S ∩ T) ⊆ (Hull M S) ∩ (Hull M T) := by
  intro u hu; rcases hu with ⟨s, hs, hus⟩; exact And.intro ⟨s, hs.left, hus⟩ ⟨s, hs.right, hus⟩

end Model

end Causal
end Bridges
end HeytingLean
