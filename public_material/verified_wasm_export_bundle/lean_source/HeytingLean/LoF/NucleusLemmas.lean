import Mathlib.Order.Nucleus

/-!
# Nucleus helper lemmas (fixed-point subtype style)

Safe, general facts that do not assume locale/frame structure.
-/

namespace HeytingLean
namespace LoF

/-- If `x` is fixed by nuclei `j` and `k`, then it is fixed by their meet `j ⊓ k` (set-level). -/
lemma mem_fix_inf_of_mem_fixes
  {α : Type*} [CompleteLattice α]
  (j k : Nucleus α) {x : α}
  (hxj : j x = x) (hxk : k x = x) :
  (j ⊓ k) x = x := by
  -- (j ⊓ k) acts pointwise via inf on α: (j ⊓ k) x = j x ⊓ k x
  -- hence it fixes any `x` fixed by both
  simp [hxj, hxk]

/-- Subtype map from the intersection of fixed points into the fixed points of the meet. -/
def fix_inter_to_fix_inf
  {α : Type*} [CompleteLattice α]
  (j k : Nucleus α) :
  {x : α // j x = x ∧ k x = x} → {x : α // (j ⊓ k) x = x} :=
  fun y => ⟨y.1, mem_fix_inf_of_mem_fixes j k y.2.1 y.2.2⟩

/-- The canonical map from the intersection of fixed points of `j` and `k` into
the fixed points of their meet is injective at the level of underlying
elements. -/
lemma fix_inter_to_fix_inf_injective
  {α : Type*} [CompleteLattice α]
  (j k : Nucleus α) :
  Function.Injective (fix_inter_to_fix_inf (j := j) (k := k)) := by
  intro x y h
  -- Equality of subtypes is determined by equality of carriers.
  apply Subtype.ext
  -- Compare the underlying elements via `Subtype.val` on the codomain.
  have hval :
      (fix_inter_to_fix_inf (j := j) (k := k) x).1 =
        (fix_inter_to_fix_inf (j := j) (k := k) y).1 := by
    have h' :=
      congrArg (fun z : {x : _ // (j ⊓ k) x = x} => z.1) h
    simpa [fix_inter_to_fix_inf] using h'
  simpa [fix_inter_to_fix_inf] using hval

end LoF
end HeytingLean
