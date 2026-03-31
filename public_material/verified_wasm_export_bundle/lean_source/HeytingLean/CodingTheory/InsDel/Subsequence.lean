import Mathlib.Data.List.Basic

namespace HeytingLean
namespace CodingTheory
namespace InsDel

/-!
# Subsequence relation for insertion/deletion codes

This is a lightweight, Lean4-native subsequence relation used for
insertion/deletion distance and codes.
-/

inductive Subseq : List α → List α → Prop
| nil (ys : List α) : Subseq [] ys
| drop {x xs ys} : Subseq xs ys → Subseq xs (x :: ys)
| keep {x xs ys} : Subseq xs ys → Subseq (x :: xs) (x :: ys)

infix:50 " ⊴ " => Subseq

lemma subseq_refl (xs : List α) : xs ⊴ xs := by
  induction xs with
  | nil => exact Subseq.nil []
  | cons x xs ih => exact Subseq.keep ih

lemma subseq_nil_left (ys : List α) : ([] : List α) ⊴ ys := by
  exact Subseq.nil ys

end InsDel
end CodingTheory
end HeytingLean
