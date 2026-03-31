import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import HeytingLean.CodingTheory.InsDel.Subsequence

namespace HeytingLean
namespace CodingTheory
namespace InsDel

/-!
# Insertion/deletion distance

This is a pure insertion/deletion distance (no substitutions).
-/

def insDelDist [DecidableEq α] : List α → List α → Nat
| [], ys => ys.length
| xs, [] => xs.length
| x :: xs, y :: ys =>
    if x = y then
      insDelDist xs ys
    else
      Nat.succ (Nat.min (insDelDist xs (y :: ys)) (insDelDist (x :: xs) ys))
termination_by
  xs ys => xs.length + ys.length
decreasing_by
  all_goals
    simp
    try omega

lemma insDelDist_nil_left [DecidableEq α] (ys : List α) :
    insDelDist ([] : List α) ys = ys.length := by
  simp [insDelDist]

lemma insDelDist_nil_right [DecidableEq α] (xs : List α) :
    insDelDist xs ([] : List α) = xs.length := by
  cases xs <;> simp [insDelDist]

lemma insDelDist_self [DecidableEq α] (xs : List α) : insDelDist xs xs = 0 := by
  induction xs with
  | nil => simp [insDelDist]
  | cons x xs ih =>
      simp [insDelDist, ih]

end InsDel
end CodingTheory
end HeytingLean
