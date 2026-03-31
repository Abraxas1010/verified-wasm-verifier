import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace HeytingLean
namespace CodingTheory
namespace InsDel

/-!
# Levenshtein-style distance via LCS length

We follow the classic insertion/deletion-only variant:
`dist(X,Y) = |X| + |Y| - 2 * lcsLength(X,Y)`.
-/

def lcsLength [DecidableEq α] : List α → List α → Nat
| [], _ => 0
| _, [] => 0
| x :: xs, y :: ys =>
    if x = y then
      Nat.succ (lcsLength xs ys)
    else
      Nat.max (lcsLength xs (y :: ys)) (lcsLength (x :: xs) ys)
termination_by
  xs ys => xs.length + ys.length
decreasing_by
  all_goals
    simp
    try omega

lemma lcsLength_nil_left [DecidableEq α] (ys : List α) :
    lcsLength ([] : List α) ys = 0 := by
  simp [lcsLength]

lemma lcsLength_nil_right [DecidableEq α] (xs : List α) :
    lcsLength xs ([] : List α) = 0 := by
  cases xs <;> simp [lcsLength]

lemma lcsLength_self [DecidableEq α] (xs : List α) : lcsLength xs xs = xs.length := by
  induction xs with
  | nil => simp [lcsLength]
  | cons x xs ih =>
      simp [lcsLength, ih]

def levDist [DecidableEq α] (xs ys : List α) : Nat :=
  xs.length + ys.length - 2 * lcsLength xs ys

lemma levDist_nil_left [DecidableEq α] (ys : List α) :
    levDist ([] : List α) ys = ys.length := by
  simp [levDist, lcsLength]

lemma levDist_nil_right [DecidableEq α] (xs : List α) :
    levDist xs ([] : List α) = xs.length := by
  cases xs <;> simp [levDist, lcsLength]

lemma levDist_self [DecidableEq α] (xs : List α) :
    levDist xs xs = 0 := by
  simp [levDist, lcsLength_self]
  omega

end InsDel
end CodingTheory
end HeytingLean
