import Mathlib.Data.List.Basic
import HeytingLean.CodingTheory.InsDel.Subsequence

namespace HeytingLean
namespace CodingTheory
namespace InsDel

/-!
# Basic list operations for insertion/deletion coding theory
-/

def delNth : List α → Nat → List α
| [], _ => []
| _ :: xs, 0 => xs
| x :: xs, n + 1 => x :: delNth xs n

def insNth : List α → Nat → α → List α
| xs, 0, a => a :: xs
| [], _ + 1, a => [a]
| x :: xs, n + 1, a => x :: insNth xs n a

lemma delNth_nil (n : Nat) : delNth ([] : List α) n = [] := by
  rfl

lemma delNth_zero (xs : List α) : delNth xs 0 = xs.tail := by
  cases xs <;> rfl

lemma delNth_subseq (xs : List α) (n : Nat) : delNth xs n ⊴ xs := by
  induction xs generalizing n with
  | nil =>
      simp [delNth, Subseq.nil]
  | cons x xs ih =>
      cases n with
      | zero =>
          simpa [delNth] using (Subseq.drop (subseq_refl xs))
      | succ n =>
          simpa [delNth] using (Subseq.keep (ih n))

def sDel {α : Type _} (xs : List α) (n : Nat) : List α := delNth xs n
def sIns {α : Type _} (xs : List α) (n : Nat) (a : α) : List α := insNth xs n a

lemma length_delNth {α : Type _} (xs : List α) (n : Nat) (h : n < xs.length) :
    (delNth xs n).length = xs.length - 1 := by
  induction xs generalizing n with
  | nil =>
      cases h
  | cons x xs ih =>
      cases n with
      | zero =>
          simp [delNth]
      | succ n =>
          have h' : n < xs.length := Nat.lt_of_succ_lt_succ h
          simp [delNth, ih n h', Nat.add_comm]
          omega

lemma insNth_delNth_get {α : Type _} (xs : List α) (n : Nat) (h : n < xs.length) :
    insNth (delNth xs n) n (xs.get ⟨n, h⟩) = xs := by
  induction xs generalizing n with
  | nil =>
      cases h
  | cons x xs ih =>
      cases n with
      | zero =>
          simp [delNth, insNth]
      | succ n =>
          have h' : n < xs.length := Nat.lt_of_succ_lt_succ h
          simp [delNth, insNth]
          exact ih n h'

end InsDel
end CodingTheory
end HeytingLean
