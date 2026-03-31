import Mathlib.Data.Real.Basic
import Batteries.Data.List.Basic

/-!
# ProbVec (Real-valued probability vectors)

Lightweight, proof-friendly container for probability-like vectors over ℝ.
This is an executable-first scaffold; we avoid heavy summation lemmas for now
and provide total functions to build and query values.

Note: We intentionally do not include Prop fields (nonnegativity/sum1) yet to
keep strict builds fast; those can be added per-lemma in proof passes.
-/

namespace HeytingLean
namespace Math

structure ProbVec where
  data : Array ℝ

namespace ProbVec

@[simp] def fromArray (xs : Array ℝ) : ProbVec := { data := xs }

@[simp] def length (p : ProbVec) : Nat := p.data.size

@[simp] def get! (p : ProbVec) (i : Nat) : ℝ := p.data[i]!

/-! A simple, proof-friendly list sum, then array sum defined via `toList`. -/

def sumList : List ℝ → ℝ
  | []      => 0
  | x :: xs => x + sumList xs

@[simp] lemma sumList_nil : sumList [] = 0 := rfl
@[simp] lemma sumList_cons (x : ℝ) (xs : List ℝ) : sumList (x :: xs) = x + sumList xs := rfl

@[simp] def sum (xs : Array ℝ) : ℝ := sumList xs.toList

noncomputable def normalizeR (xs : Array ℝ) : ProbVec :=
  let s := sum xs
  if s ≤ 0 then
    let n := xs.size
    if n = 0 then fromArray xs
    else fromArray (Array.replicate n ((1 : ℝ) / (n : ℝ)))
  else
    fromArray (xs.map (fun x => x / s))

@[simp] def map (f : ℝ → ℝ) (p : ProbVec) : ProbVec := fromArray (p.data.map f)

/-! Lightweight predicates for later proof passes. -/

def AllNonneg (xs : Array ℝ) : Prop := ∀ i, i < xs.size → 0 ≤ xs[i]!
def SumIs (xs : Array ℝ) (t : ℝ) : Prop := sum xs = t

/-! List-level helpers for normalization proofs. -/

@[simp] lemma sumList_append (xs ys : List ℝ) :
    sumList (xs ++ ys) = sumList xs + sumList ys := by
  induction xs with
  | nil => simp [sumList]
  | cons x xs ih => simp [sumList, ih, add_left_comm, add_comm]

lemma sumList_map_mul_right (c : ℝ) :
    ∀ xs, sumList (xs.map (fun x => x * c)) = sumList xs * c
  | []      => by simp [sumList]
  | x :: xs => by
      have ih := sumList_map_mul_right (c := c) xs
      simp [sumList, add_mul, ih]

lemma sumList_map_div (s : ℝ) (xs : List ℝ) :
    sumList (xs.map (fun x => x / s)) = (sumList xs) / s := by
  simpa [div_eq_mul_inv, mul_comm] using sumList_map_mul_right (c := s⁻¹) xs

lemma sumList_replicate :
    ∀ (n : Nat) (c : ℝ), sumList (List.replicate n c) = (n : ℝ) * c
  | 0, c => by simp
  | Nat.succ n, c => by
      have ih := sumList_replicate n c
      -- List.replicate (n+1) c = c :: List.replicate n c
      simp [List.replicate_succ, ih, Nat.cast_succ, add_mul, one_mul, add_comm]

noncomputable def normalizeListR (xs : List ℝ) : List ℝ :=
  let s := sumList xs
  if s ≤ 0 then
    match xs with
    | []      => []
    | _ :: _  => List.replicate xs.length ((1 : ℝ) / (xs.length : ℝ))
  else
    xs.map (fun x => x / s)

lemma normalizeList_sum1_of_nonempty {xs : List ℝ}
    (h : xs ≠ []) : sumList (normalizeListR xs) = 1 := by
  classical
  unfold normalizeListR
  by_cases hsum : sumList xs ≤ 0
  · cases xs with
    | nil => cases h rfl
    | cons x tl =>
      let n := tl.length + 1
      have hpos : 0 < n := Nat.succ_pos _
      have hne : (n : ℝ) ≠ 0 := by exact ne_of_gt (Nat.cast_pos.mpr hpos)
      have : sumList (List.replicate n ((n : ℝ)⁻¹)) = 1 := by
        calc
          sumList (List.replicate n ((n : ℝ)⁻¹))
              = (n : ℝ) * (n : ℝ)⁻¹ := by simp [sumList_replicate]
          _ = (n : ℝ) / (n : ℝ) := by simp [div_eq_mul_inv]
          _ = 1 := by simp [hne]
      have hcond : x + sumList tl ≤ 0 := by simpa [sumList] using hsum
      simpa [normalizeListR, hcond, n]
        using this
  · have hpos : 0 < sumList xs := lt_of_not_ge hsum
    have hne : sumList xs ≠ 0 := ne_of_gt hpos
    have : sumList (xs.map (fun x => x / sumList xs)) = 1 := by
      simp [sumList_map_div, div_self hne]
    simpa [hsum]

/-! Optionally, array-level normalization sum lemma can be derived by
    bridging through `toList`/`toArray`. We keep it list-first to
    avoid heavier imports. -/

end ProbVec

end Math
end HeytingLean
