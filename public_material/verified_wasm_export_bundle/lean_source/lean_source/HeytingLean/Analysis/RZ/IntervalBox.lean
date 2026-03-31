import HeytingLean.Analysis.RZ.Interval

namespace HeytingLean
namespace Analysis
namespace RZ

/-!
# Vector Interval Arithmetic (Boxes)

This module lifts the scalar interval arithmetic from `Interval` to n-dimensional boxes.
A box is a product of intervals, representing a hyperrectangle in ℚⁿ.

## Main Definitions

* `IntervalBox n`: An n-dimensional box (product of intervals)
* `IntervalBox.mem`: Membership predicate for vectors in boxes
* `IntervalBox.add`: Componentwise interval addition
* `IntervalBox.neg`: Componentwise negation
* `IntervalBox.sub`: Componentwise subtraction

## Soundness

All operations are proven sound: if x ∈ I and y ∈ J then x ⊕ y ∈ I ⊕ J.
-/

open Interval

/-- An n-dimensional box: a product of intervals. -/
structure IntervalBox (n : ℕ) where
  intervals : Fin n → Interval

namespace IntervalBox

variable {n : ℕ}

/-! ## Membership -/

/-- A vector is in a box iff each component is in the corresponding interval. -/
instance : Membership (Fin n → ℚ) (IntervalBox n) :=
  ⟨fun box x => ∀ i, x i ∈ box.intervals i⟩

@[simp] lemma mem_iff {x : Fin n → ℚ} {box : IntervalBox n} :
    x ∈ box ↔ ∀ i, x i ∈ box.intervals i := Iff.rfl

/-- The set represented by a box. -/
def toSet (box : IntervalBox n) : Set (Fin n → ℚ) := {x | x ∈ box}

/-! ## Constructors -/

/-- Build a box from a vector of lo/hi pairs. -/
def make (lo hi : Fin n → ℚ) (h : ∀ i, lo i ≤ hi i) : IntervalBox n :=
  { intervals := fun i => ⟨lo i, hi i, h i⟩ }

/-- A degenerate box containing a single point. -/
def ofPoint (x : Fin n → ℚ) : IntervalBox n :=
  { intervals := fun i => Interval.ofRat (x i) }

@[simp] lemma mem_ofPoint {x y : Fin n → ℚ} : y ∈ ofPoint x ↔ y = x := by
  constructor
  · intro hy
    ext i
    have hi := hy i
    simp only [ofPoint, Interval.mem_ofRat] at hi
    exact hi
  · intro hxy
    subst hxy
    intro i
    simp only [ofPoint, Interval.mem_ofRat]

/-! ## Box Properties -/

/-- The lower corner of a box. -/
def lo (box : IntervalBox n) : Fin n → ℚ := fun i => (box.intervals i).lo

/-- The upper corner of a box. -/
def hi (box : IntervalBox n) : Fin n → ℚ := fun i => (box.intervals i).hi

/-- Width of a box in each dimension. -/
def widths (box : IntervalBox n) : Fin n → ℚ := fun i => (box.intervals i).width

/-! ## Information Order (Reverse Inclusion) -/

instance : LE (IntervalBox n) :=
  ⟨fun I J => ∀ i, I.intervals i ≤ J.intervals i⟩

@[simp] lemma le_def {I J : IntervalBox n} : I ≤ J ↔ ∀ i, I.intervals i ≤ J.intervals i := Iff.rfl

instance : Preorder (IntervalBox n) where
  le := (· ≤ ·)
  lt := fun I J => I ≤ J ∧ ¬ J ≤ I
  le_refl I := fun i => le_refl (I.intervals i)
  le_trans I J K hIJ hJK := fun i => le_trans (hIJ i) (hJK i)

lemma le_iff_subset {I J : IntervalBox n} : I ≤ J ↔ J.toSet ⊆ I.toSet := by
  constructor
  · intro hIJ x hx i
    have hxi := hx i
    exact Interval.le_iff_subset.mp (hIJ i) hxi
  · intro hsub i
    rw [Interval.le_iff_subset]
    intro q hq
    -- Build a vector with q in position i and lo in other positions
    let v : Fin n → ℚ := fun j => if j = i then q else (J.intervals j).lo
    have hv : v ∈ J := by
      intro j
      simp only [v]
      split_ifs with heq
      · subst heq; exact hq
      · exact ⟨le_refl _, (J.intervals j).lo_le_hi⟩
    have hvI := hsub hv
    have hvi := hvI i
    simp only [v, ↓reduceIte] at hvi
    exact hvi

/-! ## Componentwise Operations -/

/-- Componentwise negation. -/
def neg (box : IntervalBox n) : IntervalBox n :=
  { intervals := fun i => Interval.neg (box.intervals i) }

/-- Componentwise addition at precision p. -/
def add (p : Nat) (I J : IntervalBox n) : IntervalBox n :=
  { intervals := fun i => Interval.add p (I.intervals i) (J.intervals i) }

/-- Componentwise subtraction at precision p. -/
def sub (p : Nat) (I J : IntervalBox n) : IntervalBox n :=
  add p I (neg J)

/-! ## Soundness Theorems -/

/-- Negation is sound: if x ∈ I then -x ∈ neg I. -/
lemma mem_neg {box : IntervalBox n} {x : Fin n → ℚ} (hx : x ∈ box) :
    (fun i => -x i) ∈ neg box := by
  intro i
  have hxi := hx i
  simp only [neg, Interval.neg, Interval.mem_iff] at *
  constructor
  · exact neg_le_neg hxi.2
  · exact neg_le_neg hxi.1

/-- Addition is sound: if x ∈ I and y ∈ J then x + y ∈ add p I J. -/
lemma mem_add {p : Nat} {I J : IntervalBox n} {x y : Fin n → ℚ}
    (hx : x ∈ I) (hy : y ∈ J) :
    (fun i => x i + y i) ∈ add p I J := by
  intro i
  exact Interval.mem_add (hx i) (hy i)

/-- Subtraction is sound: if x ∈ I and y ∈ J then x - y ∈ sub p I J. -/
lemma mem_sub {p : Nat} {I J : IntervalBox n} {x y : Fin n → ℚ}
    (hx : x ∈ I) (hy : y ∈ J) :
    (fun i => x i - y i) ∈ sub p I J := by
  have hny : (fun i => -y i) ∈ neg J := mem_neg hy
  have hadd := @mem_add n p I (neg J) x (fun i => -y i) hx hny
  simp only [sub]
  have heq : (fun i => x i - y i) = (fun i => x i + -y i) := by
    ext i
    ring
  rw [heq]
  exact hadd

/-! ## Monotonicity -/

/-- Addition is monotone in both arguments. -/
lemma add_mono {p : Nat} {I I' J J' : IntervalBox n}
    (hII' : I ≤ I') (hJJ' : J ≤ J') :
    add p I J ≤ add p I' J' := by
  intro i
  exact Interval.add_mono (hII' i) (hJJ' i)

/-- Negation is monotone. -/
lemma neg_mono {I J : IntervalBox n} (hIJ : I ≤ J) :
    neg I ≤ neg J := by
  intro i
  exact Interval.neg_mono (hIJ i)

/-- Addition is monotone in precision. -/
lemma add_mono_precision_succ (p : Nat) (I J : IntervalBox n) :
    add p I J ≤ add (p + 1) I J := by
  intro i
  exact Interval.add_mono_precision_succ p (I.intervals i) (J.intervals i)

end IntervalBox

end RZ
end Analysis
end HeytingLean
