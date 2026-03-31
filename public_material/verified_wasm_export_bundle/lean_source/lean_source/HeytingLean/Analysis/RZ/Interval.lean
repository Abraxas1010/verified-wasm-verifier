import HeytingLean.Analysis.RZ.Dyadic

namespace HeytingLean
namespace Analysis
namespace RZ

/-!
# RZ: dyadic interval arithmetic on `ℚ`

Intervals are represented by rational endpoints with a proof `lo ≤ hi`.

The computational operations (`add`, `sub`, `mulNonneg`) are parameterized by a dyadic
precision `p` and return intervals whose endpoints are dyadic rationals of denominator `2^p`,
obtained by `roundDown` / `roundUp` from `RZ.Dyadic`.

For now we provide a fully proven (sound) multiplication only under a nonnegativity precondition;
this already covers many “exact real” constructions that maintain nonnegative invariants (e.g. `sqrt`).
-/

structure Interval where
  lo : ℚ
  hi : ℚ
  lo_le_hi : lo ≤ hi

namespace Interval

@[ext] lemma ext {I J : Interval} (hlo : I.lo = J.lo) (hhi : I.hi = J.hi) : I = J := by
  cases I; cases J; cases hlo; cases hhi; rfl

instance : Membership ℚ Interval :=
  ⟨fun I x => I.lo ≤ x ∧ x ≤ I.hi⟩

/-- The subset of `ℚ` represented by an interval. -/
def toSet (I : Interval) : Set ℚ := {x | x ∈ I}

@[simp] lemma mem_iff {x : ℚ} {I : Interval} : x ∈ I ↔ I.lo ≤ x ∧ x ≤ I.hi := Iff.rfl

/-- Build an interval from two rationals by sorting endpoints. -/
def make (a b : ℚ) : Interval :=
  { lo := min a b
    hi := max a b
    lo_le_hi := min_le_max }

/-- A degenerate interval `[q,q]`. -/
def ofRat (q : ℚ) : Interval :=
  { lo := q, hi := q, lo_le_hi := le_rfl }

@[simp] lemma mem_ofRat {q x : ℚ} : x ∈ ofRat q ↔ x = q := by
  constructor
  · intro hx
    exact le_antisymm hx.2 hx.1
  · intro hx
    subst hx
    exact ⟨le_rfl, le_rfl⟩

/-- Interval width `hi - lo` (as a rational). -/
def width (I : Interval) : ℚ := I.hi - I.lo

lemma width_nonneg (I : Interval) : 0 ≤ width I := by
  dsimp [width]
  exact sub_nonneg.mpr I.lo_le_hi

/-! ## Information order (reverse inclusion) -/

instance : LE Interval :=
  ⟨fun I J => I.lo ≤ J.lo ∧ J.hi ≤ I.hi⟩

@[simp] lemma le_def {I J : Interval} : I ≤ J ↔ I.lo ≤ J.lo ∧ J.hi ≤ I.hi := Iff.rfl

instance : Preorder Interval where
  le := (· ≤ ·)
  lt := fun I J => I ≤ J ∧ ¬ J ≤ I
  le_refl I := ⟨le_rfl, le_rfl⟩
  le_trans I J K hIJ hJK := by
    refine ⟨le_trans hIJ.1 hJK.1, le_trans hJK.2 hIJ.2⟩

instance : PartialOrder Interval where
  le := (· ≤ ·)
  lt := fun I J => I ≤ J ∧ ¬ J ≤ I
  le_refl I := ⟨le_rfl, le_rfl⟩
  le_trans I J K hIJ hJK := by
    refine ⟨le_trans hIJ.1 hJK.1, le_trans hJK.2 hIJ.2⟩
  le_antisymm I J hIJ hJI := by
    apply Interval.ext
    · exact le_antisymm hIJ.1 hJI.1
    · exact le_antisymm hJI.2 hIJ.2

lemma le_iff_subset {I J : Interval} : I ≤ J ↔ J.toSet ⊆ I.toSet := by
  constructor
  · intro hIJ x hx
    have hxJ : x ∈ J := hx
    refine ⟨?_, ?_⟩
    · exact le_trans hIJ.1 hxJ.1
    · exact le_trans hxJ.2 hIJ.2
  · intro hsub
    have hlo : I.lo ≤ J.lo := by
      have : J.lo ∈ J := ⟨le_rfl, J.lo_le_hi⟩
      have : J.lo ∈ I := hsub this
      exact this.1
    have hhi : J.hi ≤ I.hi := by
      have : J.hi ∈ J := ⟨J.lo_le_hi, le_rfl⟩
      have : J.hi ∈ I := hsub this
      exact this.2
    exact ⟨hlo, hhi⟩

/-! ## Dyadic-rounded arithmetic -/

open HeytingLean.Analysis.RZ

/-- Dyadic-rounded addition: sound bounds on `x+y`. -/
def add (p : Nat) (I J : Interval) : Interval :=
  { lo := roundDown p (I.lo + J.lo)
    hi := roundUp p (I.hi + J.hi)
    lo_le_hi := by
      have h1 : roundDown p (I.lo + J.lo) ≤ I.lo + J.lo := roundDown_le p _
      have h2 : I.lo + J.lo ≤ I.hi + J.hi := add_le_add I.lo_le_hi J.lo_le_hi
      have h3 : I.hi + J.hi ≤ roundUp p (I.hi + J.hi) := le_roundUp p _
      exact le_trans (le_trans h1 h2) h3 }

/-- Negation (exact on endpoints). -/
def neg (I : Interval) : Interval :=
  { lo := -I.hi
    hi := -I.lo
    lo_le_hi := by
      have : I.lo ≤ I.hi := I.lo_le_hi
      exact neg_le_neg this }

/-- Negation preserves width. -/
lemma width_neg (I : Interval) : width (neg I) = width I := by
  dsimp [width, neg]
  ring_nf

/-- Negation is monotone w.r.t. the reverse-inclusion order. -/
lemma neg_mono {I J : Interval} (hIJ : I ≤ J) : neg I ≤ neg J := by
  constructor
  · -- lows
    exact neg_le_neg hIJ.2
  · -- highs
    exact neg_le_neg hIJ.1

/-- Dyadic-rounded subtraction: `I - J := I + (-J)`. -/
def sub (p : Nat) (I J : Interval) : Interval :=
  add p I (neg J)

lemma mem_add {p : Nat} {I J : Interval} {x y : ℚ} (hx : x ∈ I) (hy : y ∈ J) :
    x + y ∈ add p I J := by
  constructor
  · -- lower bound
    have hlow : roundDown p (I.lo + J.lo) ≤ I.lo + J.lo := roundDown_le p _
    have hsum : I.lo + J.lo ≤ x + y := add_le_add hx.1 hy.1
    exact le_trans hlow hsum
  · -- upper bound
    have hsum : x + y ≤ I.hi + J.hi := add_le_add hx.2 hy.2
    have hhi : I.hi + J.hi ≤ roundUp p (I.hi + J.hi) := le_roundUp p _
    exact le_trans hsum hhi

lemma add_mono {p : Nat} {I I' J J' : Interval} (hII' : I ≤ I') (hJJ' : J ≤ J') :
    add p I J ≤ add p I' J' := by
  -- show: add p I J ≤ add p I' J'
  constructor
  · -- lower endpoint increases with information
    have hsum : I.lo + J.lo ≤ I'.lo + J'.lo := add_le_add hII'.1 hJJ'.1
    exact roundDown_mono p hsum
  · -- upper endpoint decreases with information
    have hsum : I'.hi + J'.hi ≤ I.hi + J.hi := add_le_add hII'.2 hJJ'.2
    exact roundUp_mono p hsum

lemma add_mono_precision_succ (p : Nat) (I J : Interval) : add p I J ≤ add (p + 1) I J := by
  constructor
  · exact roundDown_le_succ p (I.lo + J.lo)
  · exact roundUp_succ_le p (I.hi + J.hi)

lemma width_add_le (p : Nat) (I J : Interval) :
    width (add p I J) ≤ width I + width J + 2 / pow2 p := by
  -- abbreviate ε = 1/2^p
  let ε : ℚ := 1 / pow2 p
  have hHi : roundUp p (I.hi + J.hi) ≤ (I.hi + J.hi) + ε := by
    simpa [ε, add_comm, add_left_comm, add_assoc] using roundUp_le_add_one_div_pow2 p (I.hi + J.hi)
  have hLo : (I.lo + J.lo) - ε ≤ roundDown p (I.lo + J.lo) := by
    simpa [ε, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      sub_one_div_pow2_le_roundDown p (I.lo + J.lo)
  have hSub :
      roundUp p (I.hi + J.hi) - roundDown p (I.lo + J.lo)
        ≤ ((I.hi + J.hi) + ε) - ((I.lo + J.lo) - ε) :=
    sub_le_sub hHi hLo
  have hRhs :
      ((I.hi + J.hi) + ε) - ((I.lo + J.lo) - ε) = width I + width J + 2 / pow2 p := by
    dsimp [ε, width]
    ring_nf
  -- close
  simpa [width, add, hRhs] using hSub

/-! ## Multiplication under a nonnegativity invariant -/

def IsNonneg (I : Interval) : Prop := 0 ≤ I.lo

lemma nonneg_hi {I : Interval} (hI : IsNonneg I) : 0 ≤ I.hi :=
  le_trans hI I.lo_le_hi

/-- Dyadic-rounded multiplication for nonnegative intervals. -/
def mulNonneg (p : Nat) (I J : Interval) (hI : IsNonneg I) (hJ : IsNonneg J) : Interval :=
  { lo := roundDown p (I.lo * J.lo)
    hi := roundUp p (I.hi * J.hi)
    lo_le_hi := by
      have h1 : roundDown p (I.lo * J.lo) ≤ I.lo * J.lo := roundDown_le p _
      have h2 : I.lo * J.lo ≤ I.hi * J.hi := by
        have hIhi : 0 ≤ I.hi := nonneg_hi hI
        exact mul_le_mul I.lo_le_hi J.lo_le_hi hJ hIhi
      have h3 : I.hi * J.hi ≤ roundUp p (I.hi * J.hi) := le_roundUp p _
      exact le_trans (le_trans h1 h2) h3 }

lemma mem_mulNonneg
    {p : Nat} {I J : Interval} (hI : IsNonneg I) (hJ : IsNonneg J)
    {x y : ℚ} (hx : x ∈ I) (hy : y ∈ J) :
    x * y ∈ mulNonneg p I J hI hJ := by
  constructor
  · -- lower bound
    have hlow : roundDown p (I.lo * J.lo) ≤ I.lo * J.lo := roundDown_le p _
    have hx0 : 0 ≤ x := le_trans hI hx.1
    have hxy : I.lo * J.lo ≤ x * y := by
      exact mul_le_mul hx.1 hy.1 hJ hx0
    exact le_trans hlow hxy
  · -- upper bound
    have hy0 : 0 ≤ y := le_trans hJ hy.1
    have hIhi : 0 ≤ I.hi := nonneg_hi hI
    have hxy : x * y ≤ I.hi * J.hi := by
      exact mul_le_mul hx.2 hy.2 hy0 hIhi
    have hhi : I.hi * J.hi ≤ roundUp p (I.hi * J.hi) := le_roundUp p _
    exact le_trans hxy hhi

lemma mulNonneg_mono_precision_succ (p : Nat) (I J : Interval) (hI : IsNonneg I) (hJ : IsNonneg J) :
    mulNonneg p I J hI hJ ≤ mulNonneg (p + 1) I J hI hJ := by
  constructor
  · exact roundDown_le_succ p (I.lo * J.lo)
  · exact roundUp_succ_le p (I.hi * J.hi)

lemma width_mulNonneg_le (p : Nat) (I J : Interval) (hI : IsNonneg I) (hJ : IsNonneg J) :
    width (mulNonneg p I J hI hJ) ≤ width I * J.hi + I.hi * width J + 2 / pow2 p := by
  let ε : ℚ := 1 / pow2 p
  have hHi : roundUp p (I.hi * J.hi) ≤ (I.hi * J.hi) + ε := by
    simpa [ε, add_comm, add_left_comm, add_assoc] using roundUp_le_add_one_div_pow2 p (I.hi * J.hi)
  have hLo : (I.lo * J.lo) - ε ≤ roundDown p (I.lo * J.lo) := by
    simpa [ε, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      sub_one_div_pow2_le_roundDown p (I.lo * J.lo)
  have hSub :
      roundUp p (I.hi * J.hi) - roundDown p (I.lo * J.lo)
        ≤ ((I.hi * J.hi) + ε) - ((I.lo * J.lo) - ε) :=
    sub_le_sub hHi hLo
  have hDecomp :
      I.hi * J.hi - I.lo * J.lo ≤ width I * J.hi + I.hi * width J := by
    have hdiffJ : 0 ≤ J.hi - J.lo := sub_nonneg.mpr J.lo_le_hi
    have hmulI : I.lo * (J.hi - J.lo) ≤ I.hi * (J.hi - J.lo) :=
      mul_le_mul_of_nonneg_right I.lo_le_hi hdiffJ
    have hadd :
        (I.hi - I.lo) * J.hi + I.lo * (J.hi - J.lo)
          ≤ (I.hi - I.lo) * J.hi + I.hi * (J.hi - J.lo) :=
      add_le_add_left hmulI ((I.hi - I.lo) * J.hi)
    -- combine with an algebraic decomposition
    calc
      I.hi * J.hi - I.lo * J.lo
          = (I.hi - I.lo) * J.hi + I.lo * (J.hi - J.lo) := by ring_nf
      _ ≤ (I.hi - I.lo) * J.hi + I.hi * (J.hi - J.lo) := hadd
      _ = width I * J.hi + I.hi * width J := by
          dsimp [width]
  -- close
  have hRhsEq :
      ((I.hi * J.hi) + ε) - ((I.lo * J.lo) - ε)
        = (I.hi * J.hi - I.lo * J.lo) + 2 / pow2 p := by
    dsimp [ε]
    ring_nf
  -- start from `hSub`, rewrite, then apply `hDecomp`
  have : roundUp p (I.hi * J.hi) - roundDown p (I.lo * J.lo)
        ≤ (I.hi * J.hi - I.lo * J.lo) + 2 / pow2 p := by
    simpa [hRhsEq] using hSub
  -- now apply `hDecomp`
  have : roundUp p (I.hi * J.hi) - roundDown p (I.lo * J.lo)
        ≤ (width I * J.hi + I.hi * width J) + 2 / pow2 p :=
    le_trans this (add_le_add_right hDecomp _)
  simpa [width, mulNonneg] using this

end Interval

end RZ
end Analysis
end HeytingLean
