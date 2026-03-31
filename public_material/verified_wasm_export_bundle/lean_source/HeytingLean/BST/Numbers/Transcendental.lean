import HeytingLean.BST.Numbers.Real

/-!
# BST.Numbers.Transcendental

Computable bounded transcendental approximations over rationals, with explicit
truncation parameters.
-/

namespace HeytingLean.BST

namespace BoundedTranscendental

def factorial : ℕ → Rat
  | 0 => 1
  | n + 1 => (n + 1 : Rat) * factorial n

def expCore (x : Rat) : ℕ → Rat
  | 0 => 0
  | n + 1 => expCore x n + x ^ n / factorial n

def lnUnitCore (u : Rat) : ℕ → Rat
  | 0 => 0
  | n + 1 => lnUnitCore u n + u ^ (n + 1) / (n + 1 : Rat)

def lnAroundOneCore (u : Rat) : ℕ → Rat
  | 0 => 0
  | n + 1 => lnAroundOneCore u n + ((-1 : Rat) ^ n) * u ^ (n + 1) / (n + 1 : Rat)

def sinCore (x : Rat) : ℕ → Rat
  | 0 => 0
  | n + 1 => sinCore x n + ((-1 : Rat) ^ n) * x ^ (2 * n + 1) / factorial (2 * n + 1)

def cosCore (x : Rat) : ℕ → Rat
  | 0 => 0
  | n + 1 => cosCore x n + ((-1 : Rat) ^ n) * x ^ (2 * n) / factorial (2 * n)

/-- Positive bounded exponential approximation.
For negative inputs we use the reciprocal positive-series branch to preserve
strict positivity of partition weights. -/
def boundedExp (x : Rat) (terms : ℕ) : Rat :=
  if x < 0 then
    if terms = 0 then 0 else 1 / expCore (-x) terms
  else
    expCore x terms

/-- Bounded natural logarithm.
On `(0, 1]` we use `ln q = -Σ (1-q)^n / n`, which keeps the sign discipline
needed for entropy proofs. For `q > 1` we use the alternating expansion around `1`. -/
def boundedLn (q : Rat) (terms : ℕ) : Rat :=
  if q ≤ 0 then 0
  else if q ≤ 1 then -(lnUnitCore (1 - q) terms)
  else lnAroundOneCore (q - 1) terms

def boundedSin (x : Rat) (terms : ℕ) : Rat :=
  sinCore x terms

def boundedCos (x : Rat) (terms : ℕ) : Rat :=
  cosCore x terms

def roundedExp (k : ℕ) (hk : 0 < k) (x : RealB k) (terms : ℕ) : RealB k :=
  RealB.round hk (boundedExp (RealB.toRat hk x) terms)

def roundedSin (k : ℕ) (hk : 0 < k) (x : RealB k) (terms : ℕ) : RealB k :=
  RealB.round hk (boundedSin (RealB.toRat hk x) terms)

def roundedCos (k : ℕ) (hk : 0 < k) (x : RealB k) (terms : ℕ) : RealB k :=
  RealB.round hk (boundedCos (RealB.toRat hk x) terms)

theorem factorial_pos (n : ℕ) : 0 < factorial n := by
  induction n with
  | zero =>
      simp [factorial]
  | succ n ih =>
      simp [factorial, ih]
      positivity

theorem expCore_nonneg {x : Rat} (hx : 0 ≤ x) : ∀ terms, 0 ≤ expCore x terms
  | 0 => by simp [expCore]
  | n + 1 => by
      simp [expCore]
      have hpow : 0 ≤ x ^ n := pow_nonneg hx _
      have hdiv : 0 ≤ x ^ n / factorial n := by
        exact div_nonneg hpow (le_of_lt (factorial_pos n))
      exact add_nonneg (expCore_nonneg hx n) hdiv

theorem expCore_pos {x : Rat} (hx : 0 ≤ x) : ∀ terms, 0 < terms → 0 < expCore x terms
  | 0, h => by cases Nat.not_lt_zero _ h
  | 1, _ => by
      simp [expCore, factorial]
  | n + 2, _ => by
      have hprev : 0 < expCore x (n + 1) := expCore_pos hx (n + 1) (Nat.succ_pos _)
      have hpow : 0 ≤ x ^ (n + 1) := pow_nonneg hx _
      have hdiv : 0 ≤ x ^ (n + 1) / factorial (n + 1) := by
        exact div_nonneg hpow (le_of_lt (factorial_pos _))
      simp [expCore]
      exact add_pos_of_pos_of_nonneg hprev hdiv

theorem expCore_zero_succ : ∀ n, expCore 0 (n + 1) = 1
  | 0 => by simp [expCore, factorial]
  | n + 1 => by
      simpa [expCore, factorial] using expCore_zero_succ n

theorem expCore_zero_pos : ∀ terms, 0 < terms → expCore 0 terms = 1
  | 0, h => by cases Nat.not_lt_zero _ h
  | n + 1, _ => expCore_zero_succ n

theorem expCore_zero (terms : ℕ) :
    expCore 0 terms = if terms = 0 then 0 else 1 := by
  by_cases h : terms = 0
  · simp [h, expCore]
  · simp [h, expCore_zero_pos terms (Nat.pos_iff_ne_zero.mpr h)]

theorem lnUnitCore_nonneg {u : Rat} (hu : 0 ≤ u) : ∀ terms, 0 ≤ lnUnitCore u terms
  | 0 => by simp [lnUnitCore]
  | n + 1 => by
      simp [lnUnitCore]
      have hpow : 0 ≤ u ^ (n + 1) := pow_nonneg hu _
      have hdiv : 0 ≤ u ^ (n + 1) / (n + 1 : Rat) := by
        positivity
      exact add_nonneg (lnUnitCore_nonneg hu n) hdiv

theorem lnUnitCore_zero (terms : ℕ) : lnUnitCore 0 terms = 0 := by
  induction terms with
  | zero =>
      simp [lnUnitCore]
  | succ n ih =>
      simp [lnUnitCore, ih]

theorem sinCore_zero (terms : ℕ) : sinCore 0 terms = 0 := by
  induction terms with
  | zero =>
      simp [sinCore]
  | succ n ih =>
      simp [sinCore, ih]

theorem cosCore_zero_succ : ∀ n, cosCore 0 (n + 1) = 1
  | 0 => by simp [cosCore, factorial]
  | n + 1 => by
      simpa [cosCore, factorial] using cosCore_zero_succ n

theorem cosCore_zero_pos : ∀ terms, 0 < terms → cosCore 0 terms = 1
  | 0, h => by cases Nat.not_lt_zero _ h
  | n + 1, _ => cosCore_zero_succ n

theorem cosCore_zero (terms : ℕ) :
    cosCore 0 terms = if terms = 0 then 0 else 1 := by
  by_cases h : terms = 0
  · simp [h, cosCore]
  · simp [h, cosCore_zero_pos terms (Nat.pos_iff_ne_zero.mpr h)]

theorem boundedExp_pos (x : Rat) (terms : ℕ) (ht : 0 < terms) :
    0 < boundedExp x terms := by
  unfold boundedExp
  by_cases hx : x < 0
  · rw [if_pos hx, if_neg (Nat.ne_of_gt ht)]
    have hcore : 0 < expCore (-x) terms := by
      apply expCore_pos
      linarith
      exact ht
    exact one_div_pos.mpr hcore
  · rw [if_neg hx]
    apply expCore_pos
    linarith
    exact ht

theorem boundedExp_zero (terms : ℕ) (ht : 0 < terms) :
    boundedExp 0 terms = 1 := by
  unfold boundedExp
  rw [if_neg (by norm_num)]
  simpa [ht.ne'] using expCore_zero terms

theorem boundedLn_one (terms : ℕ) :
    boundedLn 1 terms = 0 := by
  unfold boundedLn
  simp [lnUnitCore_zero]

theorem boundedLn_nonpos_of_pos_le_one {q : Rat} (hq0 : 0 < q) (hq1 : q ≤ 1) (terms : ℕ) :
    boundedLn q terms ≤ 0 := by
  unfold boundedLn
  rw [if_neg (by linarith), if_pos hq1]
  exact neg_nonpos.mpr (lnUnitCore_nonneg (by linarith) terms)

theorem boundedSin_zero (terms : ℕ) :
    boundedSin 0 terms = 0 := by
  simpa [boundedSin] using sinCore_zero terms

theorem boundedCos_zero (terms : ℕ) (ht : 0 < terms) :
    boundedCos 0 terms = 1 := by
  simpa [boundedCos, ht.ne'] using cosCore_zero terms

end BoundedTranscendental

end HeytingLean.BST
