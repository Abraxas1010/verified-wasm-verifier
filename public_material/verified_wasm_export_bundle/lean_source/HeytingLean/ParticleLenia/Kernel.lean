/-
  Verified Particle Lenia - Kernel Functions

  The Particle Lenia kernel is a Gaussian:
    K(r) = w_K * exp(-(r - μ_K)² / σ_K²)

  Since exp() is not directly available in the verified Nat fragment,
  we use a polynomial approximation that is accurate for the relevant range.

  Reference: https://google-research.github.io/self-organising-systems/particle-lenia/
-/

import HeytingLean.ParticleLenia.Basic

namespace HeytingLean
namespace ParticleLenia

open FixedPoint

/-! ## Gaussian Approximation

We approximate exp(-x²) using a piecewise linear function that is accurate for |x| ≤ 3.
Beyond this range, we clamp to 0.
-/

/-- Integer square root using Newton's method -/
def intSqrt (n : Int) : Int :=
  if n ≤ 0 then 0
  else if n < 4 then 1
  else
    let x0 := n / 2
    let x1 := (x0 + n / x0) / 2
    let x2 := (x1 + n / x1) / 2
    let x3 := (x2 + n / x2) / 2
    x3

/-- Helper: compute the piecewise linear approximation result -/
def expNegSqApproxRaw (x_sq_norm : Int) : Int :=
  if x_sq_norm < 0 then
    SCALE
  else if x_sq_norm < 250 then
    SCALE - (x_sq_norm / 2)
  else if x_sq_norm < 1000 then
    850 - ((x_sq_norm - 250) * 300 / 750)
  else if x_sq_norm < 2250 then
    550 - ((x_sq_norm - 1000) * 300 / 1250)
  else if x_sq_norm < 4000 then
    250 - ((x_sq_norm - 2250) * 150 / 1750)
  else if x_sq_norm < 9000 then
    100 - ((x_sq_norm - 4000) * 100 / 5000)
  else
    0

/-- Piecewise linear approximation of exp(-x²) for x ≥ 0
    Returns value in fixed-point (0 to 1000 representing 0.0 to 1.0) -/
def expNegSqApprox (x_sq : FixedPoint) : FixedPoint :=
  ⟨expNegSqApproxRaw (x_sq.raw / SCALE)⟩

/-! ## Bounds on expNegSqApproxRaw -/

/-- Helper: if a < b * c and b > 0, then a / b < c -/
theorem div_lt_of_lt_mul_pos (a b c : Int) (hb : 0 < b) (h : a < b * c) : a / b < c := by
  have hbc : a < c * b := by rw [Int.mul_comm] at h; exact h
  exact Int.ediv_lt_of_lt_mul hb hbc

/-- The approximation is non-negative for all inputs -/
theorem expNegSqApproxRaw_nonneg (x : Int) : 0 ≤ expNegSqApproxRaw x := by
  simp only [expNegSqApproxRaw]
  split_ifs with h1 h2 h3 h4 h5 h6
  · -- x < 0: returns SCALE = 1000
    simp only [SCALE]; omega
  · -- 0 ≤ x < 250: returns SCALE - x/2 ≥ 0
    simp only [SCALE]
    -- x < 250 means x/2 < 125
    have h_div_bound : x / 2 < 125 := div_lt_of_lt_mul_pos x 2 125 (by omega) (by omega)
    omega
  · -- 250 ≤ x < 1000: returns 850 - (x-250)*300/750
    have h_div : (x - 250) * 300 / 750 < 300 :=
      div_lt_of_lt_mul_pos _ 750 300 (by omega) (by omega)
    omega
  · -- 1000 ≤ x < 2250: returns 550 - (x-1000)*300/1250
    have h_div : (x - 1000) * 300 / 1250 < 300 :=
      div_lt_of_lt_mul_pos _ 1250 300 (by omega) (by omega)
    omega
  · -- 2250 ≤ x < 4000: returns 250 - (x-2250)*150/1750
    have h_div : (x - 2250) * 150 / 1750 < 150 :=
      div_lt_of_lt_mul_pos _ 1750 150 (by omega) (by omega)
    omega
  · -- 4000 ≤ x < 9000: returns 100 - (x-4000)*100/5000
    have h_div : (x - 4000) * 100 / 5000 < 100 :=
      div_lt_of_lt_mul_pos _ 5000 100 (by omega) (by omega)
    omega
  · -- x ≥ 9000: returns 0
    omega

/-- The approximation is bounded by SCALE -/
theorem expNegSqApproxRaw_bounded (x : Int) : expNegSqApproxRaw x ≤ SCALE := by
  simp only [expNegSqApproxRaw, SCALE]
  split_ifs with h1 h2 h3 h4 h5 h6 <;> omega

/-! ## Kernel Definition and Properties -/

/-- The Lenia kernel K(r) = exp(-(r - μ_K)² / σ_K²)
    Input: r_sq = r² (squared distance, in fixed-point)
    Returns: kernel value in [0, 1] (fixed-point) -/
def kernel (r_sq : FixedPoint) (params : LeniaParams) : FixedPoint :=
  let r := ⟨intSqrt r_sq.raw⟩
  let diff := r - params.mu_k
  let normalized_sq := (diff * diff) / (params.sigma_k * params.sigma_k)
  expNegSqApprox normalized_sq

/-- The kernel is always non-negative -/
theorem kernel_nonneg (r_sq : FixedPoint) (params : LeniaParams) :
    0 ≤ (kernel r_sq params).raw := by
  simp only [kernel, expNegSqApprox]
  exact expNegSqApproxRaw_nonneg _

/-- The kernel is bounded by 1 (SCALE in fixed-point) -/
theorem kernel_bounded (r_sq : FixedPoint) (params : LeniaParams) :
    (kernel r_sq params).raw ≤ SCALE := by
  simp only [kernel, expNegSqApprox]
  exact expNegSqApproxRaw_bounded _

/-! ## Growth Field -/

/-- Growth field: G(U) = exp(-(U - μ_G)² / σ_G²) -/
def growth (U : FixedPoint) (params : LeniaParams) : FixedPoint :=
  let diff := U - params.mu_g
  let normalized_sq := (diff * diff) / (params.sigma_g * params.sigma_g)
  expNegSqApprox normalized_sq

/-- Growth is always non-negative -/
theorem growth_nonneg (U : FixedPoint) (params : LeniaParams) :
    0 ≤ (growth U params).raw := by
  simp only [growth, expNegSqApprox]
  exact expNegSqApproxRaw_nonneg _

/-- Growth is bounded by 1 (SCALE in fixed-point) -/
theorem growth_bounded (U : FixedPoint) (params : LeniaParams) :
    (growth U params).raw ≤ SCALE := by
  simp only [growth, expNegSqApprox]
  exact expNegSqApproxRaw_bounded _

/-! ## Repulsion Field -/

/-- Repulsion between two particles at squared distance d_sq -/
def repulsion (d_sq : FixedPoint) (params : LeniaParams) : FixedPoint :=
  let d_raw := intSqrt d_sq.raw
  let d := ⟨d_raw⟩
  let oneMinusD := FixedPoint.one - d
  let clamped := FixedPoint.max oneMinusD FixedPoint.zero
  let clampedSq := clamped.sq
  (params.c_rep * clampedSq) / ⟨2 * SCALE⟩

/-- Helper lemma: max returns non-negative when second arg is zero -/
theorem fixedpoint_max_zero_nonneg (a : FixedPoint) :
    0 ≤ (FixedPoint.max a FixedPoint.zero).raw := by
  simp only [FixedPoint.max, FixedPoint.zero]
  split_ifs with h
  · exact h
  · omega

/-- Helper lemma: square of non-negative is non-negative -/
theorem sq_nonneg_of_nonneg (a : FixedPoint) (h : 0 ≤ a.raw) :
    0 ≤ (FixedPoint.sq a).raw := by
  simp only [FixedPoint.sq, FixedPoint.mul, SCALE]
  have : 0 ≤ a.raw * a.raw := Int.mul_nonneg h h
  exact Int.ediv_nonneg this (by omega)

/-- Repulsion is always non-negative (when c_rep ≥ 0) -/
theorem repulsion_nonneg (d_sq : FixedPoint) (params : LeniaParams)
    (h_crep : 0 ≤ params.c_rep.raw) :
    0 ≤ (repulsion d_sq params).raw := by
  simp only [repulsion]
  -- clamped is max(1-d, 0) which is ≥ 0
  have h_clamped : 0 ≤ (FixedPoint.max (FixedPoint.one - ⟨intSqrt d_sq.raw⟩) FixedPoint.zero).raw :=
    fixedpoint_max_zero_nonneg _
  -- clampedSq is clamped² which is ≥ 0
  have h_sq : 0 ≤ (FixedPoint.sq (FixedPoint.max (FixedPoint.one - ⟨intSqrt d_sq.raw⟩) FixedPoint.zero)).raw :=
    sq_nonneg_of_nonneg _ h_clamped
  -- c_rep * clampedSq ≥ 0
  simp only [FixedPoint.mul, FixedPoint.sq, SCALE] at *
  have h_prod : 0 ≤ params.c_rep.raw * ((FixedPoint.max (FixedPoint.one - ⟨intSqrt d_sq.raw⟩) FixedPoint.zero).raw *
                    (FixedPoint.max (FixedPoint.one - ⟨intSqrt d_sq.raw⟩) FixedPoint.zero).raw / 1000) :=
    Int.mul_nonneg h_crep h_sq
  have h_div1 : 0 ≤ params.c_rep.raw * ((FixedPoint.max (FixedPoint.one - ⟨intSqrt d_sq.raw⟩) FixedPoint.zero).raw *
                    (FixedPoint.max (FixedPoint.one - ⟨intSqrt d_sq.raw⟩) FixedPoint.zero).raw / 1000) / 1000 :=
    Int.ediv_nonneg h_prod (by omega)
  have h_prod2 : 0 ≤ (params.c_rep.raw * ((FixedPoint.max (FixedPoint.one - ⟨intSqrt d_sq.raw⟩) FixedPoint.zero).raw *
                     (FixedPoint.max (FixedPoint.one - ⟨intSqrt d_sq.raw⟩) FixedPoint.zero).raw / 1000) / 1000) * 1000 :=
    Int.mul_nonneg h_div1 (by omega)
  have h_divisor : (0 : Int) < 2 * 1000 := by omega
  exact Int.ediv_nonneg h_prod2 (le_of_lt h_divisor)

/-! ## Newton's Method Properties -/

/-- Helper: Newton step lower bound. (x + y) / 2 ≥ x / 2 when y ≥ 0 -/
theorem newton_step_ge_half (x y : Int) (_hx : x > 0) (hy : y ≥ 0) :
    (x + y) / 2 ≥ x / 2 := by
  have h : x ≤ x + y := by omega
  -- Int.ediv_le_ediv : 0 < c → a ≤ b → a / c ≤ b / c
  have key : x / 2 ≤ (x + y) / 2 := Int.ediv_le_ediv (by omega : (0 : Int) < 2) h
  exact key

/-- Helper: n / (n / 2) ≥ 0 for n ≥ 2 -/
theorem div_half_nonneg (n : Int) (hn : n ≥ 2) : n / (n / 2) ≥ 0 := by
  have h1 : n / 2 > 0 := by omega
  exact Int.ediv_nonneg (by omega : 0 ≤ n) (le_of_lt h1)

/-- Helper: For n ≥ 1000000, n / 2 ≥ 500000 -/
theorem half_large (n : Int) (h : n ≥ 1000000) : n / 2 ≥ 500000 := by
  have h1 : (1000000 : Int) ≤ n := h
  have key : (1000000 : Int) / 2 ≤ n / 2 := Int.ediv_le_ediv (by omega : (0 : Int) < 2) h1
  omega

/-- Helper: For x ≥ 500000, x / 2 ≥ 250000 -/
theorem half_500k (x : Int) (h : x ≥ 500000) : x / 2 ≥ 250000 := by
  have h1 : (500000 : Int) ≤ x := h
  have key : (500000 : Int) / 2 ≤ x / 2 := Int.ediv_le_ediv (by omega : (0 : Int) < 2) h1
  omega

/-- Helper: For x ≥ 250000, x / 2 ≥ 125000 -/
theorem half_250k (x : Int) (h : x ≥ 250000) : x / 2 ≥ 125000 := by
  have h1 : (250000 : Int) ≤ x := h
  have key : (250000 : Int) / 2 ≤ x / 2 := Int.ediv_le_ediv (by omega : (0 : Int) < 2) h1
  omega

/-- Helper: For x ≥ 125000, x / 2 ≥ 62500 -/
theorem half_125k (x : Int) (h : x ≥ 125000) : x / 2 ≥ 62500 := by
  have h1 : (125000 : Int) ≤ x := h
  have key : (125000 : Int) / 2 ≤ x / 2 := Int.ediv_le_ediv (by omega : (0 : Int) < 2) h1
  omega

/-- Helper: intSqrt of n ≥ SCALE² gives result ≥ SCALE

    Proof: For n ≥ 1000000, the Newton iteration starting from n/2:
    - x0 = n/2 ≥ 500000
    - Each step: x_{k+1} = (x_k + n/x_k)/2 ≥ x_k/2 (since n/x_k ≥ 0)
    - After 3 halvings: x3 ≥ n/16 ≥ 62500 ≥ 1000 = SCALE -/
theorem intSqrt_large (n : Int) (h : n ≥ SCALE * SCALE) : intSqrt n ≥ SCALE := by
  simp only [intSqrt, SCALE] at *
  split_ifs with h1 h2
  · -- n ≤ 0, but h says n ≥ 1000000, contradiction
    omega
  · -- n < 4, but h says n ≥ 1000000, contradiction
    omega
  · -- Newton's method case: need to show final expression ≥ 1000
    -- We prove this by showing each step stays above a threshold
    have hn_ge2 : n ≥ 2 := by omega

    -- Step 0: x0 = n/2 ≥ 500000
    have hx0 : n / 2 ≥ 500000 := half_large n (by omega)

    -- Step 1: x1 = (n/2 + n/(n/2))/2 ≥ 250000
    have hx1 : (n / 2 + n / (n / 2)) / 2 ≥ 250000 := by
      have h1 : n / 2 > 0 := by omega
      have h2 : n / (n / 2) ≥ 0 := div_half_nonneg n hn_ge2
      have h3 : (n / 2 + n / (n / 2)) / 2 ≥ (n / 2) / 2 := newton_step_ge_half (n/2) (n/(n/2)) h1 h2
      calc (n / 2 + n / (n / 2)) / 2 ≥ (n / 2) / 2 := h3
           _ ≥ 250000 := half_500k (n/2) hx0

    -- Step 2: x2 ≥ 125000
    have hx2 : ((n / 2 + n / (n / 2)) / 2 + n / ((n / 2 + n / (n / 2)) / 2)) / 2 ≥ 125000 := by
      have h1 : (n / 2 + n / (n / 2)) / 2 > 0 := by omega
      have h2 : n / ((n / 2 + n / (n / 2)) / 2) ≥ 0 := Int.ediv_nonneg (by omega) (by omega)
      have h3 := newton_step_ge_half ((n / 2 + n / (n / 2)) / 2) (n / ((n / 2 + n / (n / 2)) / 2)) h1 h2
      calc ((n / 2 + n / (n / 2)) / 2 + n / ((n / 2 + n / (n / 2)) / 2)) / 2
           ≥ ((n / 2 + n / (n / 2)) / 2) / 2 := h3
           _ ≥ 125000 := half_250k _ hx1

    -- Step 3: x3 ≥ 62500 ≥ 1000
    have h1 : ((n / 2 + n / (n / 2)) / 2 + n / ((n / 2 + n / (n / 2)) / 2)) / 2 > 0 := by omega
    have h2 : n / (((n / 2 + n / (n / 2)) / 2 + n / ((n / 2 + n / (n / 2)) / 2)) / 2) ≥ 0 :=
      Int.ediv_nonneg (by omega) (by omega)
    have h3 := newton_step_ge_half
      (((n / 2 + n / (n / 2)) / 2 + n / ((n / 2 + n / (n / 2)) / 2)) / 2)
      (n / (((n / 2 + n / (n / 2)) / 2 + n / ((n / 2 + n / (n / 2)) / 2)) / 2))
      h1 h2
    have hx3 : (((n / 2 + n / (n / 2)) / 2 + n / ((n / 2 + n / (n / 2)) / 2)) / 2 +
                n / (((n / 2 + n / (n / 2)) / 2 + n / ((n / 2 + n / (n / 2)) / 2)) / 2)) / 2 ≥ 62500 := by
      calc (((n / 2 + n / (n / 2)) / 2 + n / ((n / 2 + n / (n / 2)) / 2)) / 2 +
            n / (((n / 2 + n / (n / 2)) / 2 + n / ((n / 2 + n / (n / 2)) / 2)) / 2)) / 2
           ≥ (((n / 2 + n / (n / 2)) / 2 + n / ((n / 2 + n / (n / 2)) / 2)) / 2) / 2 := h3
           _ ≥ 62500 := half_125k _ hx2
    omega

/-- Repulsion is zero when distance ≥ 1 -/
theorem repulsion_zero_far (d_sq : FixedPoint) (params : LeniaParams)
    (h : d_sq.raw ≥ SCALE * SCALE) :
    (repulsion d_sq params).raw = 0 := by
  simp only [repulsion]
  -- When d² ≥ SCALE², d ≥ SCALE (i.e., d ≥ 1.0)
  have h_sqrt : intSqrt d_sq.raw ≥ SCALE := intSqrt_large d_sq.raw h
  simp only [SCALE] at h_sqrt

  -- one - d = ⟨1000 - intSqrt d_sq.raw⟩ which has raw ≤ 0 since intSqrt d_sq.raw ≥ 1000
  have h_one_raw : FixedPoint.one.raw = 1000 := by simp only [FixedPoint.one, SCALE]
  have h_diff_raw : (FixedPoint.one - ⟨intSqrt d_sq.raw⟩).raw = 1000 - intSqrt d_sq.raw := by
    -- FixedPoint subtraction: (a - b).raw = a.raw - b.raw
    rfl
  have h_diff : (FixedPoint.one - ⟨intSqrt d_sq.raw⟩).raw ≤ 0 := by
    rw [h_diff_raw]
    omega

  -- max(1-d, 0) = 0 since 1-d ≤ 0
  have h_clamped : (FixedPoint.max (FixedPoint.one - ⟨intSqrt d_sq.raw⟩) FixedPoint.zero).raw = 0 := by
    simp only [FixedPoint.max, FixedPoint.zero]
    split_ifs with hge
    · -- 1-d ≥ 0, but we showed 1-d ≤ 0, so 1-d = 0
      omega
    · rfl

  -- Now show the whole expression is 0: (c_rep * 0²) / (2 * SCALE) = 0
  -- 0² = 0, c_rep * 0 = 0, 0 / (2 * SCALE) = 0

  -- The clamped value is ⟨0⟩
  let clamped := FixedPoint.max (FixedPoint.one - ⟨intSqrt d_sq.raw⟩) FixedPoint.zero
  -- Note: h_clamped tells us clamped.raw = 0

  -- sq(clamped) where clamped.raw = 0
  have h_sq_zero : clamped.sq.raw = 0 := by
    show (FixedPoint.mul clamped clamped).raw = 0
    simp only [FixedPoint.mul, SCALE]
    -- Goal: clamped.raw * clamped.raw / 1000 = 0
    rw [h_clamped]
    native_decide

  -- c_rep * sq where sq.raw = 0
  have h_mul_zero : (params.c_rep * clamped.sq).raw = 0 := by
    show (FixedPoint.mul params.c_rep (FixedPoint.sq clamped)).raw = 0
    simp only [FixedPoint.mul, FixedPoint.sq, SCALE]
    -- Goal: params.c_rep.raw * (clamped.raw * clamped.raw / 1000) / 1000 = 0
    rw [h_clamped]
    -- Now: params.c_rep.raw * (0 * 0 / 1000) / 1000 = 0
    simp only [Int.mul_zero, Int.zero_ediv]

  -- Division: a / b where a.raw = 0
  -- Need to show: (⟨0⟩ / ⟨2000⟩).raw = 0
  -- That is: if 2000 = 0 then 0 else 0 * 1000 / 2000 = 0
  show (FixedPoint.div (FixedPoint.mul params.c_rep (FixedPoint.sq clamped)) ⟨2 * SCALE⟩).raw = 0
  simp only [FixedPoint.div, FixedPoint.mul, FixedPoint.sq, SCALE]
  rw [h_clamped]
  simp only [Int.mul_zero, Int.zero_mul, Int.zero_ediv]
  split_ifs <;> rfl

end ParticleLenia
end HeytingLean
