import HeytingLean.Eigen.BEACONS.CompositionBound

namespace HeytingLean
namespace Eigen
namespace BEACONS

/-!
Lightweight IEEE-754 audit interface.

`floatApprox ulp exact rounded` means the rounded implementation stays within
`ulp` of the exact real-valued expression.

`floatApproxULP atol maxUlps ulp exact rounded` mirrors the runtime audit used
by `ml/eigenlearner/symbolic_audit.py`, where the denominator is stabilized as
`max atol ulp`, and the normalized error budget is `maxUlps * max atol ulp`.
-/

def floatApprox (ulp exact rounded : ℝ) : Prop := |exact - rounded| ≤ ulp

def ulpScale (atol ulp : ℝ) : ℝ := max atol ulp

def ulpBudget (atol maxUlps ulp : ℝ) : ℝ :=
  maxUlps * ulpScale atol ulp

def floatApproxULP (atol maxUlps ulp exact rounded : ℝ) : Prop :=
  |exact - rounded| ≤ ulpBudget atol maxUlps ulp

inductive IEEERoundingMode where
  | nearestEven
  | towardZero
  | towardPosInf
  | towardNegInf
deriving Repr, DecidableEq

def modeUlps : IEEERoundingMode → ℝ
  | .nearestEven => 1
  | .towardZero => 2
  | .towardPosInf => 2
  | .towardNegInf => 2

def modeOutputBudget (mode : IEEERoundingMode) (atol ulp : ℝ) : ℝ :=
  modeUlps mode * ulpScale atol ulp

structure IEEEAuditAdapter where
  round : IEEERoundingMode → ℝ → ℝ
  ulp : ℝ → ℝ
  ulp_nonneg : ∀ x, 0 ≤ ulp x
  round_sound : ∀ mode atol x, floatApprox (modeOutputBudget mode atol (ulp x)) x (round mode x)

structure IEEEBitPreciseAdapter extends IEEEAuditAdapter where
  Word : Type
  encode : ℝ → Word
  decode : Word → ℝ
  roundWord : IEEERoundingMode → Word → Word
  ulpWord : Word → ℝ
  ulpWord_nonneg : ∀ w, 0 ≤ ulpWord w
  round_decode_sound : ∀ mode x, round mode x = decode (roundWord mode (encode x))
  ulp_decode_sound : ∀ x, ulp x = ulpWord (encode x)

theorem IEEEBitPreciseAdapter.ulp_nonneg_from_word
    (a : IEEEBitPreciseAdapter) (x : ℝ) :
    0 ≤ a.ulp x := by
  rw [a.ulp_decode_sound x]
  exact a.ulpWord_nonneg (a.encode x)

theorem floatApprox_nonneg
    {ulp exact rounded : ℝ}
    (h : floatApprox ulp exact rounded) :
    0 ≤ ulp := by
  unfold floatApprox at h
  exact le_trans (abs_nonneg _) h

theorem floatApprox_add
    {ulp₁ ulp₂ x₁ x₂ y₁ y₂ : ℝ}
    (h₁ : floatApprox ulp₁ x₁ y₁)
    (h₂ : floatApprox ulp₂ x₂ y₂) :
    floatApprox (ulp₁ + ulp₂) (x₁ + x₂) (y₁ + y₂) := by
  unfold floatApprox at *
  calc
    |(x₁ + x₂) - (y₁ + y₂)|
        ≤ |(x₁ + x₂) - (y₁ + x₂)| + |(y₁ + x₂) - (y₁ + y₂)| := by
          exact abs_sub_le _ _ _
    _ = |x₁ - y₁| + |x₂ - y₂| := by ring_nf
    _ ≤ ulp₁ + ulp₂ := add_le_add h₁ h₂

theorem ulpScale_nonneg
    {atol ulp : ℝ}
    (hUlp : 0 ≤ ulp) :
    0 ≤ ulpScale atol ulp := by
  unfold ulpScale
  exact le_trans hUlp (le_max_right _ _)

theorem modeUlps_nonneg (mode : IEEERoundingMode) : 0 ≤ modeUlps mode := by
  cases mode <;> simp [modeUlps]

theorem one_le_modeUlps (mode : IEEERoundingMode) : 1 ≤ modeUlps mode := by
  cases mode <;> simp [modeUlps]

theorem modeOutputBudget_nonneg
    (mode : IEEERoundingMode) {atol ulp : ℝ}
    (hUlp : 0 ≤ ulp) :
    0 ≤ modeOutputBudget mode atol ulp := by
  unfold modeOutputBudget
  exact mul_nonneg (modeUlps_nonneg mode) (ulpScale_nonneg hUlp)

theorem floatApproxULP_of_floatApprox
    {atol maxUlps ulp exact rounded : ℝ}
    (hApprox : floatApprox ulp exact rounded)
    (hMaxUlps : 1 ≤ maxUlps) :
    floatApproxULP atol maxUlps ulp exact rounded := by
  unfold floatApprox floatApproxULP ulpBudget ulpScale at *
  have hUlpNonneg : 0 ≤ ulp := floatApprox_nonneg hApprox
  have hScaleNonneg : 0 ≤ max atol ulp := le_trans hUlpNonneg (le_max_right _ _)
  have hBase : |exact - rounded| ≤ max atol ulp :=
    le_trans hApprox (le_max_right _ _)
  have hLift : max atol ulp ≤ maxUlps * (max atol ulp) := by
    have h := mul_le_mul_of_nonneg_right hMaxUlps hScaleNonneg
    simpa using h
  exact hBase.trans hLift

theorem floatApproxULP_mode_of_floatApprox
    {mode : IEEERoundingMode} {atol ulp exact rounded : ℝ}
    (hApprox : floatApprox ulp exact rounded) :
    floatApproxULP atol (modeUlps mode) ulp exact rounded := by
  exact floatApproxULP_of_floatApprox hApprox (one_le_modeUlps mode)

theorem floatApprox_of_floatApproxULP
    {atol maxUlps ulp exact rounded : ℝ}
    (h : floatApproxULP atol maxUlps ulp exact rounded) :
    floatApprox (ulpBudget atol maxUlps ulp) exact rounded := by
  simpa [floatApprox, floatApproxULP] using h

theorem floatApproxULP_add
    {atol₁ atol₂ maxUlps₁ maxUlps₂ ulp₁ ulp₂ x₁ x₂ y₁ y₂ : ℝ}
    (h₁ : floatApproxULP atol₁ maxUlps₁ ulp₁ x₁ y₁)
    (h₂ : floatApproxULP atol₂ maxUlps₂ ulp₂ x₂ y₂) :
    floatApprox
      (ulpBudget atol₁ maxUlps₁ ulp₁ + ulpBudget atol₂ maxUlps₂ ulp₂)
      (x₁ + x₂) (y₁ + y₂) := by
  exact floatApprox_add (floatApprox_of_floatApproxULP h₁) (floatApprox_of_floatApproxULP h₂)

theorem floatApprox_compose_lipschitz
    {f fHat g gHat : ℝ → ℝ} {εf εg L : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hOuterErr : ∀ x, |f x - fHat x| ≤ εf)
    (hOuterLip : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (hInnerErr : ∀ x, |g x - gHat x| ≤ εg) :
    ∀ x, floatApprox (εf + L * εg) (f (g x)) (fHat (gHat x)) := by
  intro x
  unfold floatApprox
  exact latent_composition_error hL_nonneg hOuterErr hOuterLip hInnerErr x

theorem floatApprox_compose_lipschitz_ulp
    {f fHat g gHat : ℝ → ℝ} {εf εg L atol maxUlps : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hOuterErr : ∀ x, |f x - fHat x| ≤ εf)
    (hOuterLip : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (hInnerErr : ∀ x, |g x - gHat x| ≤ εg)
    (hMaxUlps : 1 ≤ maxUlps) :
    ∀ x, floatApproxULP atol maxUlps (εf + L * εg) (f (g x)) (fHat (gHat x)) := by
  intro x
  exact floatApproxULP_of_floatApprox
    (floatApprox_compose_lipschitz hL_nonneg hOuterErr hOuterLip hInnerErr x)
    hMaxUlps

theorem floatApprox_mul
    {ux uy x xHat y yHat AxHat By : ℝ}
    (hx : floatApprox ux x xHat)
    (hy : floatApprox uy y yHat)
    (hYBound : |y| ≤ By)
    (hXHatBound : |xHat| ≤ AxHat) :
    floatApprox (ux * By + AxHat * uy) (x * y) (xHat * yHat) := by
  unfold floatApprox at *
  have hUxNonneg : 0 ≤ ux := floatApprox_nonneg hx
  have hAxHatNonneg : 0 ≤ AxHat := le_trans (abs_nonneg xHat) hXHatBound
  have h1 : |x - xHat| * |y| ≤ ux * By := by
    exact mul_le_mul hx hYBound (abs_nonneg y) hUxNonneg
  have h2 : |xHat| * |y - yHat| ≤ AxHat * uy := by
    exact mul_le_mul hXHatBound hy (abs_nonneg (y - yHat)) hAxHatNonneg
  have hDecomp : x * y - xHat * yHat = (x - xHat) * y + xHat * (y - yHat) := by
    ring
  calc
    |x * y - xHat * yHat|
        = |(x - xHat) * y + xHat * (y - yHat)| := by simp [hDecomp]
    _ ≤ |(x - xHat) * y| + |xHat * (y - yHat)| := by
          simpa using abs_add_le ((x - xHat) * y) (xHat * (y - yHat))
    _ = |x - xHat| * |y| + |xHat| * |y - yHat| := by
          simp [abs_mul]
    _ ≤ ux * By + AxHat * uy := add_le_add h1 h2

theorem floatApprox_div_const_right
    {u x xHat y : ℝ}
    (hx : floatApprox u x xHat)
    (hy : y ≠ 0) :
    floatApprox (u / |y|) (x / y) (xHat / y) := by
  unfold floatApprox at *
  have hDecomp : x / y - xHat / y = (x - xHat) / y := by
    field_simp [hy]
  calc
    |x / y - xHat / y|
        = |(x - xHat) / y| := by simp [hDecomp]
    _ = |x - xHat| / |y| := by simp [abs_div]
    _ ≤ u / |y| := by
          exact div_le_div_of_nonneg_right hx (abs_nonneg y)

theorem floatApprox_div_rounded_right
    {ux uy x xHat y yHat AxHat denFloor : ℝ}
    (hx : floatApprox ux x xHat)
    (hy : floatApprox uy y yHat)
    (hXHatBound : |xHat| ≤ AxHat)
    (hDenFloorPos : 0 < denFloor)
    (hYFloor : denFloor ≤ |y|)
    (hYHatFloor : denFloor ≤ |yHat|) :
    floatApprox
      (ux / denFloor + AxHat * uy / (denFloor * denFloor))
      (x / y) (xHat / yHat) := by
  unfold floatApprox at *
  have hUxNonneg : 0 ≤ ux := floatApprox_nonneg hx
  have hUyNonneg : 0 ≤ uy := floatApprox_nonneg hy
  have hAxHatNonneg : 0 ≤ AxHat := le_trans (abs_nonneg xHat) hXHatBound
  have hYPos : 0 < |y| := lt_of_lt_of_le hDenFloorPos hYFloor
  have hYHatPos : 0 < |yHat| := lt_of_lt_of_le hDenFloorPos hYHatFloor
  have hyNe : y ≠ 0 := by exact abs_pos.mp hYPos
  have hyHatNe : yHat ≠ 0 := by exact abs_pos.mp hYHatPos
  have hInvY : 1 / |y| ≤ 1 / denFloor := by
    exact one_div_le_one_div_of_le hDenFloorPos hYFloor
  have hTerm1 : |(x - xHat) / y| ≤ ux / denFloor := by
    calc
      |(x - xHat) / y|
          = |x - xHat| / |y| := by simp [abs_div]
      _ = |x - xHat| * (1 / |y|) := by ring
      _ ≤ ux * (1 / denFloor) := by
            exact mul_le_mul hx hInvY (by positivity) hUxNonneg
      _ = ux / denFloor := by ring
  have hTerm2Num : |xHat| * |yHat - y| ≤ AxHat * uy := by
    have hySwap : |yHat - y| = |y - yHat| := by simp [abs_sub_comm]
    have hyBound : |yHat - y| ≤ uy := by simpa [hySwap] using hy
    exact mul_le_mul hXHatBound hyBound (abs_nonneg (yHat - y)) hAxHatNonneg
  have hDenProdLower : denFloor * denFloor ≤ |y| * |yHat| := by
    exact mul_le_mul hYFloor hYHatFloor (by positivity) (abs_nonneg y)
  have hDenSqPos : 0 < denFloor * denFloor := by positivity
  have hInvDen : 1 / (|y| * |yHat|) ≤ 1 / (denFloor * denFloor) := by
    exact one_div_le_one_div_of_le hDenSqPos hDenProdLower
  have hTerm2 : |xHat * (yHat - y) / (y * yHat)| ≤ AxHat * uy / (denFloor * denFloor) := by
    calc
      |xHat * (yHat - y) / (y * yHat)|
          = (|xHat| * |yHat - y|) / (|y| * |yHat|) := by
              simp [abs_div, abs_mul]
      _ = (|xHat| * |yHat - y|) * (1 / (|y| * |yHat|)) := by ring
      _ ≤ (AxHat * uy) * (1 / (denFloor * denFloor)) := by
            exact mul_le_mul hTerm2Num hInvDen (by positivity) (mul_nonneg hAxHatNonneg hUyNonneg)
      _ = AxHat * uy / (denFloor * denFloor) := by ring
  have hDecomp : x / y - xHat / yHat = (x - xHat) / y + xHat * (yHat - y) / (y * yHat) := by
    field_simp [hyNe, hyHatNe]
    ring
  calc
    |x / y - xHat / yHat|
        = |(x - xHat) / y + xHat * (yHat - y) / (y * yHat)| := by simp [hDecomp]
    _ ≤ |(x - xHat) / y| + |xHat * (yHat - y) / (y * yHat)| := by
          simpa using abs_add_le ((x - xHat) / y) (xHat * (yHat - y) / (y * yHat))
    _ ≤ ux / denFloor + AxHat * uy / (denFloor * denFloor) :=
          add_le_add hTerm1 hTerm2

theorem floatApprox_div_rounded_right_output
    {ux uy x xHat y yHat AxHat denFloor uOut zRounded : ℝ}
    (hx : floatApprox ux x xHat)
    (hy : floatApprox uy y yHat)
    (hXHatBound : |xHat| ≤ AxHat)
    (hDenFloorPos : 0 < denFloor)
    (hYFloor : denFloor ≤ |y|)
    (hYHatFloor : denFloor ≤ |yHat|)
    (hOut : floatApprox uOut (xHat / yHat) zRounded) :
    floatApprox
      (ux / denFloor + AxHat * uy / (denFloor * denFloor) + uOut)
      (x / y) zRounded := by
  have hBase :
      floatApprox
        (ux / denFloor + AxHat * uy / (denFloor * denFloor))
        (x / y) (xHat / yHat) :=
    floatApprox_div_rounded_right hx hy hXHatBound hDenFloorPos hYFloor hYHatFloor
  unfold floatApprox at *
  calc
    |x / y - zRounded|
        ≤ |x / y - xHat / yHat| + |xHat / yHat - zRounded| := by
            exact abs_sub_le _ _ _
    _ ≤ (ux / denFloor + AxHat * uy / (denFloor * denFloor)) + uOut :=
          add_le_add hBase hOut
    _ = ux / denFloor + AxHat * uy / (denFloor * denFloor) + uOut := by ring

theorem floatApproxULP_div_rounded_right_output
    {ux uy x xHat y yHat AxHat denFloor uOut zRounded atol maxUlps : ℝ}
    (hx : floatApprox ux x xHat)
    (hy : floatApprox uy y yHat)
    (hXHatBound : |xHat| ≤ AxHat)
    (hDenFloorPos : 0 < denFloor)
    (hYFloor : denFloor ≤ |y|)
    (hYHatFloor : denFloor ≤ |yHat|)
    (hOut : floatApprox uOut (xHat / yHat) zRounded)
    (hMaxUlps : 1 ≤ maxUlps) :
    floatApproxULP atol maxUlps
      (ux / denFloor + AxHat * uy / (denFloor * denFloor) + uOut)
      (x / y) zRounded := by
  exact floatApproxULP_of_floatApprox
    (floatApprox_div_rounded_right_output
      hx hy hXHatBound hDenFloorPos hYFloor hYHatFloor hOut)
    hMaxUlps

theorem floatApproxULP_div_rounded_mode_output
    {mode : IEEERoundingMode}
    {ux uy x xHat y yHat AxHat denFloor uOut zRounded atol : ℝ}
    (hx : floatApprox ux x xHat)
    (hy : floatApprox uy y yHat)
    (hXHatBound : |xHat| ≤ AxHat)
    (hDenFloorPos : 0 < denFloor)
    (hYFloor : denFloor ≤ |y|)
    (hYHatFloor : denFloor ≤ |yHat|)
    (hOut : floatApprox uOut (xHat / yHat) zRounded) :
    floatApproxULP atol (modeUlps mode)
      (ux / denFloor + AxHat * uy / (denFloor * denFloor) + uOut)
      (x / y) zRounded := by
  exact floatApproxULP_of_floatApprox
    (floatApprox_div_rounded_right_output
      hx hy hXHatBound hDenFloorPos hYFloor hYHatFloor hOut)
    (one_le_modeUlps mode)

theorem floatApprox_div_rounded_mode_output_of_adapter
    {mode : IEEERoundingMode}
    {adapter : IEEEAuditAdapter}
    {ux uy x xHat y yHat AxHat denFloor atol : ℝ}
    (hx : floatApprox ux x xHat)
    (hy : floatApprox uy y yHat)
    (hXHatBound : |xHat| ≤ AxHat)
    (hDenFloorPos : 0 < denFloor)
    (hYFloor : denFloor ≤ |y|)
    (hYHatFloor : denFloor ≤ |yHat|) :
    floatApprox
      (ux / denFloor + AxHat * uy / (denFloor * denFloor) +
        modeOutputBudget mode atol (adapter.ulp (xHat / yHat)))
      (x / y) (adapter.round mode (xHat / yHat)) := by
  have hOut :
      floatApprox
        (modeOutputBudget mode atol (adapter.ulp (xHat / yHat)))
        (xHat / yHat) (adapter.round mode (xHat / yHat)) := by
    exact adapter.round_sound mode atol (xHat / yHat)
  exact floatApprox_div_rounded_right_output
    hx hy hXHatBound hDenFloorPos hYFloor hYHatFloor hOut

theorem floatApproxULP_div_rounded_mode_output_of_adapter
    {mode : IEEERoundingMode}
    {adapter : IEEEAuditAdapter}
    {ux uy x xHat y yHat AxHat denFloor atol : ℝ}
    (hx : floatApprox ux x xHat)
    (hy : floatApprox uy y yHat)
    (hXHatBound : |xHat| ≤ AxHat)
    (hDenFloorPos : 0 < denFloor)
    (hYFloor : denFloor ≤ |y|)
    (hYHatFloor : denFloor ≤ |yHat|) :
    floatApproxULP atol (modeUlps mode)
      (ux / denFloor + AxHat * uy / (denFloor * denFloor) +
        modeOutputBudget mode atol (adapter.ulp (xHat / yHat)))
      (x / y) (adapter.round mode (xHat / yHat)) := by
  exact floatApproxULP_mode_of_floatApprox
    (floatApprox_div_rounded_mode_output_of_adapter
      hx hy hXHatBound hDenFloorPos hYFloor hYHatFloor)

noncomputable def roundedDivWord
    (adapter : IEEEBitPreciseAdapter)
    (mode : IEEERoundingMode)
    (x y : ℝ) : adapter.Word :=
  adapter.roundWord mode (adapter.encode (x / y))

noncomputable def roundedDivVal
    (adapter : IEEEBitPreciseAdapter)
    (mode : IEEERoundingMode)
    (x y : ℝ) : ℝ :=
  adapter.decode (roundedDivWord adapter mode x y)

theorem roundedDivVal_eq_round
    (adapter : IEEEBitPreciseAdapter)
    (mode : IEEERoundingMode)
    (x y : ℝ) :
    roundedDivVal adapter mode x y = adapter.round mode (x / y) := by
  unfold roundedDivVal roundedDivWord
  simpa using (adapter.round_decode_sound mode (x / y)).symm

theorem roundedDiv_ulp_eq_word
    (adapter : IEEEBitPreciseAdapter)
    (x y : ℝ) :
    adapter.ulp (x / y) = adapter.ulpWord (adapter.encode (x / y)) := by
  simpa using adapter.ulp_decode_sound (x / y)

theorem floatApprox_div_rounded_mode_output_word_of_adapter
    {mode : IEEERoundingMode}
    {adapter : IEEEBitPreciseAdapter}
    {ux uy x xHat y yHat AxHat denFloor atol : ℝ}
    (hx : floatApprox ux x xHat)
    (hy : floatApprox uy y yHat)
    (hXHatBound : |xHat| ≤ AxHat)
    (hDenFloorPos : 0 < denFloor)
    (hYFloor : denFloor ≤ |y|)
    (hYHatFloor : denFloor ≤ |yHat|) :
    floatApprox
      (ux / denFloor + AxHat * uy / (denFloor * denFloor) +
        modeOutputBudget mode atol (adapter.ulpWord (adapter.encode (xHat / yHat))))
      (x / y) (roundedDivVal adapter mode xHat yHat) := by
  have hBase :
      floatApprox
        (ux / denFloor + AxHat * uy / (denFloor * denFloor) +
          modeOutputBudget mode atol (adapter.ulp (xHat / yHat)))
        (x / y) (adapter.round mode (xHat / yHat)) :=
    floatApprox_div_rounded_mode_output_of_adapter
      (mode := mode) (adapter := adapter.toIEEEAuditAdapter)
      hx hy hXHatBound hDenFloorPos hYFloor hYHatFloor
  have hUlp :
      modeOutputBudget mode atol (adapter.ulp (xHat / yHat))
        = modeOutputBudget mode atol (adapter.ulpWord (adapter.encode (xHat / yHat))) := by
    simp [roundedDiv_ulp_eq_word]
  have hOut :
      roundedDivVal adapter mode xHat yHat = adapter.round mode (xHat / yHat) := by
    exact roundedDivVal_eq_round adapter mode xHat yHat
  simpa [hUlp, hOut] using hBase

theorem floatApproxULP_div_rounded_mode_output_word_of_adapter
    {mode : IEEERoundingMode}
    {adapter : IEEEBitPreciseAdapter}
    {ux uy x xHat y yHat AxHat denFloor atol : ℝ}
    (hx : floatApprox ux x xHat)
    (hy : floatApprox uy y yHat)
    (hXHatBound : |xHat| ≤ AxHat)
    (hDenFloorPos : 0 < denFloor)
    (hYFloor : denFloor ≤ |y|)
    (hYHatFloor : denFloor ≤ |yHat|) :
    floatApproxULP atol (modeUlps mode)
      (ux / denFloor + AxHat * uy / (denFloor * denFloor) +
        modeOutputBudget mode atol (adapter.ulpWord (adapter.encode (xHat / yHat))))
      (x / y) (roundedDivVal adapter mode xHat yHat) := by
  exact floatApproxULP_mode_of_floatApprox
    (floatApprox_div_rounded_mode_output_word_of_adapter
      (mode := mode) (adapter := adapter)
      hx hy hXHatBound hDenFloorPos hYFloor hYHatFloor)

end BEACONS
end Eigen
end HeytingLean
