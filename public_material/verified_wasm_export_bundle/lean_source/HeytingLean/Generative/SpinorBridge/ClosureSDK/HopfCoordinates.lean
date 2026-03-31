import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import HeytingLean.Generative.SpinorBridge.ClosureSDK.ConjugationChannels

noncomputable section

open scoped Quaternion

namespace HeytingLean.Generative.SpinorBridge.ClosureSDK

/-- A non-trivial balanced quaternion sample with all coordinates equal. -/
def quatUniform : Q := ⟨(1 : ℝ) / 2, (1 : ℝ) / 2, (1 : ℝ) / 2, (1 : ℝ) / 2⟩

/-- The first Hopf base coordinate from the Closure SDK formula. -/
def hopfProjectX (q : Q) : ℝ :=
  2 * (q.imI * q.imK + q.re * q.imJ)

/-- The second Hopf base coordinate from the Closure SDK formula. -/
def hopfProjectY (q : Q) : ℝ :=
  2 * (q.imJ * q.imK - q.re * q.imI)

/-- The third Hopf base coordinate from the Closure SDK formula. -/
def hopfProjectZ (q : Q) : ℝ :=
  q.re ^ 2 + q.imK ^ 2 - q.imI ^ 2 - q.imJ ^ 2

/-- The coordinate formula used for the Hopf-style base projection. -/
def hopfProject (q : Q) : Fin 3 → ℝ
  | 0 => hopfProjectX q
  | 1 => hopfProjectY q
  | _ => hopfProjectZ q

/-- The imaginary input used by the SDK's fiber-angle formula. -/
def hopfPhaseNumerator (q : Q) : ℝ :=
  2 * (q.re * q.imI + q.imJ * q.imK)

/-- The real input used by the SDK's fiber-angle formula. -/
def hopfPhaseDenominator (q : Q) : ℝ :=
  q.re ^ 2 + q.imK ^ 2 - q.imI ^ 2 - q.imJ ^ 2

/-- The Hopf fiber phase from the Closure SDK formula. -/
def hopfPhase (q : Q) : ℝ :=
  Complex.arg ((hopfPhaseDenominator q : ℂ) + (hopfPhaseNumerator q : ℂ) * Complex.I)

/-- The Closure SDK `sigma` observable. -/
def sigma (q : Q) : ℝ :=
  2 * Real.arccos |q.re|

@[simp] theorem hopfProject_apply_zero (q : Q) : hopfProject q 0 = hopfProjectX q := rfl

@[simp] theorem hopfProject_apply_one (q : Q) : hopfProject q 1 = hopfProjectY q := rfl

@[simp] theorem hopfProject_apply_two (q : Q) : hopfProject q 2 = hopfProjectZ q := rfl

@[simp] theorem sigma_one : sigma (1 : Q) = 0 := by
  simp [sigma]

@[simp] theorem sigma_neg_one : sigma (-1 : Q) = 0 := by
  simp [sigma]

@[simp] theorem sigma_quatI : sigma quatI = Real.pi := by
  rw [sigma, quatI]
  norm_num
  ring

@[simp] theorem hopfProject_one_zero : hopfProject (1 : Q) 0 = 0 := by
  norm_num [hopfProject, hopfProjectX]

@[simp] theorem hopfProject_one_one : hopfProject (1 : Q) 1 = 0 := by
  norm_num [hopfProject, hopfProjectY]

@[simp] theorem hopfProject_one_two : hopfProject (1 : Q) 2 = 1 := by
  norm_num [hopfProject, hopfProjectZ]

@[simp] theorem hopfProject_neg_one_zero : hopfProject (-1 : Q) 0 = 0 := by
  norm_num [hopfProject, hopfProjectX]

@[simp] theorem hopfProject_neg_one_one : hopfProject (-1 : Q) 1 = 0 := by
  norm_num [hopfProject, hopfProjectY]

@[simp] theorem hopfProject_neg_one_two : hopfProject (-1 : Q) 2 = 1 := by
  norm_num [hopfProject, hopfProjectZ]

@[simp] theorem hopfProject_quatI_zero : hopfProject quatI 0 = 0 := by
  norm_num [hopfProject, hopfProjectX, quatI]

@[simp] theorem hopfProject_quatI_one : hopfProject quatI 1 = 0 := by
  norm_num [hopfProject, hopfProjectY, quatI]

@[simp] theorem hopfProject_quatI_two : hopfProject quatI 2 = -1 := by
  norm_num [hopfProject, hopfProjectZ, quatI]

@[simp] theorem hopfPhase_one : hopfPhase (1 : Q) = 0 := by
  simp [hopfPhase, hopfPhaseNumerator, hopfPhaseDenominator]

@[simp] theorem hopfPhase_quatI : hopfPhase quatI = Real.pi := by
  rw [hopfPhase, hopfPhaseNumerator, hopfPhaseDenominator, quatI]
  norm_num

@[simp] theorem hopfProject_quatUniform_zero : hopfProject quatUniform 0 = 1 := by
  norm_num [hopfProject, hopfProjectX, quatUniform]

@[simp] theorem hopfProject_quatUniform_one : hopfProject quatUniform 1 = 0 := by
  norm_num [hopfProject, hopfProjectY, quatUniform]

@[simp] theorem hopfProject_quatUniform_two : hopfProject quatUniform 2 = 0 := by
  norm_num [hopfProject, hopfProjectZ, quatUniform]

@[simp] theorem hopfPhase_quatUniform : hopfPhase quatUniform = Real.pi / 2 := by
  rw [hopfPhase, hopfPhaseNumerator, hopfPhaseDenominator, quatUniform]
  norm_num

end HeytingLean.Generative.SpinorBridge.ClosureSDK
