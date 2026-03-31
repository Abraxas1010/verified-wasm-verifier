import Mathlib.Analysis.Quaternion

noncomputable section

open scoped Quaternion

namespace HeytingLean.Generative.SpinorBridge.ClosureSDK

abbrev Q := Quaternion ℝ

/-- The standard quaternion basis element `i`. -/
def quatI : Q := ⟨0, 1, 0, 0⟩

/-- The standard quaternion basis element `j`. -/
def quatJ : Q := ⟨0, 0, 1, 0⟩

/-- The standard quaternion basis element `k`. -/
def quatK : Q := ⟨0, 0, 0, 1⟩

@[simp] theorem star_quatI : star quatI = -quatI := by
  ext <;> simp [quatI]

@[simp] theorem star_quatJ : star quatJ = -quatJ := by
  ext <;> simp [quatJ]

@[simp] theorem star_quatK : star quatK = -quatK := by
  ext <;> simp [quatK]

@[simp] theorem quatI_mul_quatJ : quatI * quatJ = quatK := by
  ext <;> simp [quatI, quatJ, quatK]

@[simp] theorem quatJ_mul_quatI : quatJ * quatI = -quatK := by
  ext <;> simp [quatI, quatJ, quatK]

@[simp] theorem quatJ_mul_quatK : quatJ * quatK = quatI := by
  ext <;> simp [quatI, quatJ, quatK]

@[simp] theorem quatK_mul_quatJ : quatK * quatJ = -quatI := by
  ext <;> simp [quatI, quatJ, quatK]

@[simp] theorem quatK_mul_quatI : quatK * quatI = quatJ := by
  ext <;> simp [quatI, quatJ, quatK]

@[simp] theorem quatI_mul_quatK : quatI * quatK = -quatJ := by
  ext <;> simp [quatI, quatJ, quatK]

/-- A concrete witness that quaternion multiplication is non-commutative. -/
theorem quaternion_noncommutative : ∃ a b : Q, a * b ≠ b * a := by
  refine ⟨quatI, quatJ, ?_⟩
  intro h
  have himK := congrArg (fun q : Q => q.imK) h
  norm_num [quatI_mul_quatJ, quatJ_mul_quatI, quatK] at himK

end HeytingLean.Generative.SpinorBridge.ClosureSDK
