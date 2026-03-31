import HeytingLean.Generative.SpinorBridge.ClosureSDK.QuaternionCore

noncomputable section

open scoped Quaternion

namespace HeytingLean.Generative.SpinorBridge.ClosureSDK

abbrev scalarPart (q : Q) : Q := (q.re : Q)

abbrev vectorPart (q : Q) : Q := q.im

/-- Every quaternion splits into its scalar and vector channels. -/
theorem scalar_vector_decomp (q : Q) : scalarPart q + vectorPart q = q := by
  simp [scalarPart, vectorPart, Quaternion.re_add_im]

@[simp] theorem star_scalarPart (q : Q) : star (scalarPart q) = scalarPart q := by
  simp [scalarPart]

@[simp] theorem star_vectorPart (q : Q) : star (vectorPart q) = -vectorPart q := by
  simp [vectorPart]

@[simp] theorem scalarPart_quatI : scalarPart quatI = 0 := by
  ext <;> simp [scalarPart, quatI]

@[simp] theorem scalarPart_quatJ : scalarPart quatJ = 0 := by
  ext <;> simp [scalarPart, quatJ]

@[simp] theorem scalarPart_quatK : scalarPart quatK = 0 := by
  ext <;> simp [scalarPart, quatK]

@[simp] theorem vectorPart_quatI : vectorPart quatI = quatI := by
  ext <;> simp [vectorPart, quatI]

@[simp] theorem vectorPart_quatJ : vectorPart quatJ = quatJ := by
  ext <;> simp [vectorPart, quatJ]

@[simp] theorem vectorPart_quatK : vectorPart quatK = quatK := by
  ext <;> simp [vectorPart, quatK]

end HeytingLean.Generative.SpinorBridge.ClosureSDK
