import HeytingLean.LeanCP.RealWorld.NTTVerified

namespace HeytingLean.LeanCP.RealWorld

open HeytingLean.Crypto.Lattice
open NTTVerified

namespace INTTVerified

abbrev q : Nat := NTTIterative.q
abbrev F : Type := NTTIterative.F

/-- Convert a size-256 field array back to centered machine representatives. -/
def intArray256OfField (a : Array F) : Array Int :=
  Array.ofFn (fun i : Fin 256 => normalizeFieldCoeff (a.getD i.val 0))

theorem intArray256OfField_size (a : Array F) : (intArray256OfField a).size = 256 := by
  simp [intArray256OfField]

theorem fieldArray256_intArray256OfField (a : Array F) (ha : a.size = 256) :
    fieldArray256 (intArray256OfField a) = a := by
  apply Array.ext_getElem?
  intro i
  by_cases hi : i < 256
  · have hiL : i < (fieldArray256 (intArray256OfField a)).size := by
      simpa [fieldArray256] using hi
    have hiR : i < a.size := by
      simpa [ha] using hi
    have hEq :
        coeffToField ((intArray256OfField a).getD i 0) = a.getD i 0 := by
      simp [intArray256OfField, fieldArray256, Array.getD_eq_getD_getElem?, hi, hiR,
        coeffToField_normalizeFieldCoeff]
    have hLopt :
        (fieldArray256 (intArray256OfField a))[i]? =
          some (coeffToField ((intArray256OfField a).getD i 0)) := by
      simp [fieldArray256, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hi]
    have hRopt : a[i]? = some (a.getD i 0) := by
      simp [Array.getD_eq_getD_getElem?, hiR]
    rw [hLopt, hRopt]
    exact congrArg some hEq
  · have hiL : ¬ i < (fieldArray256 (intArray256OfField a)).size := by
      simpa [fieldArray256] using hi
    have hiR : ¬ i < a.size := by
      simpa [ha] using hi
    simp [Array.getElem?_eq_none, hiL, hiR]

theorem centered_intArray256OfField (a : Array F) :
    CenteredCoeffs (intArray256OfField a) := by
  intro i hi
  have hiA : i < (intArray256OfField a).size := by
    simpa [intArray256OfField] using hi
  have hi256 : i < 256 := by
    simpa [intArray256OfField] using hi
  simpa [intArray256OfField, Array.getD_eq_getD_getElem?, hiA, hi256] using
    normalizeFieldCoeff_centered (a.getD i 0)

private theorem size_applyInverseOp256
    (inv2 : F) (a : Array F) (ha : a.size = 256) (op : NTTIterative.InverseOp) :
    (NTTIterative.applyInverseOp256 inv2 a ha op).size = a.size := by
  simp [NTTIterative.applyInverseOp256, Array.size_set]

private theorem size_applyInverseOps256
    (inv2 : F) (ops : List NTTIterative.InverseOp) (a : Array F) (ha : a.size = 256) :
    (NTTIterative.applyInverseOps256 inv2 ops a ha).size = a.size := by
  revert a
  induction ops with
  | nil =>
      intro a ha
      simp [NTTIterative.applyInverseOps256]
  | cons op ops ih =>
      intro a ha
      simp [NTTIterative.applyInverseOps256, ih,
        size_applyInverseOp256 (inv2 := inv2) (a := a) (ha := ha) (op := op)]

private theorem size_inttField (a : Array F) (ha : a.size = 256) :
    (NTTIterative.inttIterative a ha).size = 256 := by
  simpa [NTTIterative.inttIterative, ha] using
    size_applyInverseOps256 (inv2 := ((2 : F)⁻¹)) (ops := NTTIterative.inverseOps) (a := a) (ha := ha)

/-- LeanCP-facing inverse NTT transport via the certified lattice inverse transform. -/
def inttIterativeInt (a : Array Int) (_ha : a.size = 256) : Array Int :=
  intArray256OfField (NTTIterative.inttIterative (fieldArray256 a) (fieldArray256_size a))

theorem size_inttIterativeInt (a : Array Int) (ha : a.size = 256) :
    (inttIterativeInt a ha).size = 256 := by
  simp [inttIterativeInt, intArray256OfField]

theorem centered_inttIterativeInt (a : Array Int) (ha : a.size = 256) :
    CenteredCoeffs (inttIterativeInt a ha) := by
  simpa [inttIterativeInt] using
    centered_intArray256OfField (NTTIterative.inttIterative (fieldArray256 a) (fieldArray256_size a))

theorem inttIterativeInt_refines (a : Array Int) (ha : a.size = 256) :
    fieldArray256 (inttIterativeInt a ha) =
      NTTIterative.inttIterative (fieldArray256 a) (fieldArray256_size a) := by
  simpa [inttIterativeInt] using
    fieldArray256_intArray256OfField
      (a := NTTIterative.inttIterative (fieldArray256 a) (fieldArray256_size a))
      (ha := size_inttField (a := fieldArray256 a) (ha := fieldArray256_size a))

end INTTVerified

end HeytingLean.LeanCP.RealWorld
