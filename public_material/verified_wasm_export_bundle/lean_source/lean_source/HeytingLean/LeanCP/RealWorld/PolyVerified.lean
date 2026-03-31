import HeytingLean.LeanCP.RealWorld.INTTVerified
import HeytingLean.Crypto.Lattice.NTTConvolution
import HeytingLean.Crypto.KEM.MLKEMCompress

namespace HeytingLean.LeanCP.RealWorld

open HeytingLean.Crypto.Lattice
open NTTVerified
open INTTVerified

namespace PolyVerified

abbrev q : Nat := NTTIterative.q
abbrev F : Type := NTTIterative.F

private theorem size_applyForwardOpField (a : Array F) (op : NTTIterative.ForwardOp) :
    (NTTIterative.applyForwardOp a op).size = a.size := by
  simp [NTTIterative.applyForwardOp, Array.size_setIfInBounds]

private theorem size_applyForwardOpsField (ops : List NTTIterative.ForwardOp) (a : Array F) :
    (NTTIterative.applyForwardOps ops a).size = a.size := by
  induction ops generalizing a with
  | nil =>
      simp [NTTIterative.applyForwardOps]
  | cons op ops ih =>
      simp [NTTIterative.applyForwardOps]
      calc
        (List.foldl (fun acc op => NTTIterative.applyForwardOp acc op)
            (NTTIterative.applyForwardOp a op) ops).size
            = (NTTIterative.applyForwardOp a op).size := ih _
        _ = a.size := size_applyForwardOpField a op

private theorem size_applyInverseOp256Field
    (inv2 : F) (a : Array F) (ha : a.size = 256) (op : NTTIterative.InverseOp) :
    (NTTIterative.applyInverseOp256 inv2 a ha op).size = a.size := by
  simp [NTTIterative.applyInverseOp256, Array.size_set]

private theorem size_applyInverseOps256Field
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
        size_applyInverseOp256Field (inv2 := inv2) (a := a) (ha := ha) (op := op)]

private theorem size_inttField (a : Array F) (ha : a.size = 256) :
    (NTTIterative.inttIterative a ha).size = 256 := by
  simpa [NTTIterative.inttIterative, ha] using
    size_applyInverseOps256Field (inv2 := ((2 : F)⁻¹)) (ops := NTTIterative.inverseOps) (a := a) (ha := ha)

def polyAddInt (a b : Array Int) : Array Int :=
  Array.ofFn (fun i : Fin 256 =>
    normalizeFieldCoeff (coeffToField (a.getD i.val 0) + coeffToField (b.getD i.val 0)))

def polySubInt (a b : Array Int) : Array Int :=
  Array.ofFn (fun i : Fin 256 =>
    normalizeFieldCoeff (coeffToField (a.getD i.val 0) - coeffToField (b.getD i.val 0)))

theorem polyAddInt_size (a b : Array Int) : (polyAddInt a b).size = 256 := by
  simp [polyAddInt]

theorem polySubInt_size (a b : Array Int) : (polySubInt a b).size = 256 := by
  simp [polySubInt]

theorem fieldArray256_polyAddInt (a b : Array Int) :
    fieldArray256 (polyAddInt a b) =
      Array.ofFn (fun i : Fin 256 => coeffToField (a.getD i.val 0) + coeffToField (b.getD i.val 0)) := by
  apply Array.ext_getElem?
  intro i
  by_cases hi : i < 256
  · have hiL : i < (fieldArray256 (polyAddInt a b)).size := by
      simpa [fieldArray256] using hi
    have hEq :
        coeffToField ((polyAddInt a b).getD i 0) =
          coeffToField (a.getD i 0) + coeffToField (b.getD i 0) := by
      simp [polyAddInt, Array.getD_eq_getD_getElem?, hi, coeffToField_normalizeFieldCoeff]
    have hLopt :
        (fieldArray256 (polyAddInt a b))[i]? =
          some (coeffToField ((polyAddInt a b).getD i 0)) := by
      simp [fieldArray256, Array.getD_eq_getD_getElem?, hi]
    have hRopt :
        (Array.ofFn (fun i : Fin 256 => coeffToField (a.getD i.val 0) + coeffToField (b.getD i.val 0)))[i]? =
          some (coeffToField (a.getD i 0) + coeffToField (b.getD i 0)) := by
      simp [hi]
    rw [hLopt, hRopt]
    exact congrArg some hEq
  · simp [fieldArray256, polyAddInt, Array.getElem?_ofFn, hi]

theorem fieldArray256_polySubInt (a b : Array Int) :
    fieldArray256 (polySubInt a b) =
      Array.ofFn (fun i : Fin 256 => coeffToField (a.getD i.val 0) - coeffToField (b.getD i.val 0)) := by
  apply Array.ext_getElem?
  intro i
  by_cases hi : i < 256
  · have hiL : i < (fieldArray256 (polySubInt a b)).size := by
      simpa [fieldArray256] using hi
    have hEq :
        coeffToField ((polySubInt a b).getD i 0) =
          coeffToField (a.getD i 0) - coeffToField (b.getD i 0) := by
      simp [polySubInt, Array.getD_eq_getD_getElem?, hi, coeffToField_normalizeFieldCoeff]
    have hLopt :
        (fieldArray256 (polySubInt a b))[i]? =
          some (coeffToField ((polySubInt a b).getD i 0)) := by
      simp [fieldArray256, Array.getD_eq_getD_getElem?, hi]
    have hRopt :
        (Array.ofFn (fun i : Fin 256 => coeffToField (a.getD i.val 0) - coeffToField (b.getD i.val 0)))[i]? =
          some (coeffToField (a.getD i 0) - coeffToField (b.getD i 0)) := by
      simp [hi]
    rw [hLopt, hRopt]
    exact congrArg some hEq
  · simp [fieldArray256, polySubInt, Array.getElem?_ofFn, hi]

def basemulInt (a b : Array Int) : Array Int :=
  intArray256OfField
    (NTTIterative.basemul (fieldArray256 a) (fieldArray256 b) (fieldArray256_size a) (fieldArray256_size b))

theorem basemulInt_size (a b : Array Int) : (basemulInt a b).size = 256 := by
  simp [basemulInt, intArray256OfField]

theorem fieldArray256_basemulInt (a b : Array Int) :
    fieldArray256 (basemulInt a b) =
      NTTIterative.basemul (fieldArray256 a) (fieldArray256 b) (fieldArray256_size a) (fieldArray256_size b) := by
  simpa [basemulInt] using
    fieldArray256_intArray256OfField
      (a := NTTIterative.basemul (fieldArray256 a) (fieldArray256 b) (fieldArray256_size a) (fieldArray256_size b))
      (ha := by simp [NTTIterative.basemul])

def polyMulViaNTTInt (a b : Array Int) : Array Int :=
  let nttA := NTTIterative.nttIterative (fieldArray256 a) (fieldArray256_size a)
  let nttB := NTTIterative.nttIterative (fieldArray256 b) (fieldArray256_size b)
  let hnttA : nttA.size = 256 := by
    simpa [nttA, NTTIterative.nttIterative, fieldArray256_size a] using
      size_applyForwardOpsField NTTIterative.forwardOps (fieldArray256 a)
  let hnttB : nttB.size = 256 := by
    simpa [nttB, NTTIterative.nttIterative, fieldArray256_size b] using
      size_applyForwardOpsField NTTIterative.forwardOps (fieldArray256 b)
  let nttProd := NTTIterative.basemul nttA nttB hnttA hnttB
  let hnttProd : nttProd.size = 256 := by
    simp [nttProd, NTTIterative.basemul]
  intArray256OfField (NTTIterative.inttIterative nttProd hnttProd)

theorem polyMulViaNTTInt_size (a b : Array Int) : (polyMulViaNTTInt a b).size = 256 := by
  simp [polyMulViaNTTInt, intArray256OfField]

theorem polyMulViaNTTInt_refines (a b : Array Int) :
    fieldArray256 (polyMulViaNTTInt a b) =
      NTTConvolution.Task5.negacyclicConv (fieldArray256 a) (fieldArray256 b)
        (fieldArray256_size a) (fieldArray256_size b) := by
  let nttA := NTTIterative.nttIterative (fieldArray256 a) (fieldArray256_size a)
  let nttB := NTTIterative.nttIterative (fieldArray256 b) (fieldArray256_size b)
  let hnttA : nttA.size = 256 := by
    simpa [nttA, NTTIterative.nttIterative, fieldArray256_size a] using
      size_applyForwardOpsField NTTIterative.forwardOps (fieldArray256 a)
  let hnttB : nttB.size = 256 := by
    simpa [nttB, NTTIterative.nttIterative, fieldArray256_size b] using
      size_applyForwardOpsField NTTIterative.forwardOps (fieldArray256 b)
  let nttProd := NTTIterative.basemul nttA nttB hnttA hnttB
  let hnttProd : nttProd.size = 256 := by
    simp [nttProd, NTTIterative.basemul]
  have hMul :
      NTTIterative.inttIterative nttProd hnttProd =
        NTTConvolution.Task5.negacyclicConv (fieldArray256 a) (fieldArray256 b)
          (fieldArray256_size a) (fieldArray256_size b) := by
    simpa [polyMulViaNTTInt, nttA, nttB, nttProd] using
      NTTConvolution.Task5.ntt_mul_correct
        (a := fieldArray256 a) (b := fieldArray256 b)
        (ha := fieldArray256_size a) (hb := fieldArray256_size b)
  calc
    fieldArray256 (polyMulViaNTTInt a b)
        = NTTIterative.inttIterative nttProd hnttProd := by
            simpa [polyMulViaNTTInt, nttA, nttB, nttProd] using
              fieldArray256_intArray256OfField
                (a := NTTIterative.inttIterative nttProd hnttProd)
                (ha := size_inttField (a := nttProd) (ha := hnttProd))
    _ = NTTConvolution.Task5.negacyclicConv (fieldArray256 a) (fieldArray256 b)
          (fieldArray256_size a) (fieldArray256_size b) := hMul

open HeytingLean.Crypto.KEM.FIPS203.Compress

def compressCoeffInt (d : Nat) (x : Int) : Fin (2 ^ d) :=
  compress (q := q) d (coeffToField x)

def decompressCoeffInt (d : Nat) (x : Fin (2 ^ d)) : Int :=
  normalizeFieldCoeff (decompress (q := q) d x)

theorem coeffToField_decompressCoeffInt (d : Nat) (x : Fin (2 ^ d)) :
    coeffToField (decompressCoeffInt d x) = decompress (q := q) d x := by
  simp [decompressCoeffInt, coeffToField_normalizeFieldCoeff]

end PolyVerified

end HeytingLean.LeanCP.RealWorld
