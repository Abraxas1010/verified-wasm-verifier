import HeytingLean.Crypto.Lattice.NTTBridgeProof
import HeytingLean.Crypto.Lattice.NTTCRTBridge
import HeytingLean.Crypto.Lattice.NTTSpecCRTBridge
import Mathlib.Algebra.Polynomial.Div
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Ring

/-!
# Gap 1 Tasks 4–5: round-trip and convolution correctness (algorithm level)

This module finishes the remaining Gap 1 steps:

Task 4:
- prove `inttIterative (nttIterative a) = a` for all size-256 coefficient arrays;
- prove the reverse direction `nttIterative (inttIterative t) = t` for all size-256 NTT-domain arrays.

Task 5:
- prove that the NTT-domain multiplication (`basemul`) implements negacyclic multiplication in the
  quotient ring `Rq = (ZMod 3329)[X] ⧸ ⟨X^256 + 1⟩` when transported back to coefficients by the
  iterative inverse NTT.
-/

set_option maxRecDepth 4096

namespace HeytingLean
namespace Crypto
namespace Lattice
namespace NTTConvolution

open scoped BigOperators

open NTTIterative
open NTTBridge
open NTTBridgeProof

abbrev q : Nat := NTT.q
abbrev F : Type := ZMod q
abbrev Idx : Type := Fin 256
abbrev Vec : Type := Idx → F

private def vecOfArray (a : Array F) : Vec :=
  fun i => a.getD i.val 0

private def arrayOfVec (v : Vec) : Array F :=
  Array.ofFn v

private def basisArray (i : Idx) : Array F :=
  Array.ofFn (fun j : Idx => if j = i then (1 : F) else 0)

private lemma size_basisArray (i : Idx) : (basisArray i).size = 256 := by
  simp [basisArray]

private lemma size_applyForwardOp (a : Array F) (op : ForwardOp) :
    (applyForwardOp a op).size = a.size := by
  simp [applyForwardOp]

private lemma size_applyForwardOps (ops : List ForwardOp) (a : Array F) :
    (applyForwardOps ops a).size = a.size := by
  revert a
  induction ops with
  | nil =>
      intro a
      simp [applyForwardOps]
  | cons op ops ih =>
      intro a
      have hfold : applyForwardOps (op :: ops) a = applyForwardOps ops (applyForwardOp a op) := by
        rfl
      calc
        (applyForwardOps (op :: ops) a).size
            = (applyForwardOps ops (applyForwardOp a op)).size := by simp [hfold]
        _ = (applyForwardOp a op).size := by simpa using (ih (a := applyForwardOp a op))
        _ = a.size := size_applyForwardOp a op

private lemma size_nttIterative (a : Array F) (ha : a.size = 256) :
    (nttIterative a ha).size = 256 := by
  -- `applyForwardOps` preserves size.
  simpa [nttIterative, ha] using (size_applyForwardOps forwardOps a)

private lemma size_applyInverseOp256 (inv2 : F) (a : Array F) (ha : a.size = 256) (op : InverseOp) :
    (applyInverseOp256 inv2 a ha op).size = a.size := by
  -- Two `set`s preserve size.
  simp [applyInverseOp256, Array.size_set]

private lemma size_applyInverseOps256 (inv2 : F) (ops : List InverseOp) (a : Array F) (ha : a.size = 256) :
    (NTTIterative.applyInverseOps256 inv2 ops a ha).size = a.size := by
  revert a
  induction ops with
  | nil =>
      intro a ha
      simp [NTTIterative.applyInverseOps256]
  | cons op ops ih =>
      intro a ha
      -- Unfold one step and use size preservation of `applyInverseOp256`.
      simp [NTTIterative.applyInverseOps256, ih, size_applyInverseOp256 (inv2 := inv2) (a := a) (ha := ha) (op := op)]

private lemma size_inttIterative (a : Array F) (ha : a.size = 256) :
    (inttIterative a ha).size = 256 := by
  -- `applyInverseOps256` preserves size.
  simpa [inttIterative, ha] using
    (size_applyInverseOps256 (inv2 := ((2 : F)⁻¹)) (ops := inverseOps) (a := a) (ha := ha))

private lemma vecOfArray_arrayOfVec (v : Vec) : vecOfArray (arrayOfVec v) = v := by
  funext i
  simp [vecOfArray, arrayOfVec, Array.getD_eq_getD_getElem?]

private lemma arrayOfVec_vecOfArray (a : Array F) (ha : a.size = 256) :
    arrayOfVec (vecOfArray a) = a := by
  classical
  apply Array.ext_getElem?
  intro i
  by_cases hi : i < 256
  · have hi' : i < a.size := by
      rw [ha]
      exact hi
    have hD : a.getD i 0 = a[i] := by
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi']
    have hL : (arrayOfVec (vecOfArray a))[i]? = some (a.getD i 0) := by
      simp [arrayOfVec, vecOfArray, hi]
    have hR : a[i]? = some (a[i]) := by
      exact Array.getElem?_eq_getElem hi'
    simp [hL, hR, hD]
  · have hle : a.size ≤ i := by
      rw [ha]
      exact Nat.le_of_not_gt hi
    have hleL : (arrayOfVec (vecOfArray a)).size ≤ i := by
      have : (256 : Nat) ≤ i := Nat.le_of_not_gt hi
      simpa [arrayOfVec] using this
    have hL : (arrayOfVec (vecOfArray a))[i]? = none := Array.getElem?_eq_none hleL
    have hR : a[i]? = none := Array.getElem?_eq_none hle
    simp [hL, hR]

private lemma array_eq_of_vecOfArray_eq (a b : Array F) (ha : a.size = 256) (hb : b.size = 256)
    (h : vecOfArray a = vecOfArray b) : a = b := by
  classical
  apply Array.ext_getElem?
  intro i
  by_cases hi : i < 256
  · have hiA : i < a.size := by simpa [ha] using hi
    have hiB : i < b.size := by simpa [hb] using hi
    have hVec : vecOfArray a ⟨i, hi⟩ = vecOfArray b ⟨i, hi⟩ := by
      simp [h]
    have hA : a.getD i 0 = a[i] := by
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hiA]
    have hB : b.getD i 0 = b[i] := by
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hiB]
    have hAB : a[i] = b[i] := by
      simpa [vecOfArray, hA, hB] using hVec
    simp [Array.getElem?_eq_getElem hiA, Array.getElem?_eq_getElem hiB, hAB]
  · have hleA : a.size ≤ i := by
      rw [ha]
      exact Nat.le_of_not_gt hi
    have hleB : b.size ≤ i := by
      rw [hb]
      exact Nat.le_of_not_gt hi
    simp [Array.getElem?_eq_none hleA, Array.getElem?_eq_none hleB]

/-!
## Task 4: round-trip theorems
-/

theorem inttIterative_nttIterative_roundtrip_on_basis :
    ∀ i : Idx,
      inttIterative (nttIterative (basisArray i) (by simp [basisArray]))
          (size_nttIterative (a := basisArray i) (ha := by simp [basisArray])) =
        basisArray i := by
  native_decide

theorem nttIterative_inttIterative_roundtrip_on_basis :
    ∀ i : Idx,
      nttIterative (inttIterative (basisArray i) (by simp [basisArray]))
          (size_inttIterative (a := basisArray i) (ha := by simp [basisArray])) =
        basisArray i := by
  native_decide

/-!
We lift the basis-vector round-trips to all inputs using linearity:

- `nttIterative` is the quadratic-spec matrix transform (`NTTBridgeProof.nttIterative_matches_quadraticSpec_proved`).
- `inttIterative` is a fixed composition of linear inverse butterflies (`inverseOps`).
-/

private def basisVec (i : Idx) : Vec :=
  fun j : Idx => if j = i then (1 : F) else 0

private lemma basisVec_eq_piSingle (i : Idx) : basisVec i = (Pi.single i (1 : F) : Vec) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [basisVec, Pi.single, Function.update]
  · simp [basisVec, Pi.single, Function.update, h]

private lemma vecOfArray_basisArray (i : Idx) :
    vecOfArray (basisArray i) = basisVec i := by
  funext j
  by_cases h : j = i
  · subst h
    simp [basisArray, basisVec, vecOfArray, Array.getD_eq_getD_getElem?]
  · simp [basisArray, basisVec, vecOfArray, Array.getD_eq_getD_getElem?, h]

private lemma arrayOfVec_basisVec (i : Idx) :
    arrayOfVec (basisVec i) = basisArray i := by
  classical
  apply Array.ext_getElem?
  intro j
  simp [arrayOfVec, basisArray, basisVec, Array.getElem?_ofFn]

private def specLin : Vec →ₗ[F] Vec :=
  (quadSpecMatrix : Matrix Idx Idx F).mulVecLin

private lemma vecOfArray_quadraticSpec (a : Array F) :
    vecOfArray (quadraticSpec a) = (quadSpecMatrix.mulVec (vecOfArray a)) := by
  have hvec : (fun t : Idx => a[t.val]?.getD 0) = vecOfArray a := by
    funext t
    simp [vecOfArray, Array.getD_eq_getD_getElem?]
  funext j
  have hj : j.val < 256 := j.isLt
  have hL :
      vecOfArray (quadraticSpec a) j =
        quadSpecMatrix.mulVec (fun t : Idx => a[t.val]?.getD 0) j := by
    simp [vecOfArray, quadraticSpec, Array.getD_eq_getD_getElem?, hj]
  simpa [hvec] using hL

private lemma vecOfArray_nttIterative (a : Array F) (ha : a.size = 256) :
    vecOfArray (nttIterative a ha) = specLin (vecOfArray a) := by
  have h := nttIterative_matches_quadraticSpec_proved a ha
  -- Rewrite to the spec and view both sides as vectors.
  have : vecOfArray (nttIterative a ha) = vecOfArray (quadraticSpec a) :=
    congrArg vecOfArray h
  simpa [specLin] using this.trans (vecOfArray_quadraticSpec a)

private def invOpFun (inv2 : F) (op : InverseOp) (v : Vec) : Vec :=
  fun i =>
    if i = op.i1 then
      inv2 * (v op.i1 + v op.i2)
    else if i = op.i2 then
      (inv2 * op.zkInv) * (v op.i1 - v op.i2)
    else
      v i

private def invOpLin (inv2 : F) (op : InverseOp) : Vec →ₗ[F] Vec where
  toFun v := invOpFun inv2 op v
  map_add' v w := by
    ext i
    by_cases h1 : i = op.i1
    · subst h1
      simp [invOpFun]
      ring
    · by_cases h2 : i = op.i2
      · subst h2
        simp [invOpFun, h1]
        ring
      · simp [invOpFun, h1, h2]
  map_smul' c v := by
    ext i
    by_cases h1 : i = op.i1
    · subst h1
      simp [invOpFun]
      ring
    · by_cases h2 : i = op.i2
      · subst h2
        simp [invOpFun, h1]
        ring
      · simp [invOpFun, h1, h2]

private def execInvVec (inv2 : F) : List InverseOp → Vec → Vec
  | [], v => v
  | op :: ops, v => execInvVec inv2 ops (invOpLin inv2 op v)

private lemma execInvVec_add (inv2 : F) (ops : List InverseOp) (v w : Vec) :
    execInvVec inv2 ops (v + w) = execInvVec inv2 ops v + execInvVec inv2 ops w := by
  induction ops generalizing v w with
  | nil => simp [execInvVec]
  | cons op ops ih =>
      simp [execInvVec, ih, (invOpLin inv2 op).map_add]

private lemma execInvVec_smul (inv2 : F) (ops : List InverseOp) (c : F) (v : Vec) :
    execInvVec inv2 ops (c • v) = c • execInvVec inv2 ops v := by
  induction ops generalizing v with
  | nil => simp [execInvVec]
  | cons op ops ih =>
      simp [execInvVec, ih, (invOpLin inv2 op).map_smul]

private def inttLin : Vec →ₗ[F] Vec where
  toFun v := execInvVec ((2 : F)⁻¹) inverseOps v
  map_add' v w := by simpa using execInvVec_add ((2 : F)⁻¹) inverseOps v w
  map_smul' c v := by simpa using execInvVec_smul ((2 : F)⁻¹) inverseOps c v

private lemma vecOfArray_applyInverseOp256 (inv2 : F) (a : Array F) (ha : a.size = 256) (op : InverseOp) :
    vecOfArray (applyInverseOp256 inv2 a ha op) = invOpLin inv2 op (vecOfArray a) := by
  classical
  funext i
  -- Expand the definition: two `set`s, so only `i1` and `i2` change.
  by_cases h1 : i = op.i1
  · subst h1
    -- At `i1`, we see `inv2*(u+v)`.
    simp [applyInverseOp256, vecOfArray, invOpLin, invOpFun, Array.getD_eq_getD_getElem?, ha]
  · by_cases h2 : i = op.i2
    · subst h2
      have hne : (op.i1.val : Nat) ≠ op.i2.val := by
        intro h
        apply h1
        exact Fin.ext h.symm
      simp [applyInverseOp256, vecOfArray, invOpLin, invOpFun, Array.getD_eq_getD_getElem?, ha, h1, hne]
    ·
      have hne1 : (op.i1.val : Nat) ≠ i.val := by
        intro h
        apply h1
        exact Fin.ext h.symm
      have hne2 : (op.i2.val : Nat) ≠ i.val := by
        intro h
        apply h2
        exact Fin.ext h.symm
      simp [applyInverseOp256, vecOfArray, invOpLin, invOpFun, Array.getD_eq_getD_getElem?, ha, h1, h2, hne1, hne2]

private lemma vecOfArray_applyInverseOps256 (inv2 : F) (ops : List InverseOp) (a : Array F) (ha : a.size = 256) :
    vecOfArray (applyInverseOps256 inv2 ops a ha) = execInvVec inv2 ops (vecOfArray a) := by
  classical
  induction ops generalizing a with
  | nil =>
      simp [NTTIterative.applyInverseOps256, execInvVec]
  | cons op ops ih =>
      simp [NTTIterative.applyInverseOps256, execInvVec, ih,
        vecOfArray_applyInverseOp256 (inv2 := inv2) (a := a) (ha := ha) (op := op)]

private lemma vecOfArray_inttIterative (a : Array F) (ha : a.size = 256) :
    vecOfArray (inttIterative a ha) = inttLin (vecOfArray a) := by
  -- `inttIterative` is `applyInverseOps256` specialized to `inverseOps`.
  simpa [inttIterative, inttLin] using
    (vecOfArray_applyInverseOps256 (inv2 := ((2 : F)⁻¹)) (ops := inverseOps) (a := a) (ha := ha))

private lemma inttLin_specLin_id :
    (inttLin.comp specLin) = LinearMap.id := by
  classical
  -- Basis-vector extensionality on linear maps `Vec →ₗ Vec`.
  apply (Pi.basisFun F Idx).ext
  intro i
  -- Use the computed round-trip on the corresponding basis array.
  have hBasis : (basisArray i).size = 256 := by simp [basisArray]
  have hNTTSize : (nttIterative (basisArray i) hBasis).size = 256 :=
    size_nttIterative (a := basisArray i) (ha := hBasis)
  have hArr :
      inttIterative (nttIterative (basisArray i) hBasis) hNTTSize = basisArray i :=
    inttIterative_nttIterative_roundtrip_on_basis i
  have hVec :
      vecOfArray
          (inttIterative
            (nttIterative (basisArray i) hBasis)
            hNTTSize)
        = vecOfArray (basisArray i) := congrArg vecOfArray hArr
  -- Rewrite each side to the corresponding linear maps.
  have hL :
      vecOfArray
          (inttIterative
            (nttIterative (basisArray i) hBasis)
            hNTTSize)
        = inttLin (specLin (basisVec i)) := by
    -- Left: `inttIterative` vector view.
    have h1 :=
      vecOfArray_inttIterative
        (a := nttIterative (basisArray i) hBasis)
        (ha := hNTTSize)
    -- Right: `nttIterative` vector view.
    have h2 :=
      vecOfArray_nttIterative (a := basisArray i) (ha := hBasis)
    -- Convert `vecOfArray (basisArray i)` into the basis vector.
    simpa [basisVec, vecOfArray_basisArray, h2, specLin] using h1
  have hR : vecOfArray (basisArray i) = basisVec i := vecOfArray_basisArray i
  have hFinal : inttLin (specLin (basisVec i)) = basisVec i := by
    -- Combine `hVec` with the two rewrites.
    simpa [hL, hR] using hVec
  have hFinal' : inttLin (specLin (Pi.single i (1 : F))) = Pi.single i (1 : F) := by
    simpa [basisVec_eq_piSingle] using hFinal
  simpa [Pi.basisFun_apply] using hFinal'

theorem inttIterative_nttIterative_id :
    ∀ (a : Array F) (ha : a.size = 256),
      inttIterative (nttIterative a ha) (size_nttIterative (a := a) (ha := ha)) = a := by
  intro a ha
  have hNTTSize : (nttIterative a ha).size = 256 := size_nttIterative (a := a) (ha := ha)
  -- Compare via vector views, using the linear-map identity.
  have hvec :
      vecOfArray (inttIterative (nttIterative a ha) hNTTSize) = vecOfArray a := by
    have h1 :=
      vecOfArray_nttIterative (a := a) (ha := ha)
    have h2 :=
      vecOfArray_inttIterative (a := nttIterative a ha) (ha := hNTTSize)
    have hid : inttLin (specLin (vecOfArray a)) = vecOfArray a := by
      have := congrArg (fun L => L (vecOfArray a)) inttLin_specLin_id
      simpa using this
    simpa [h1, h2] using hid
  have hsize : (inttIterative (nttIterative a ha) hNTTSize).size = 256 :=
    size_inttIterative (a := nttIterative a ha) (ha := hNTTSize)
  exact array_eq_of_vecOfArray_eq
    (a := inttIterative (nttIterative a ha) hNTTSize)
    (b := a)
    (ha := hsize)
    (hb := ha)
    hvec

theorem nttIterative_inttIterative_id :
    ∀ (t : Array F) (ht : t.size = 256),
      nttIterative (inttIterative t ht) (size_inttIterative (a := t) (ha := ht)) = t := by
  intro t ht
  have hInttSize : (inttIterative t ht).size = 256 := size_inttIterative (a := t) (ha := ht)
  -- Use the same linearity argument, but with the other basis round-trip.
  -- First show `specLin ∘ inttLin = id` by basis extensionality.
  have hid : (specLin.comp inttLin) = LinearMap.id := by
    classical
    apply (Pi.basisFun F Idx).ext
    intro i
    have hBasis : (basisArray i).size = 256 := by simp [basisArray]
    have hInttSizeBasis : (inttIterative (basisArray i) hBasis).size = 256 :=
      size_inttIterative (a := basisArray i) (ha := hBasis)
    have hArr :
        nttIterative (inttIterative (basisArray i) hBasis) hInttSizeBasis = basisArray i :=
      nttIterative_inttIterative_roundtrip_on_basis i
    have hVec :
        vecOfArray
            (nttIterative (inttIterative (basisArray i) hBasis) hInttSizeBasis)
          = vecOfArray (basisArray i) := congrArg vecOfArray hArr
    have hL :
        vecOfArray
            (nttIterative (inttIterative (basisArray i) hBasis) hInttSizeBasis)
          = specLin (inttLin (basisVec i)) := by
      have h1 :=
        vecOfArray_nttIterative
          (a := inttIterative (basisArray i) hBasis)
          (ha := hInttSizeBasis)
      have h2 :=
        vecOfArray_inttIterative (a := basisArray i) (ha := hBasis)
      simpa [basisVec, vecOfArray_basisArray, h2] using h1
    have hR : vecOfArray (basisArray i) = basisVec i := vecOfArray_basisArray i
    have hFinal : specLin (inttLin (basisVec i)) = basisVec i := by
      simpa [hL, hR] using hVec
    have hFinal' : specLin (inttLin (Pi.single i (1 : F))) = Pi.single i (1 : F) := by
      simpa [basisVec_eq_piSingle] using hFinal
    simpa [Pi.basisFun_apply] using hFinal'
  have hvec :
      vecOfArray (nttIterative (inttIterative t ht) hInttSize) = vecOfArray t := by
    have h1 := vecOfArray_inttIterative (a := t) (ha := ht)
    have h2 := vecOfArray_nttIterative (a := inttIterative t ht) (ha := hInttSize)
    have hid' : specLin (inttLin (vecOfArray t)) = vecOfArray t := by
      have h0 := congrArg (fun L => L (vecOfArray t)) hid
      -- `LinearMap.id` evaluates to the input.
      simpa [LinearMap.comp_apply] using h0
    simpa [h1, h2] using hid'
  have hsize : (nttIterative (inttIterative t ht) hInttSize).size = 256 :=
    size_nttIterative (a := inttIterative t ht) (ha := hInttSize)
  exact array_eq_of_vecOfArray_eq
    (a := nttIterative (inttIterative t ht) hInttSize)
    (b := t)
    (ha := hsize)
    (hb := ht)
    hvec

/-!
## Task 5: NTT multiplication = negacyclic multiplication in `Rq`

We define a canonical “negacyclic convolution” as the coefficient array of the monic remainder of
`poly256 a * poly256 b` modulo `X^256 + 1`. This is the canonical representative of multiplication
in the quotient ring `Rq = K[X] ⧸ ⟨X^256 + 1⟩`.

Then we prove that the NTT-based multiplication pipeline (`nttIterative` → `basemul` → `inttIterative`)
computes the same canonical representative.
-/

namespace Task5

open scoped BigOperators Polynomial
open Polynomial

open NTTCorrectness
open NTTLoopInvariants
open NTTSpecCRTBridge
open NTTSpecCRTBridge.Index
open NTTCRTBridge
open NTTCRTBridge.Quad

abbrev K : Type := NTTCorrectness.K
abbrev R : Type := NTTCorrectness.R
abbrev Rq : Type := NTTCorrectness.Rq
abbrev NTTDomain : Type := NTTCorrectness.NTTDomain

private noncomputable def modulusPoly : R :=
  (X ^ (256 : Nat) + 1 : R)

private lemma modulusPoly_monic : (modulusPoly : R).Monic := by
  -- `X^256 + 1` is monic.
  simpa [modulusPoly] using
    (Polynomial.monic_X_pow_add_C (R := K) (a := (1 : K)) (n := 256) (by decide : (256 : Nat) ≠ 0))

private noncomputable def rqOfArray (a : Array K) : Rq :=
  Ideal.Quotient.mk _ (Split.poly256 a)

private noncomputable def pairPoly (a0 a1 : K) : R :=
  C a0 + C a1 * X

private lemma coeff_poly256 (a : Array K) (n : Nat) :
    (Split.poly256 a).coeff n = if n < 256 then a.getD n 0 else 0 := by
  classical
  have hsum :
      (Split.poly256 a).coeff n =
        ∑ j : Fin 256, (if n = j.val then a.getD j.val 0 else 0) := by
    simp [Split.poly256]
    rfl
  by_cases hn : n < 256
  · let i : Fin 256 := ⟨n, hn⟩
    have hsingle :
        (∑ j : Fin 256, if n = j.val then a.getD j.val 0 else 0) = a.getD n 0 := by
      classical
      refine (Fintype.sum_eq_single i ?_).trans ?_
      · intro j hj
        have hn' : n ≠ j.val := by
          intro hnj
          apply hj
          exact Fin.ext (by simpa [i] using hnj.symm)
        simp [hn']
      · simp [i]
    simpa [hsum, hn] using hsingle
  · have hne : ∀ j : Fin 256, n ≠ j.val := by
      intro j hnj
      exact hn (hnj ▸ j.isLt)
    have : (∑ j : Fin 256, if n = j.val then a.getD j.val 0 else 0) = 0 := by
      classical
      simp [hne]
    simpa [hsum, hn] using this

private lemma poly256_eq_of_coeff_eq (a b : Array K)
    (h : ∀ n, (Split.poly256 a).coeff n = (Split.poly256 b).coeff n) :
    Split.poly256 a = Split.poly256 b := by
  ext n
  exact h n

private lemma array_eq_of_poly256_eq (a b : Array K) (ha : a.size = 256) (hb : b.size = 256)
    (h : Split.poly256 a = Split.poly256 b) : a = b := by
  classical
  apply Array.ext_getElem?
  intro i
  by_cases hi : i < 256
  · have hiA : i < a.size := by simpa [ha] using hi
    have hiB : i < b.size := by simpa [hb] using hi
    have hcoeff :
        (Split.poly256 a).coeff i = (Split.poly256 b).coeff i := by
      simpa using congrArg (fun p : R => p.coeff i) h
    have haCoeff : (Split.poly256 a).coeff i = a.getD i 0 := by
      simp [coeff_poly256, hi]
    have hbCoeff : (Split.poly256 b).coeff i = b.getD i 0 := by
      simp [coeff_poly256, hi]
    have habD : a.getD i 0 = b.getD i 0 := by
      simpa [haCoeff, hbCoeff] using hcoeff
    have hab : a[i] = b[i] := by
      -- In-bounds indices, `getD` agrees with `getElem`.
      have hDa : a.getD i 0 = a[i] := by
        simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hiA]
      have hDb : b.getD i 0 = b[i] := by
        simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hiB]
      simpa [hDa, hDb] using habD
    simp [Array.getElem?_eq_getElem hiA, Array.getElem?_eq_getElem hiB, hab]
  · have hleA : a.size ≤ i := by
      rw [ha]
      exact Nat.le_of_not_gt hi
    have hleB : b.size ≤ i := by
      rw [hb]
      exact Nat.le_of_not_gt hi
    simp [Array.getElem?_eq_none hleA, Array.getElem?_eq_none hleB]

private lemma poly256_eq_of_rqOfArray_eq (a b : Array K) (h : rqOfArray a = rqOfArray b) :
    Split.poly256 a = Split.poly256 b := by
  -- In the quotient, equality means `p - q ∈ ⟨X^256+1⟩`, hence divisibility by `X^256+1`.
  have hmem : (Split.poly256 a - Split.poly256 b) ∈ (Ideal.span ({(X ^ (256 : Nat) + 1 : R)} : Set R)) := by
    -- `Ideal.Quotient.eq` is the defining equivalence relation.
    simpa [rqOfArray] using (Ideal.Quotient.eq.mp h)
  rcases (Ideal.mem_span_singleton.mp hmem) with ⟨r, hr⟩
  have hdvd : (modulusPoly : R) ∣ (Split.poly256 a - Split.poly256 b) := by
    refine ⟨r, ?_⟩
    -- `hr : r * (X^256+1) = p - q`
    simpa [modulusPoly, mul_comm, mul_left_comm, mul_assoc] using hr
  -- The LHS has degree `< 256` (all coefficients above `255` are zero), so the only multiple is zero.
  have hdeg :
      degree (Split.poly256 a - Split.poly256 b) < (256 : WithBot Nat) := by
    -- Use the coefficient characterization of degree.
    have hcoeff : ∀ m : Nat, 256 ≤ m → (Split.poly256 a - Split.poly256 b).coeff m = 0 := by
      intro m hm
      have hma : ¬m < 256 := Nat.not_lt_of_ge hm
      have hmb : ¬m < 256 := Nat.not_lt_of_ge hm
      -- Coefficients of each `poly256` vanish for `m ≥ 256`.
      have ha0 : (Split.poly256 a).coeff m = 0 := by
        simp [coeff_poly256, hma]
      have hb0 : (Split.poly256 b).coeff m = 0 := by
        simp [coeff_poly256, hmb]
      simp [Polynomial.coeff_sub, ha0, hb0]
    -- Translate to a `degree` bound.
    have : degree (Split.poly256 a - Split.poly256 b) < 256 := by
      exact (Polynomial.degree_lt_iff_coeff_zero (f := (Split.poly256 a - Split.poly256 b)) (n := 256)).2 hcoeff
    simpa using this
  have hdegMod : degree (modulusPoly : R) = 256 := by
    -- `X^256 + 1` has degree 256.
    simpa [modulusPoly] using (Polynomial.degree_X_pow_add_C (R := K) (n := 256) (a := (1 : K)) (by decide : 0 < (256 : Nat)))
  have hzero : (Split.poly256 a - Split.poly256 b) = 0 :=
    Polynomial.eq_zero_of_dvd_of_degree_lt (p := modulusPoly) (q := (Split.poly256 a - Split.poly256 b))
      hdvd (by simpa [hdegMod] using hdeg)
  exact sub_eq_zero.mp hzero

private noncomputable def coeffArray256 (p : R) : Array K :=
  Array.ofFn (fun i : Fin 256 => p.coeff i.val)

private lemma poly256_coeffArray256_eq (p : R) (hp : degree p < (256 : WithBot Nat)) :
    Split.poly256 (coeffArray256 p) = p := by
  classical
  ext n
  by_cases hn : n < 256
  · have : (Split.poly256 (coeffArray256 p)).coeff n = (coeffArray256 p).getD n 0 := by
      simp [coeff_poly256, hn]
    have hget : (coeffArray256 p).getD n 0 = p.coeff n := by
      simp [coeffArray256, Array.getD_eq_getD_getElem?, hn]
    simp [this, hget]
  · have hn' : 256 ≤ n := Nat.le_of_not_gt hn
    have hcoeff0 : p.coeff n = 0 := by
      -- Coefficients vanish above the degree bound.
      have := (Polynomial.degree_lt_iff_coeff_zero (f := p) (n := 256)).1 hp n hn'
      simpa using this
    have hpoly0 : (Split.poly256 (coeffArray256 p)).coeff n = 0 := by
      simp [coeff_poly256, hn]
    simp [hpoly0, hcoeff0]

noncomputable def negacyclicConv (a b : Array K) (ha : a.size = 256) (hb : b.size = 256) : Array K :=
  let _ := ha; let _ := hb
  let p : R := Split.poly256 a * Split.poly256 b
  let r : R := p %ₘ modulusPoly
  coeffArray256 r

private lemma rqOfArray_negacyclicConv (a b : Array K) (ha : a.size = 256) (hb : b.size = 256) :
    rqOfArray (negacyclicConv a b ha hb) = rqOfArray a * rqOfArray b := by
  classical
  -- Unfold the definition and replace `poly256 (coeffArray256 r)` by `r` (since `r` has degree < 256).
  dsimp [negacyclicConv, rqOfArray]
  set p : R := Split.poly256 a * Split.poly256 b
  set r : R := p %ₘ modulusPoly
  have hr : degree r < (256 : WithBot Nat) := by
    -- `deg (p %ₘ q) < deg q` for monic `q`, and `deg (X^256+1) = 256`.
    have hlt : degree r < degree (modulusPoly : R) := by
      simpa [r] using (Polynomial.degree_modByMonic_lt (p := p) (q := modulusPoly) modulusPoly_monic)
    have hdegQ : degree (modulusPoly : R) = 256 := by
      simpa [modulusPoly] using
        (Polynomial.degree_X_pow_add_C (R := K) (n := 256) (a := (1 : K)) (by decide : 0 < (256 : Nat)))
    simpa [hdegQ] using hlt
  have hpoly : Split.poly256 (coeffArray256 r) = r := poly256_coeffArray256_eq (p := r) hr
  -- Convert `mk r = mk p` in the quotient using `r = p - q*(p/ₘ q)`.
  have hmk : (Ideal.Quotient.mk (Ideal.span ({modulusPoly} : Set R)) r : Rq) =
      Ideal.Quotient.mk (Ideal.span ({modulusPoly} : Set R)) p := by
    -- Show `r - p ∈ ⟨q⟩`, where `q = X^256+1`.
    refine (Ideal.Quotient.eq).2 ?_
    have hrdef : r = p - modulusPoly * (p /ₘ modulusPoly) := by
      simpa [r] using (Polynomial.modByMonic_eq_sub_mul_div (p := p) (q := modulusPoly) modulusPoly_monic)
    have hsub : r - p = -(modulusPoly * (p /ₘ modulusPoly)) := by
      -- `r - p = (p - q*div) - p`.
      simp [hrdef, sub_eq_add_neg, add_left_comm, add_comm]
    refine Ideal.mem_span_singleton.2 ?_
    refine ⟨-(p /ₘ modulusPoly), ?_⟩
    -- `(-div) * q = -(q * div)`.
    simp [hsub]
  -- Finish: `mk (poly256 (coeffArray256 r)) = mk p`.
  simpa [hpoly, p, r] using hmk

/-!
### Algebraic interpretation of `nttIterative` output

We interpret a length-256 NTT output array as an element of the CRT product ring `NTTDomain` by
pairing indices `(2i, 2i+1)` as `a0 + a1*X` in each factor `K[X]/(X^2-μ)`.
-/

private noncomputable def indexOfMu (μ : NTTCorrectness.roots256) : Fin 128 :=
  Classical.choose (Mu.muByIndex_surjective_roots256 (μ := (μ : K)) μ.property)

private lemma muByIndex_indexOfMu (μ : NTTCorrectness.roots256) :
    Mu.muByIndex (indexOfMu μ) = (μ : K) :=
  Classical.choose_spec (Mu.muByIndex_surjective_roots256 (μ := (μ : K)) μ.property)

private noncomputable def nttDomainOfArray (y : Array K) : NTTDomain :=
  fun μ =>
    let i := indexOfMu μ
    Ideal.Quotient.mk _ (pairPoly (y.getD (2 * i.val) 0) (y.getD (2 * i.val + 1) 0))

private lemma NTT_mk (p : R) (μ : NTTCorrectness.roots256) :
    NTTCorrectness.NTT (Ideal.Quotient.mk _ p : Rq) μ =
      Ideal.Quotient.mk (NTTCorrectness.quadIdeal (μ : K)) p := by
  classical
  -- Unfold the CRT ring equivalence and use the canonical component map.
  simp [NTTCorrectness.NTT, NTTCorrectness.nttEquiv, NTTCorrectness.Rq, NTTCorrectness.NTTDomain,
    Ideal.quotEquivOfEq_mk, Ideal.quotientInfRingEquivPiQuotient, Ideal.quotientInfToPiQuotient_mk']

private lemma nttDomainOfArray_quadraticSpec_eq_NTT (a : Array K) :
    nttDomainOfArray (quadraticSpec a) = NTTCorrectness.NTT (rqOfArray a) := by
  classical
  funext μ
  let i : Fin 128 := indexOfMu μ
  have hμ : Mu.muByIndex i = (μ : K) := muByIndex_indexOfMu μ
  -- Right side: `NTT` reduces to `mk (poly256 a)` in each factor.
  have hNTT : NTTCorrectness.NTT (rqOfArray a) μ =
      Ideal.Quotient.mk (quadIdeal (μ : K)) (Split.poly256 a) := by
    simpa [rqOfArray] using (NTT_mk (p := Split.poly256 a) (μ := μ))
  -- `mk_poly256_eq_quadraticSpec` gives the degree-1 remainder in the factor ring.
  have hfactor :
      Ideal.Quotient.mk (quadIdeal (Mu.muByIndex i)) (Split.poly256 a) =
        Ideal.Quotient.mk (quadIdeal (Mu.muByIndex i))
          (pairPoly ((quadraticSpec a).getD (2 * i.val) 0) ((quadraticSpec a).getD (2 * i.val + 1) 0)) := by
    simpa [pairPoly, even256_val, odd256_val] using
      (NTTSpecCRTBridge.CRT.mk_poly256_eq_quadraticSpec (a := a) (i := i))
  -- Transport `hfactor` to the quotient ring indexed by `μ`.
  have hEqIdeal : quadIdeal (Mu.muByIndex i) = quadIdeal (μ : K) := by
    simp [hμ]
  have hfactor' :
      Ideal.Quotient.mk (quadIdeal (μ : K)) (Split.poly256 a) =
        Ideal.Quotient.mk (quadIdeal (μ : K))
          (pairPoly ((quadraticSpec a).getD (2 * i.val) 0) ((quadraticSpec a).getD (2 * i.val + 1) 0)) := by
    have := congrArg (Ideal.quotEquivOfEq hEqIdeal) hfactor
    simpa [Ideal.quotEquivOfEq_mk] using this
  -- Rewrite the RHS via `hNTT`, then unfold the LHS.
  rw [hNTT]
  dsimp [nttDomainOfArray, i]
  exact hfactor'.symm

private lemma nttDomainOfArray_nttIterative_eq_NTT (a : Array K) (ha : a.size = 256) :
    nttDomainOfArray (nttIterative a ha) = NTTCorrectness.NTT (rqOfArray a) := by
  have hqs := nttIterative_matches_quadraticSpec_proved a ha
  simpa [hqs] using (nttDomainOfArray_quadraticSpec_eq_NTT (a := a))

set_option maxHeartbeats 20000000 in
private lemma nttDomainOfArray_basemul (y1 y2 : Array K) (hy1 : y1.size = 256) (hy2 : y2.size = 256) :
    nttDomainOfArray (basemul y1 y2 hy1 hy2) = nttDomainOfArray y1 * nttDomainOfArray y2 := by
  classical
  funext μ
  let i : Fin 128 := indexOfMu μ
  have hμ : Mu.muByIndex i = (μ : K) := muByIndex_indexOfMu μ
  have hμalg : NTTIterative.muForPairIndex i = (μ : K) := by
    -- `muForPairIndex` matches the `Mu.muByIndex` ordering definitionally.
    simpa [NTTIterative.muForPairIndex, Mu.muByIndex] using hμ
  -- Extract the pair coefficients (use `getD`, since indices are in-bounds).
  set a0 : K := y1.getD (2 * i.val) 0
  set a1 : K := y1.getD (2 * i.val + 1) 0
  set b0 : K := y2.getD (2 * i.val) 0
  set b1 : K := y2.getD (2 * i.val + 1) 0
  -- Compute the output coefficients from `basemul`.
  have hEven0 :
      (basemul y1 y2 hy1 hy2).getD (2 * i.val) 0 =
        (basemulPair a0 a1 b0 b1 (NTTIterative.muForPairIndex i)).1 := by
    -- Avoid unfolding `Array.ofFn`; use the dedicated projection lemma.
    simpa [NTTIterative.basemulPairAt, a0, a1, b0, b1] using
      (NTTIterative.basemul_getD_even (a := y1) (b := y2) (ha := hy1) (hb := hy2) (i := i))
  have hOdd0 :
      (basemul y1 y2 hy1 hy2).getD (2 * i.val + 1) 0 =
        (basemulPair a0 a1 b0 b1 (NTTIterative.muForPairIndex i)).2 := by
    -- Avoid unfolding `Array.ofFn`; use the dedicated projection lemma.
    simpa [NTTIterative.basemulPairAt, a0, a1, b0, b1] using
      (NTTIterative.basemul_getD_odd (a := y1) (b := y2) (ha := hy1) (hb := hy2) (i := i))
  have hEven :
      (basemul y1 y2 hy1 hy2).getD (2 * i.val) 0 = (basemulPair a0 a1 b0 b1 (μ : K)).1 := by
    simpa [hμalg] using hEven0
  have hOdd :
      (basemul y1 y2 hy1 hy2).getD (2 * i.val + 1) 0 = (basemulPair a0 a1 b0 b1 (μ : K)).2 := by
    simpa [hμalg] using hOdd0
  -- Reduce both sides to a statement in the quotient ring for `μ`.
  dsimp [nttDomainOfArray, i]
  have hMul :
      Ideal.Quotient.mk (quadIdeal (μ : K)) (pairPoly a0 a1) *
          Ideal.Quotient.mk (quadIdeal (μ : K)) (pairPoly b0 b1) =
        Ideal.Quotient.mk (quadIdeal (μ : K))
          (pairPoly (basemulPair a0 a1 b0 b1 (μ : K)).1 (basemulPair a0 a1 b0 b1 (μ : K)).2) := by
    simpa [pairPoly, NTTIterative.basemulPair] using
      (basemulPair_eq_quotient_mul (a0 := a0) (a1 := a1) (b0 := b0) (b1 := b1) (μ := (μ : K)))
  -- Rewrite the LHS coefficients to the quadratic-factor multiplication outputs, then apply `hMul`.
  rw [hEven, hOdd]
  exact hMul.symm

private lemma rqOfArray_inttIterative_eq_invNTT (y : Array K) (hy : y.size = 256) :
    rqOfArray (inttIterative y hy) = invNTT (nttDomainOfArray y) := by
  classical
  -- Use `y = nttIterative (inttIterative y)` and the established interpretation of `nttIterative`.
  have hy' : (inttIterative y hy).size = 256 := by
    simpa using (size_inttIterative (a := y) (ha := hy))
  have hround :
      nttIterative (inttIterative y hy) hy' = y :=
    nttIterative_inttIterative_id (t := y) (ht := hy)
  -- Interpret both sides in `NTTDomain`.
  have hNTT :
      nttDomainOfArray y = NTTCorrectness.NTT (rqOfArray (inttIterative y hy)) := by
    -- Rewrite `y` as the forward transform of `inttIterative y`.
    simpa [hround] using (nttDomainOfArray_nttIterative_eq_NTT (a := inttIterative y hy) (ha := hy'))
  -- Apply `invNTT` to both sides and simplify.
  have := congrArg invNTT hNTT
  simpa [NTTCorrectness.invNTT_NTT] using this.symm

private lemma rqOfArray_nttMul (a b : Array K) (ha : a.size = 256) (hb : b.size = 256) :
    let nttA := nttIterative a ha
    let nttB := nttIterative b hb
    let nttProd := basemul nttA nttB (size_nttIterative (a := a) (ha := ha)) (size_nttIterative (a := b) (ha := hb))
    let result := inttIterative nttProd (by
      -- `basemul` preserves size.
      simp [nttProd, NTTIterative.basemul])
    rqOfArray result = rqOfArray a * rqOfArray b := by
  classical
  intro nttA nttB nttProd result
  have hnttA : nttDomainOfArray nttA = NTTCorrectness.NTT (rqOfArray a) :=
    nttDomainOfArray_nttIterative_eq_NTT (a := a) (ha := ha)
  have hnttB : nttDomainOfArray nttB = NTTCorrectness.NTT (rqOfArray b) :=
    nttDomainOfArray_nttIterative_eq_NTT (a := b) (ha := hb)
  have hprodSize : nttProd.size = 256 := by
    simp [nttProd, NTTIterative.basemul]
  have hprod : nttDomainOfArray nttProd = nttDomainOfArray nttA * nttDomainOfArray nttB := by
    -- `basemul` is pointwise multiplication in each factor.
    simpa [nttProd] using
      (nttDomainOfArray_basemul (y1 := nttA) (y2 := nttB)
        (hy1 := size_nttIterative (a := a) (ha := ha)) (hy2 := size_nttIterative (a := b) (ha := hb)))
  have hInv : rqOfArray result = invNTT (nttDomainOfArray nttProd) := by
    -- `result` is `inttIterative nttProd`.
    have : rqOfArray (inttIterative nttProd hprodSize) = invNTT (nttDomainOfArray nttProd) :=
      rqOfArray_inttIterative_eq_invNTT (y := nttProd) (hy := hprodSize)
    simpa [result] using this
  -- Combine: invNTT respects multiplication and is inverse to NTT on `Rq`.
  calc
    rqOfArray result
        = invNTT (nttDomainOfArray nttProd) := hInv
    _ = invNTT (nttDomainOfArray nttA * nttDomainOfArray nttB) := by simp [hprod]
    _ = invNTT (NTT (rqOfArray a) * NTT (rqOfArray b)) := by simp [hnttA, hnttB]
    _ = rqOfArray a * rqOfArray b := by simpa using (invNTT_mul (x := rqOfArray a) (y := rqOfArray b))

theorem ntt_mul_correct (a b : Array K) (ha : a.size = 256) (hb : b.size = 256) :
    let nttA := nttIterative a ha
    let nttB := nttIterative b hb
    let nttProd := basemul nttA nttB (size_nttIterative (a := a) (ha := ha)) (size_nttIterative (a := b) (ha := hb))
    let result := inttIterative nttProd (by
      -- `basemul` preserves size.
      simp [nttProd, NTTIterative.basemul])
    result = negacyclicConv a b ha hb := by
  classical
  intro nttA nttB nttProd result
  have hresSize : result.size = 256 := by
    -- `inttIterative` preserves size.
    simpa [result] using (size_inttIterative (a := nttProd) (ha := by simp [nttProd, NTTIterative.basemul]))
  have hnegSize : (negacyclicConv a b ha hb).size = 256 := by
    simp [negacyclicConv, coeffArray256]
  -- Compare in the quotient ring `Rq`.
  have hRq :
      rqOfArray result = rqOfArray (negacyclicConv a b ha hb) := by
    have h1 : rqOfArray result = rqOfArray a * rqOfArray b := by
      simpa [nttA, nttB, nttProd, result] using (rqOfArray_nttMul (a := a) (b := b) (ha := ha) (hb := hb))
    have h2 : rqOfArray (negacyclicConv a b ha hb) = rqOfArray a * rqOfArray b :=
      rqOfArray_negacyclicConv (a := a) (b := b) (ha := ha) (hb := hb)
    simpa [h1] using h2.symm
  have hpoly : Split.poly256 result = Split.poly256 (negacyclicConv a b ha hb) :=
    poly256_eq_of_rqOfArray_eq (a := result) (b := negacyclicConv a b ha hb) hRq
  -- Convert polynomial equality back to arrays.
  exact array_eq_of_poly256_eq (a := result) (b := negacyclicConv a b ha hb) (ha := hresSize) (hb := hnegSize) hpoly

end Task5

end NTTConvolution
end Lattice
end Crypto
end HeytingLean
