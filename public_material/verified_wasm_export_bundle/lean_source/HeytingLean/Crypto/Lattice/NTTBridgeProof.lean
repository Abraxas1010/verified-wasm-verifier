import HeytingLean.Crypto.Lattice.NTTBridge
import HeytingLean.Crypto.Lattice.NTTIterativeBasisAgreement
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

/-!
# Gap 1: proof that the iterative NTT matches the quadratic-factor specification

This file closes the main remaining Gap 1 conjecture for ML-KEM NTT verification:

`NTTIterative.nttIterative` (executable butterfly schedule) computes the same transform as the
quadratic-factor specification `NTTBridge.quadraticSpec` (a matrix over `ZMod 3329` encoding the
`X^2 - μ` factor outputs in the implementation ordering).

Strategy:
- Define the forward NTT as a linear map on vectors `Fin 256 → F` by executing the fixed list of
  butterfly operations.
- Use the previously certified milestone that the algorithm agrees with the quadratic spec on all
  256 basis vectors (proved by `native_decide`).
- Conclude full equality by `Pi.basisFun` extensionality of linear maps.
- Transfer back to `Array F` using `Array.ofFn`/`getD`.
-/

namespace HeytingLean
namespace Crypto
namespace Lattice
namespace NTTBridgeProof

open scoped BigOperators

open HeytingLean.Crypto.Lattice.NTTIterative
open HeytingLean.Crypto.Lattice.NTTBridge
open HeytingLean.Crypto.Lattice.NTTIterativeBasisAgreement

abbrev q : Nat := NTT.q
abbrev F : Type := ZMod q

abbrev Vec : Type := Fin 256 → F

private def vecOfArray (a : Array F) : Vec :=
  fun i => a.getD i.val 0

private def arrayOfVec (v : Vec) : Array F :=
  Array.ofFn v

private lemma vecOfArray_arrayOfVec (v : Vec) : vecOfArray (arrayOfVec v) = v := by
  funext i
  simp [vecOfArray, arrayOfVec, Array.getD_eq_getD_getElem?]

private lemma arrayOfVec_vecOfArray (a : Array F) (ha : a.size = 256) :
    arrayOfVec (vecOfArray a) = a := by
  classical
  apply Array.ext_getElem?
  intro i
  by_cases hi : i < 256
  · have hi' : i < a.size := by simpa [ha] using hi
    -- In bounds: `ofFn` returns the stored value, and `getD` agrees with `getElem?`.
    have : a.getD i 0 = a[i] := by
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi']
    simp [arrayOfVec, vecOfArray, hi, this, Array.getElem?_eq_getElem hi']
  · have hle : a.size ≤ i := by
      have : (256 : Nat) ≤ i := Nat.le_of_not_gt hi
      simpa [ha] using this
    simp [arrayOfVec, hi, Array.getElem?_eq_none hle]

/-!
## The forward NTT as a linear map on vectors
-/

private def forwardOpFun (op : ForwardOp) (v : Vec) : Vec :=
  fun i =>
    if _ : i = op.i1 then
      v op.i1 + op.zk * v op.i2
    else if _ : i = op.i2 then
      v op.i1 - op.zk * v op.i2
    else
      v i

private def forwardOpLin (op : ForwardOp) : Vec →ₗ[F] Vec where
  toFun v := forwardOpFun op v
  map_add' v w := by
    ext i
    by_cases h1 : i = op.i1
    · subst h1
      simp [forwardOpFun]
      ring
    · by_cases h2 : i = op.i2
      · subst h2
        simp [forwardOpFun, h1]
        ring
      · simp [forwardOpFun, h1, h2]
  map_smul' c v := by
    ext i
    by_cases h1 : i = op.i1
    · subst h1
      simp [forwardOpFun]
      ring
    · by_cases h2 : i = op.i2
      · subst h2
        simp [forwardOpFun, h1]
        ring
      · simp [forwardOpFun, h1, h2]

private def execVec : List ForwardOp → Vec → Vec
  | [], v => v
  | op :: ops, v => execVec ops (forwardOpLin op v)

private lemma execVec_nil (v : Vec) : execVec [] v = v := by
  rfl

private lemma execVec_cons (op : ForwardOp) (ops : List ForwardOp) (v : Vec) :
    execVec (op :: ops) v = execVec ops (forwardOpLin op v) := by
  rfl

private lemma execVec_add (ops : List ForwardOp) (v w : Vec) :
    execVec ops (v + w) = execVec ops v + execVec ops w := by
  induction ops generalizing v w with
  | nil => simp [execVec]
  | cons op ops ih =>
      simp [execVec, ih, (forwardOpLin op).map_add]

private lemma execVec_smul (ops : List ForwardOp) (c : F) (v : Vec) :
    execVec ops (c • v) = c • execVec ops v := by
  induction ops generalizing v with
  | nil => simp [execVec]
  | cons op ops ih =>
      simp [execVec, ih, (forwardOpLin op).map_smul]

private def algLin : Vec →ₗ[F] Vec where
  toFun v := execVec forwardOps v
  map_add' v w := by
    simpa using execVec_add forwardOps v w
  map_smul' c v := by
    simpa using execVec_smul forwardOps c v

private def specLin : Vec →ₗ[F] Vec :=
  (quadSpecMatrix : Matrix (Fin 256) (Fin 256) F).mulVecLin

/-!
## Arrays vs vectors: one-step and full-schedule correspondence
-/

private lemma vecOfArray_applyForwardOp (a : Array F) (ha : a.size = 256) (op : ForwardOp) :
    vecOfArray (applyForwardOp a op) = forwardOpLin op (vecOfArray a) := by
  funext i
  set_option linter.unnecessarySimpa false in
    have hi1 : op.i1.val < a.size := by simpa [ha] using op.i1.isLt
  set_option linter.unnecessarySimpa false in
    have hi2 : op.i2.val < a.size := by simpa [ha] using op.i2.isLt
  by_cases h1 : i = op.i1
  · subst h1
    -- The final write is at `i1`, so we see the `(aj + zk*bj)` branch.
    simp [vecOfArray, applyForwardOp, forwardOpFun, forwardOpLin, Array.getD_eq_getD_getElem?,
      Array.size_setIfInBounds, hi1, hi2, -Array.getElem?_eq_getElem]
  · by_cases h2 : i = op.i2
    · subst h2
      -- `i2` is written first and not overwritten (since `i ≠ i1` by `h1`).
      have hne : op.i2.val ≠ op.i1.val := by
        intro h
        apply h1
        exact Fin.ext h
      have hL :
          vecOfArray (applyForwardOp a op) op.i2 =
            vecOfArray a op.i1 - op.zk * vecOfArray a op.i2 := by
        -- Evaluate the updated array at the `i2` index using `getElem?` lemmas.
        simp [vecOfArray, applyForwardOp, Array.getD_eq_getD_getElem?, hne.symm, hi1, hi2,
          -Array.getElem?_eq_getElem]
      -- The `forwardOpLin` computation at `i2` selects the second branch.
      simpa [forwardOpLin, forwardOpFun, h1] using hL
    · -- All other indices are unchanged by the two `setIfInBounds`.
      have hne1 : i.val ≠ op.i1.val := by
        intro h
        apply h1
        exact Fin.ext h
      have hne2 : i.val ≠ op.i2.val := by
        intro h
        apply h2
        exact Fin.ext h
      have hL :
          vecOfArray (applyForwardOp a op) i = vecOfArray a i := by
        simp [vecOfArray, applyForwardOp, Array.getD_eq_getD_getElem?, hne1.symm, hne2.symm, hi1, hi2,
          -Array.getElem?_eq_getElem]
      simpa [forwardOpLin, forwardOpFun, h1, h2] using hL

private lemma vecOfArray_applyForwardOps (ops : List ForwardOp) (a : Array F) (ha : a.size = 256) :
    vecOfArray (applyForwardOps ops a) = execVec ops (vecOfArray a) := by
  classical
  revert a
  induction ops with
  | nil =>
      intro a ha
      simp [applyForwardOps, execVec]
  | cons op ops ih =>
      intro a ha
      have ha' : (applyForwardOp a op).size = 256 := by
        simp [applyForwardOp, ha]
      have ih' := ih (a := applyForwardOp a op) ha'
      have hstep := vecOfArray_applyForwardOp a ha op
      -- `applyForwardOps` unfolds as a `foldl`, so the head step is definitional.
      have hfold : applyForwardOps (op :: ops) a = applyForwardOps ops (applyForwardOp a op) := rfl
      calc
        vecOfArray (applyForwardOps (op :: ops) a)
            = vecOfArray (applyForwardOps ops (applyForwardOp a op)) := by simp [hfold]
        _ = execVec ops (vecOfArray (applyForwardOp a op)) := ih'
        _ = execVec ops (forwardOpLin op (vecOfArray a)) := by
              simpa using congrArg (execVec ops) hstep
        _ = execVec (op :: ops) (vecOfArray a) := by rfl

private lemma vecOfArray_nttIterative (a : Array F) (ha : a.size = 256) :
    vecOfArray (nttIterative a ha) = algLin (vecOfArray a) := by
  have h :
      vecOfArray (nttIterative a ha) = execVec forwardOps (vecOfArray a) := by
    simpa [nttIterative] using vecOfArray_applyForwardOps forwardOps a ha
  have hAlg : execVec forwardOps (vecOfArray a) = algLin (vecOfArray a) := by
    rfl
  exact h.trans hAlg

private lemma vecOfArray_quadraticSpec (a : Array F) :
    vecOfArray (quadraticSpec a) =
      (quadSpecMatrix.mulVec (fun i : Fin 256 => a.getD i.val 0)) := by
  funext i
  simp [quadraticSpec, vecOfArray, Array.getD_eq_getD_getElem?]

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
      have hfold : applyForwardOps (op :: ops) a = applyForwardOps ops (applyForwardOp a op) := rfl
      calc
        (applyForwardOps (op :: ops) a).size
            = (applyForwardOps ops (applyForwardOp a op)).size := by simp [hfold]
        _ = (applyForwardOp a op).size := ih (a := applyForwardOp a op)
        _ = a.size := size_applyForwardOp a op

/-!
## Closing the gap: `nttIterative_matches_quadraticSpec`
-/

theorem nttIterative_matches_quadraticSpec_proved :
    nttIterative_matches_quadraticSpec := by
  classical
  -- First show the underlying linear maps agree by basis extensionality.
  have hLin : algLin = specLin := by
    apply (Pi.basisFun F (Fin 256)).ext
    intro j
    have hbasisArr :
        nttIterative (basisArray j) (by simp [basisArray]) =
          quadraticSpec (basisArray j) :=
      nttIterative_eq_quadraticSpec_on_basis j
    have hbasisVec : vecOfArray (basisArray j) = Pi.single j (1 : F) := by
      funext i
      by_cases h : i = j
      · subst h
        simp [basisArray, vecOfArray, Array.getD_eq_getD_getElem?]
      · simp [basisArray, vecOfArray, Array.getD_eq_getD_getElem?, h]
    have hsz : (basisArray j).size = 256 := by simp [basisArray]
    have hEqVec :
        vecOfArray (nttIterative (basisArray j) (by simp [basisArray])) =
          vecOfArray (quadraticSpec (basisArray j)) :=
      congrArg vecOfArray hbasisArr
    have hL :
        vecOfArray (nttIterative (basisArray j) (by simp [basisArray])) =
          algLin (Pi.single j (1 : F)) := by
      have hL' :
          vecOfArray (nttIterative (basisArray j) hsz) =
            algLin (vecOfArray (basisArray j)) :=
        vecOfArray_nttIterative (basisArray j) hsz
      simpa [hbasisVec] using hL'
    have hR :
        vecOfArray (quadraticSpec (basisArray j)) =
          specLin (Pi.single j (1 : F)) := by
      have hR' :
          vecOfArray (quadraticSpec (basisArray j)) =
            quadSpecMatrix.mulVec (vecOfArray (basisArray j)) := by
        exact vecOfArray_quadraticSpec (basisArray j)
      simpa [specLin, hbasisVec] using hR'
    have hvecEq : algLin (Pi.single j (1 : F)) = specLin (Pi.single j (1 : F)) := by
      calc
        algLin (Pi.single j (1 : F)) =
            vecOfArray (nttIterative (basisArray j) (by simp [basisArray])) := by
              simpa using hL.symm
        _ = vecOfArray (quadraticSpec (basisArray j)) := hEqVec
        _ = specLin (Pi.single j (1 : F)) := hR
    simpa [Pi.basisFun_apply] using hvecEq

  -- Now transfer equality back to arrays.
  intro a ha
  have hsz1 : (nttIterative a ha).size = 256 := by
    -- `applyForwardOp` preserves size, so the fold does too.
    have hsz : (applyForwardOps forwardOps a).size = a.size :=
      size_applyForwardOps forwardOps a
    dsimp [nttIterative]
    simpa [ha] using hsz
  have hsz2 : (quadraticSpec a).size = 256 := by
    simp [quadraticSpec]
  -- Compare via their vector views.
  have hvec :
      vecOfArray (nttIterative a ha) = vecOfArray (quadraticSpec a) := by
    have h1 : vecOfArray (nttIterative a ha) = algLin (vecOfArray a) :=
      vecOfArray_nttIterative a ha
    have h2 : vecOfArray (quadraticSpec a) = specLin (vecOfArray a) := by
      have h0 := vecOfArray_quadraticSpec a
      have h0' : vecOfArray (quadraticSpec a) = quadSpecMatrix.mulVec (vecOfArray a) :=
        vecOfArray_quadraticSpec a
      simpa [specLin] using h0'
    have h12 : algLin (vecOfArray a) = specLin (vecOfArray a) := by
      simpa using congrArg (fun f => f (vecOfArray a)) hLin
    exact h1.trans (h12.trans h2.symm)
  -- Conclude by extensionality on `getElem?`, treating `b` and `c` as variables to avoid
  -- unfolding the NTT definition during simplification.
  classical
  generalize hb : nttIterative a ha = b
  generalize hc : quadraticSpec a = c
  have hbsize : b.size = 256 := by simpa [hb] using hsz1
  have hcsize : c.size = 256 := by simpa [hc] using hsz2
  have hvec' : vecOfArray b = vecOfArray c := by simpa [hb, hc] using hvec
  have hbc : b = c := by
    apply Array.ext_getElem?
    intro i
    by_cases hi : i < 256
    · have hiB : i < b.size := by simpa [hbsize] using hi
      have hiC : i < c.size := by simpa [hcsize] using hi
      have hD : b.getD i 0 = c.getD i 0 := by
        have h' := congrArg (fun f => f ⟨i, hi⟩) hvec'
        simpa [vecOfArray] using h'
      have hx : b[i]? = some (b.getD i 0) := by
        have hb : b[i]? = some b[i] := Array.getElem?_eq_getElem hiB
        have hbD : b.getD i 0 = b[i] := by
          simp [Array.getD_eq_getD_getElem?, hb]
        simp [hbD, hb]
      have hy : c[i]? = some (c.getD i 0) := by
        have hc : c[i]? = some c[i] := Array.getElem?_eq_getElem hiC
        have hcD : c.getD i 0 = c[i] := by
          simp [Array.getD_eq_getD_getElem?, hc]
        simp [hcD, hc]
      calc
        b[i]? = some (b.getD i 0) := hx
        _ = some (c.getD i 0) := by simp [hD]
        _ = c[i]? := hy.symm
    · have hle : (256 : Nat) ≤ i := Nat.le_of_not_gt hi
      have hleB : b.size ≤ i := by simpa [hbsize] using hle
      have hleC : c.size ≤ i := by simpa [hcsize] using hle
      simp [Array.getElem?_eq_none hleB, Array.getElem?_eq_none hleC]
  simpa [hb, hc] using hbc

end NTTBridgeProof
end Lattice
end Crypto
end HeytingLean
