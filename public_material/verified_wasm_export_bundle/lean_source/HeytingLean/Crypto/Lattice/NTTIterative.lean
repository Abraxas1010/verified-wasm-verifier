import HeytingLean.Crypto.Lattice.NTT
import Init.Data.Array.Lemmas
import Mathlib.Data.Fin.Basic

/-!
# Iterative NTT (algorithm skeleton; ML-KEM shape)

This module provides an **executable**, iterative Cooley–Tukey NTT in the ML-KEM setting
(`q = 3329`, `n = 256`) intended for:

- later refinement/connection to the algebraic CRT proof in `NTTCorrectness.lean`;
- runtime experiments and (eventually) KAT / implementation parity checks.

This file is deliberately **algorithmic** and does not claim that the implementation matches the
CRT `RingEquiv` NTT yet; that bridge is tracked separately.

References:
- NIST FIPS 203 (ML-KEM), NTT section and reference implementation structure
- Isabelle AFP "Number Theoretic Transform" (Ammer & Kreuzer, 2025) for proof structure ideas
- VSTTE 2020 NTT verification notes (for algorithm invariants)
-/

namespace HeytingLean
namespace Crypto
namespace Lattice
namespace NTTIterative

open scoped BigOperators

abbrev q : Nat := NTT.q
abbrev F : Type := ZMod q

instance : Fact (Nat.Prime q) := by
  dsimp [q, NTT.q]
  exact ⟨by native_decide⟩

/-!
## Bit-reversal and twiddle table
-/

private def bitRevAux (bits n acc : Nat) : Nat :=
  match bits with
  | 0 => acc
  | Nat.succ bits' =>
      bitRevAux bits' (n / 2) (acc * 2 + (n % 2))

/-- Reverse the lowest `bits` of `n`, producing a `Nat`. -/
def bitRevNat (bits n : Nat) : Nat :=
  bitRevAux bits n 0

/-- Bit-reversal of a 7-bit index (for twiddle tables of length 128). -/
def bitRev7 (i : Fin 128) : Fin 128 :=
  ⟨bitRevNat 7 i.val % 128, Nat.mod_lt _ (by decide)⟩

/-- Precomputed twiddle factors: `ζ^(bitRev7 i)` for `i ∈ [0,128)`. -/
def zetaTable : Array F :=
  Array.ofFn (fun i : Fin 128 => (NTT.zeta : F) ^ (bitRev7 i).val)

def zetaInvTable : Array F :=
  zetaTable.map (fun z => z⁻¹)

/-!
## Butterfly and iterative NTT
-/

/-- Single butterfly: `(a,b) ↦ (a + ζ^k·b, a - ζ^k·b)`. -/
def butterfly (a b zk : F) : F × F :=
  (a + zk * b, a - zk * b)

/-!
## Forward NTT as a fixed sequence of butterflies

For `n = 256`, the forward ML-KEM NTT schedule is completely deterministic: 7 stages, each with
128 butterflies, grouped into `2^stage` blocks that share a single twiddle factor `ζ^k`.

Encoding the schedule as an explicit list of butterfly operations has two benefits:
- it keeps the implementation executable (it is still just a loop over 896 operations), and
- it makes linearity / refinement proofs substantially easier (the algorithm is a composition of
  linear butterfly maps).
-/

structure ForwardOp where
  i1 : Fin 256
  i2 : Fin 256
  zk : F

private def forwardOp (i1 i2 : Nat) (zk : F) : ForwardOp :=
  { i1 := Fin.ofNat 256 i1, i2 := Fin.ofNat 256 i2, zk := zk }

/-- The full forward schedule as a list of 896 butterfly operations. -/
opaque forwardOps : List ForwardOp :=
  (List.range 7).flatMap (fun stage =>
    let blocks := 2 ^ stage
    let len := 128 / blocks
    (List.range blocks).flatMap (fun b =>
      let start := (2 * len) * b
      let k := blocks + b
      let zk : F := zetaTable[k]!
      (List.range len).map (fun j => forwardOp (start + j) (start + j + len) zk)))

def applyForwardOp (a : Array F) (op : ForwardOp) : Array F :=
  let i1 := op.i1.val
  let i2 := op.i2.val
  let aj := a.getD i1 0
  let bj := a.getD i2 0
  let t := op.zk * bj
  let a := a.setIfInBounds i2 (aj - t)
  a.setIfInBounds i1 (aj + t)

def applyForwardOps (ops : List ForwardOp) (a : Array F) : Array F :=
  ops.foldl (fun acc op => applyForwardOp acc op) a

/-- Forward NTT (decimation-in-time) on 256 coefficients. -/
def nttIterative (f : Array F) (hsize : f.size = 256) : Array F :=
  let _ := hsize
  applyForwardOps forwardOps f

/-!
## Inverse NTT as a fixed sequence of butterflies

As with the forward pass, the inverse ML-KEM schedule for `n = 256` is deterministic: 7 stages,
each a collection of disjoint butterflies with a stage/block-dependent twiddle factor. Encoding the
inverse as an explicit list of butterfly operations keeps it executable and makes linearity proofs
substantially easier downstream.
-/

structure InverseOp where
  i1 : Fin 256
  i2 : Fin 256
  zkInv : F

private def inverseOp (i1 i2 : Nat) (zkInv : F) : InverseOp :=
  { i1 := Fin.ofNat 256 i1, i2 := Fin.ofNat 256 i2, zkInv := zkInv }

/-- The full inverse schedule as a list of 896 butterfly operations. -/
opaque inverseOps : List InverseOp :=
  (List.range 7).flatMap (fun stage =>
    let len := 2 ^ (stage + 1)
    let blocks : Nat := 256 / (2 * len)
    (List.range blocks).flatMap (fun blockIdx =>
      let start := (2 * len) * blockIdx
      let k : Nat := blocks + blockIdx
      let zkInv : F := zetaInvTable[k]!
      (List.range len).map (fun j => inverseOp (start + j) (start + j + len) zkInv)))

def applyInverseOp (a : Array F) (op : InverseOp) : Array F :=
  let i1 := op.i1.val
  let i2 := op.i2.val
  let u := a.getD i1 0
  let v := a.getD i2 0
  let inv2 : F := (2 : F)⁻¹
  let a := a.setIfInBounds i1 (inv2 * (u + v))
  a.setIfInBounds i2 ((inv2 * op.zkInv) * (u - v))

def applyInverseOps (ops : List InverseOp) (a : Array F) : Array F :=
  ops.foldl (fun acc op => applyInverseOp acc op) a

/-- Execute a single inverse butterfly, specialized to size `256` and an explicit `inv2` factor. -/
def applyInverseOp256 (inv2 : F) (a : Array F) (ha : a.size = 256) (op : InverseOp) : Array F :=
  let i1 := op.i1.val
  let i2 := op.i2.val
  have hi1 : i1 < a.size := by
    have : i1 < 256 := by
      dsimp [i1]
      exact op.i1.isLt
    simpa [ha] using this
  have hi2 : i2 < a.size := by
    have : i2 < 256 := by
      dsimp [i2]
      exact op.i2.isLt
    simpa [ha] using this
  let u := a.getD i1 0
  let v := a.getD i2 0
  -- Write `i2` first, then `i1`; this makes it easier to reason about indices independently.
  let a' := a.set i2 ((inv2 * op.zkInv) * (u - v)) hi2
  have hi1' : i1 < a'.size := by
    simpa [a', Array.size_set] using hi1
  a'.set i1 (inv2 * (u + v)) hi1'

/-- Execute an inverse schedule while threading the invariant `a.size = 256`. -/
def applyInverseOps256 (inv2 : F) : List InverseOp → (a : Array F) → a.size = 256 → Array F
  | [], a, _ha => a
  | op :: ops, a, ha =>
      applyInverseOps256 inv2 ops (applyInverseOp256 inv2 a ha op) (by
        simpa [applyInverseOp256, Array.size_set] using ha)

/-- Iterative inverse NTT (decimation-in-frequency) on 256 coefficients. -/
def inttIterative (f : Array F) (hsize : f.size = 256) : Array F :=
  let inv2 : F := (2 : F)⁻¹
  applyInverseOps256 inv2 inverseOps f hsize

/-!
## NTT-domain multiplication (quadratic factors)

ML-KEM’s NTT domain corresponds to 128 quadratic factors `X^2 - μ`. An element in a factor ring
can be represented as a pair `(a0, a1)` corresponding to `a0 + a1*X`, and multiplication is:

`(a0 + a1*X) * (b0 + b1*X) = (a0*b0 + μ*a1*b1) + (a0*b1 + a1*b0)*X`  mod `(X^2 - μ)`.

The remaining verification work is to *prove* that the chosen `μ` per pair matches the output
ordering/twiddle conventions of `nttIterative` (tracked as Gap 1).
-/

/-- Multiply two degree-1 representatives in `K[X]/(X^2 - μ)`. -/
def basemulPair (a0 a1 b0 b1 μ : F) : F × F :=
  (a0 * b0 + μ * a1 * b1, a0 * b1 + a1 * b0)

/-- The quadratic-factor evaluation point associated to pair index `i` in the implementation
ordering (odd exponents in bit-reversal order). -/
def muForPairIndex (i : Fin 128) : F :=
  (NTT.zeta : F) ^ (2 * (bitRev7 i).val + 1)

theorem muForPairIndex_def (i : Fin 128) :
    muForPairIndex i = (NTT.zeta : F) ^ (2 * (bitRev7 i).val + 1) :=
  rfl

/-- Multiply the `i`th coefficient-pair `(2i, 2i+1)` in the quadratic factor ring `K[X]/(X^2 - μᵢ)`. -/
def basemulPairAt (a b : Array F) (i : Fin 128) : F × F :=
  let idx0 := 2 * i.val
  let idx1 := 2 * i.val + 1
  basemulPair (a.getD idx0 0) (a.getD idx1 0) (b.getD idx0 0) (b.getD idx1 0) (muForPairIndex i)

/-- The pointwise multiplication function underlying `basemul`. -/
def basemulFn (a b : Array F) (ha : a.size = 256) (hb : b.size = 256) : Fin 256 → F :=
  fun j =>
    let _ := ha; let _ := hb
    let i : Nat := j.val / 2
    have hi : i < 128 := by
      have hj : j.val < 128 * 2 := by
        rw [show 128 * 2 = 256 by decide]
        exact j.isLt
      exact Nat.div_lt_of_lt_mul hj
    let iFin : Fin 128 := ⟨i, hi⟩
    let (c0, c1) := basemulPairAt a b iFin
    if j.val % 2 = 0 then c0 else c1

/-- Pointwise multiply two NTT outputs using per-pair quadratic-factor multiplication. -/
def basemul (a b : Array F) (ha : a.size = 256) (hb : b.size = 256) : Array F :=
  Array.ofFn (basemulFn a b ha hb)

@[simp] theorem basemul_getD (a b : Array F) (ha : a.size = 256) (hb : b.size = 256) (j : Nat) :
    (basemul a b ha hb).getD j 0 = if hj : j < 256 then basemulFn a b ha hb ⟨j, hj⟩ else 0 := by
  classical
  by_cases hj : j < 256
  · simp [basemul, Array.getD_eq_getD_getElem?, hj]
  · simp [basemul, Array.getD_eq_getD_getElem?, hj]

theorem basemul_getD_even (a b : Array F) (ha : a.size = 256) (hb : b.size = 256) (i : Fin 128) :
    (basemul a b ha hb).getD (2 * i.val) 0 = (basemulPairAt a b i).1 := by
  classical
  have hlt : (2 * i.val) < 256 := by
    have hi : i.val < 128 := i.isLt
    have hmul : 2 * i.val < 2 * 128 := Nat.mul_lt_mul_of_pos_left hi (by decide : 0 < 2)
    simpa [show 2 * 128 = 256 by decide] using hmul
  have hdiv : (2 * i.val) / 2 = i.val := by simp
  have hmod : (2 * i.val) % 2 = 0 := by simp
  -- Compute via `basemul_getD`, then simplify `basemulFn` at this index.
  have h0 := (basemul_getD (a := a) (b := b) (ha := ha) (hb := hb) (j := 2 * i.val))
  -- Use the `hj : (2*i)<256` branch of the `dite`.
  have h1 :
      (basemul a b ha hb).getD (2 * i.val) 0 = basemulFn a b ha hb ⟨2 * i.val, hlt⟩ := by
    simpa [hlt] using h0
  -- Now unfold `basemulFn` at the even index.
  -- The computed pair index is `i` and the parity branch chooses `.1`.
  simpa [basemulFn, basemulPairAt, hdiv, hmod] using h1

theorem basemul_getD_odd (a b : Array F) (ha : a.size = 256) (hb : b.size = 256) (i : Fin 128) :
    (basemul a b ha hb).getD (2 * i.val + 1) 0 = (basemulPairAt a b i).2 := by
  classical
  have hlt : (2 * i.val + 1) < 256 := by
    have hi : i.val < 128 := i.isLt
    have hle : i.val ≤ 127 := Nat.le_pred_of_lt hi
    have hmul : 2 * i.val ≤ 2 * 127 := Nat.mul_le_mul_left 2 hle
    have hadd : 2 * i.val + 1 ≤ 2 * 127 + 1 := Nat.add_le_add_right hmul 1
    have : 2 * i.val + 1 ≤ 255 := by
      simpa [show 2 * 127 + 1 = 255 by decide] using hadd
    exact lt_of_le_of_lt this (by decide : 255 < 256)
  have hdiv : (2 * i.val + 1) / 2 = i.val := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (Nat.add_mul_div_left 1 i.val (by decide : 0 < 2))
  have hmod : (2 * i.val + 1) % 2 ≠ 0 := by simp
  have h0 := (basemul_getD (a := a) (b := b) (ha := ha) (hb := hb) (j := 2 * i.val + 1))
  have h1 :
      (basemul a b ha hb).getD (2 * i.val + 1) 0 = basemulFn a b ha hb ⟨2 * i.val + 1, hlt⟩ := by
    simpa [hlt] using h0
  -- Unfold `basemulFn` at the odd index: parity branch chooses `.2`.
  -- `simp` rewrites `if (j%2=0)` using `hmod`.
  simpa [basemulFn, basemulPairAt, hdiv, hmod] using h1

end NTTIterative
end Lattice
end Crypto
end HeytingLean
