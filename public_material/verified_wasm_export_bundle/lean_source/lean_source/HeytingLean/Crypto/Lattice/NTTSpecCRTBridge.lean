import HeytingLean.Crypto.Lattice.NTTCRTBridge
import HeytingLean.Crypto.Lattice.NTTLoopInvariants
import Mathlib.Algebra.Polynomial.Monomial
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

/-!
# Gap 1 Task 2: quadraticSpec matches CRT projection

This file connects the coefficient-level quadratic specification (`NTTBridge.quadraticSpec`) to the
quadratic CRT factor rings `K[X]/(X^2-μ)` used in `NTTCorrectness`.

Concretely, for `μ = ζ^(2*bitRev7(i)+1)`:
- `quadraticSpec a` at indices `2i, 2i+1` computes the even/odd coefficient evaluations at `μ`;
- the image of `poly256 a` in `K[X]/(X^2-μ)` is exactly `a0 + a1*X` with those coefficients.
-/

namespace HeytingLean
namespace Crypto
namespace Lattice
namespace NTTSpecCRTBridge

open scoped BigOperators Polynomial
open Polynomial

open NTTCorrectness
open NTTLoopInvariants
open NTTBridge

abbrev q : Nat := NTT.q
abbrev K : Type := ZMod q
abbrev R : Type := Polynomial K

namespace Index

/-- Even output coordinate `2*i`. -/
def even256 (i : Fin 128) : Fin 256 :=
  ⟨2 * i.val, by
    have hi : i.val < 128 := i.isLt
    have h2 : 2 * i.val < 2 * 128 :=
      Nat.mul_lt_mul_of_pos_left hi (by decide : 0 < (2 : Nat))
    simpa using h2⟩

/-- Odd output coordinate `2*i+1`. -/
def odd256 (i : Fin 128) : Fin 256 :=
  ⟨2 * i.val + 1, by
    have hi : i.val < 128 := i.isLt
    have hi' : i.val ≤ 127 := Nat.le_pred_of_lt hi
    have hle : 2 * i.val + 1 ≤ 2 * 127 + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 2 hi') 1
    have hmax : 2 * 127 + 1 < 256 := by decide
    exact lt_of_le_of_lt hle hmax⟩

@[simp] theorem even256_val (i : Fin 128) : (even256 i).val = 2 * i.val := rfl
@[simp] theorem odd256_val (i : Fin 128) : (odd256 i).val = 2 * i.val + 1 := rfl

end Index

namespace SplitEval

open Split

theorem evenPoly_eval (a : Array K) (μ : K) :
    (evenPoly a).eval μ = ∑ k : Fin 128, (a.getD (2 * k.val) 0) * μ ^ k.val := by
  classical
  -- Avoid `simp` loops between `eval` and `eval₂`.
  change Polynomial.eval₂ (RingHom.id K) μ (evenPoly a) =
      ∑ k : Fin 128, (a.getD (2 * k.val) 0) * μ ^ k.val
  simp [evenPoly]
  -- Use additivity of `eval₂` across the finite sum.
  let term : Fin 128 → K[X] := fun k => C (a.getD (2 * k.val) 0) * X ^ k.val
  have hsum :
      (∑ k ∈ (Finset.univ : Finset (Fin 128)), term k).eval₂ (RingHom.id K) μ =
        ∑ k ∈ (Finset.univ : Finset (Fin 128)), (term k).eval₂ (RingHom.id K) μ := by
    simpa [term] using
      (Polynomial.eval₂_finset_sum (f := RingHom.id K) (x := μ)
        (s := (Finset.univ : Finset (Fin 128))) (g := term))
  -- Evaluate each summand: `(C c * X^n).eval₂ id μ = c * μ^n`.
  -- First rewrite the bindered sums as `Fintype` sums.
  simpa [term, mul_assoc, Finset.sum_mul, Finset.mul_sum] using hsum

theorem oddPoly_eval (a : Array K) (μ : K) :
    (oddPoly a).eval μ = ∑ k : Fin 128, (a.getD (2 * k.val + 1) 0) * μ ^ k.val := by
  classical
  change Polynomial.eval₂ (RingHom.id K) μ (oddPoly a) =
      ∑ k : Fin 128, (a.getD (2 * k.val + 1) 0) * μ ^ k.val
  simp [oddPoly]
  let term : Fin 128 → K[X] := fun k => C (a.getD (2 * k.val + 1) 0) * X ^ k.val
  have hsum :
      (∑ k ∈ (Finset.univ : Finset (Fin 128)), term k).eval₂ (RingHom.id K) μ =
        ∑ k ∈ (Finset.univ : Finset (Fin 128)), (term k).eval₂ (RingHom.id K) μ := by
    simpa [term] using
      (Polynomial.eval₂_finset_sum (f := RingHom.id K) (x := μ)
        (s := (Finset.univ : Finset (Fin 128))) (g := term))
  simpa [term, mul_assoc, Finset.sum_mul, Finset.mul_sum] using hsum

end SplitEval

namespace QuadSpec

open SplitEval
open Index

def evenEmbed (k : Fin 128) : Fin 256 :=
  ⟨2 * k.val, by
    have hk : k.val < 128 := k.isLt
    have h2 : 2 * k.val < 2 * 128 :=
      Nat.mul_lt_mul_of_pos_left hk (by decide : 0 < (2 : Nat))
    simpa using h2⟩

def oddEmbed (k : Fin 128) : Fin 256 :=
  ⟨2 * k.val + 1, by
    have hk : k.val < 128 := k.isLt
    have hk' : k.val ≤ 127 := Nat.le_pred_of_lt hk
    have hle : 2 * k.val + 1 ≤ 2 * 127 + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 2 hk') 1
    have hmax : 2 * 127 + 1 < 256 := by decide
    exact lt_of_le_of_lt hle hmax⟩

theorem evenEmbed_injective : Function.Injective evenEmbed := by
  intro a b h
  apply Fin.ext
  have : (2 * a.val) = (2 * b.val) := by simpa [evenEmbed] using congrArg Fin.val h
  exact Nat.mul_left_cancel (by decide : 0 < 2) this

theorem oddEmbed_injective : Function.Injective oddEmbed := by
  intro a b h
  apply Fin.ext
  have : (2 * a.val + 1) = (2 * b.val + 1) := by simpa [oddEmbed] using congrArg Fin.val h
  have h2 : (2 * a.val) = (2 * b.val) := Nat.add_right_cancel this
  exact Nat.mul_left_cancel (by decide : 0 < 2) h2

theorem filter_even_eq_image :
    (Finset.univ.filter (fun i : Fin 256 => i.val % 2 = 0)) = (Finset.univ.image evenEmbed) := by
  classical
  ext i
  constructor
  · intro hi
    have hi' : i.val % 2 = 0 := by simpa using (Finset.mem_filter.1 hi).2
    have hdiv : 2 ∣ i.val := Nat.dvd_of_mod_eq_zero hi'
    let kNat : Nat := i.val / 2
    have hk : kNat < 128 := by
      have hiLt' : i.val < 2 * 128 := by omega
      exact Nat.div_lt_of_lt_mul hiLt'
    let k : Fin 128 := ⟨kNat, hk⟩
    have hkval : 2 * k.val = i.val := by
      -- `2 * (i/2) = i` because `i` is even.
      dsimp [k, kNat]
      simpa using Nat.mul_div_cancel' hdiv
    refine Finset.mem_image.2 ?_
    refine ⟨k, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    simp [evenEmbed, hkval]
  · intro hi
    rcases Finset.mem_image.1 hi with ⟨k, _hk, rfl⟩
    refine Finset.mem_filter.2 ?_
    refine ⟨Finset.mem_univ _, ?_⟩
    simp [evenEmbed]

theorem filter_odd_eq_image :
    (Finset.univ.filter (fun i : Fin 256 => i.val % 2 = 1)) = (Finset.univ.image oddEmbed) := by
  classical
  ext i
  constructor
  · intro hi
    have hi' : i.val % 2 = 1 := by simpa using (Finset.mem_filter.1 hi).2
    have hodd : i.val % 2 = 1 := hi'
    let kNat : Nat := i.val / 2
    have hk : kNat < 128 := by
      have hiLt' : i.val < 2 * 128 := by omega
      exact Nat.div_lt_of_lt_mul hiLt'
    let k : Fin 128 := ⟨kNat, hk⟩
    have hkval : 2 * k.val + 1 = i.val := by
      have h' : i.val / 2 * 2 + i.val % 2 = i.val := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm] using
          (Nat.mod_add_div i.val 2)
      simpa [kNat, Nat.mul_comm, hodd, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h'
    refine Finset.mem_image.2 ?_
    refine ⟨k, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    simp [oddEmbed, hkval]
  · intro hi
    rcases Finset.mem_image.1 hi with ⟨k, _hk, rfl⟩
    refine Finset.mem_filter.2 ?_
    refine ⟨Finset.mem_univ _, ?_⟩
    simp [oddEmbed]

private theorem quadSpecMatrix_even_row (i : Fin 128) (j : Fin 256) :
    quadSpecMatrix (even256 i) j =
      if j.val % 2 = 0 then (Mu.muByIndex i) ^ (j.val / 2) else 0 := by
  -- Unfold the row parameters `r,pos,rev` for an even row `2*i`.
  simp [NTTBridge.quadSpecMatrix, Mu.muByIndex, even256, NTTIterative.bitRev7]

private theorem quadSpecMatrix_odd_row (i : Fin 128) (j : Fin 256) :
    quadSpecMatrix (odd256 i) j =
      if j.val % 2 = 1 then (Mu.muByIndex i) ^ (j.val / 2) else 0 := by
  -- Unfold the row parameters `r,pos,rev` for an odd row `2*i+1`.
  have hr : (2 * i.val + 1) / 2 = i.val := by
    simpa [Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (Nat.mul_add_div (m := 2) (x := i.val) (y := 1) (m_pos := by decide))
  have hpos : (2 * i.val + 1) % 2 = 1 := by simp
  simp [NTTBridge.quadSpecMatrix, Mu.muByIndex, odd256, NTTIterative.bitRev7, hr, hpos]

abbrev Vec : Type := Fin 256 → K

private def basisVec (j : Fin 256) : Vec :=
  (Pi.single j (1 : K) : Vec)

private def specEvenLin (i : Fin 128) : Vec →ₗ[K] K :=
  (LinearMap.proj (even256 i)).comp
    (Matrix.mulVecLin (quadSpecMatrix : Matrix (Fin 256) (Fin 256) K))

private def specOddLin (i : Fin 128) : Vec →ₗ[K] K :=
  (LinearMap.proj (odd256 i)).comp
    (Matrix.mulVecLin (quadSpecMatrix : Matrix (Fin 256) (Fin 256) K))

private def polyEvenLin (μ : K) : Vec →ₗ[K] K where
  toFun v := (Finset.univ : Finset (Fin 128)).sum fun k => v (evenEmbed k) * μ ^ k.val
  map_add' v w := by
    classical
    simp [Finset.sum_add_distrib, add_mul]
  map_smul' c v := by
    classical
    simp [Finset.mul_sum, smul_eq_mul, mul_assoc]

private def polyOddLin (μ : K) : Vec →ₗ[K] K where
  toFun v := (Finset.univ : Finset (Fin 128)).sum fun k => v (oddEmbed k) * μ ^ k.val
  map_add' v w := by
    classical
    simp [Finset.sum_add_distrib, add_mul]
  map_smul' c v := by
    classical
    simp [Finset.mul_sum, smul_eq_mul, mul_assoc]

private lemma specEvenLin_on_basis (i : Fin 128) (j : Fin 256) :
    specEvenLin i (basisVec j) = quadSpecMatrix (even256 i) j := by
  classical
  -- `mulVec` on a `Pi.single` is a column pick.
  simp [basisVec, specEvenLin]

private lemma specOddLin_on_basis (i : Fin 128) (j : Fin 256) :
    specOddLin i (basisVec j) = quadSpecMatrix (odd256 i) j := by
  classical
  simp [basisVec, specOddLin]

private lemma polyEvenLin_on_basis (μ : K) (j : Fin 256) :
    polyEvenLin μ (basisVec j) = if j.val % 2 = 0 then μ ^ (j.val / 2) else 0 := by
  classical
  -- Unfold only the `toFun` (avoid unfolding the linearity proofs).
  change
    (Finset.univ : Finset (Fin 128)).sum (fun k : Fin 128 => (basisVec j) (evenEmbed k) * μ ^ k.val) =
      if j.val % 2 = 0 then μ ^ (j.val / 2) else 0
  by_cases hj : j.val % 2 = 0
  · have hdiv : 2 ∣ j.val := Nat.dvd_of_mod_eq_zero hj
    let kNat : Nat := j.val / 2
    have hk : kNat < 128 := by
      have hjlt : j.val < 2 * 128 := by
        exact lt_of_lt_of_eq j.isLt (by decide : (256 : Nat) = 2 * 128)
      exact Nat.div_lt_of_lt_mul hjlt
    let k0 : Fin 128 := ⟨kNat, hk⟩
    have hk0 : evenEmbed k0 = j := by
      apply Fin.ext
      dsimp [evenEmbed, k0, kNat]
      simpa using (Nat.mul_div_cancel' hdiv)
    have hsum :
        (Finset.univ : Finset (Fin 128)).sum (fun k => (basisVec j) (evenEmbed k) * μ ^ k.val) =
          (basisVec j) (evenEmbed k0) * μ ^ k0.val := by
      refine Finset.sum_eq_single k0 ?_ ?_
      · intro k hk hkneq
        have hne : evenEmbed k ≠ j := by
          intro hkEq
          have : evenEmbed k = evenEmbed k0 := by simpa [hk0] using hkEq
          exact hkneq (evenEmbed_injective this)
        simp [basisVec, hne]
      · intro hk0not
        exact False.elim (hk0not (Finset.mem_univ k0))
    -- Only the `k0` term survives, and it is `μ^(j/2)`.
    have hk0' : (basisVec j) (evenEmbed k0) = (1 : K) := by
      rw [hk0]
      simp [basisVec]
    rw [hsum]
    have hk0val : k0.val = j.val / 2 := rfl
    simp [hj, hk0', hk0val]
  · have h0 :
        (Finset.univ : Finset (Fin 128)).sum (fun k => (basisVec j) (evenEmbed k) * μ ^ k.val) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro k hk
      have hne : evenEmbed k ≠ j := by
        intro hkEq
        have : j.val % 2 = 0 := by
          have : (evenEmbed k).val % 2 = 0 := by simp [evenEmbed]
          simpa [hkEq] using this
        exact hj this
      simp [basisVec, hne]
    rw [h0]
    simp [hj]

private lemma polyOddLin_on_basis (μ : K) (j : Fin 256) :
    polyOddLin μ (basisVec j) = if j.val % 2 = 1 then μ ^ (j.val / 2) else 0 := by
  classical
  change
    (Finset.univ : Finset (Fin 128)).sum (fun k : Fin 128 => (basisVec j) (oddEmbed k) * μ ^ k.val) =
      if j.val % 2 = 1 then μ ^ (j.val / 2) else 0
  by_cases hj : j.val % 2 = 1
  · let kNat : Nat := j.val / 2
    have hk : kNat < 128 := by
      have hjlt : j.val < 2 * 128 := by
        exact lt_of_lt_of_eq j.isLt (by decide : (256 : Nat) = 2 * 128)
      exact Nat.div_lt_of_lt_mul hjlt
    let k0 : Fin 128 := ⟨kNat, hk⟩
    have hk0 : oddEmbed k0 = j := by
      apply Fin.ext
      -- `j = 2*(j/2) + 1` because `j` is odd.
      dsimp [oddEmbed, k0, kNat]
      have h' : j.val / 2 * 2 + j.val % 2 = j.val := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm] using
          (Nat.mod_add_div j.val 2)
      -- Rewrite the remainder as `1`.
      simpa [Nat.mul_comm, hj, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h'
    have hsum :
        (Finset.univ : Finset (Fin 128)).sum (fun k => (basisVec j) (oddEmbed k) * μ ^ k.val) =
          (basisVec j) (oddEmbed k0) * μ ^ k0.val := by
      refine Finset.sum_eq_single k0 ?_ ?_
      · intro k hk hkneq
        have hne : oddEmbed k ≠ j := by
          intro hkEq
          have : oddEmbed k = oddEmbed k0 := by simpa [hk0] using hkEq
          exact hkneq (oddEmbed_injective this)
        simp [basisVec, hne]
      · intro hk0not
        exact False.elim (hk0not (Finset.mem_univ k0))
    have hk0' : (basisVec j) (oddEmbed k0) = (1 : K) := by
      rw [hk0]
      simp [basisVec]
    rw [hsum]
    have hk0val : k0.val = j.val / 2 := rfl
    simp [hj, hk0', hk0val]
  · have h0 :
        (Finset.univ : Finset (Fin 128)).sum (fun k => (basisVec j) (oddEmbed k) * μ ^ k.val) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro k hk
      have hne : oddEmbed k ≠ j := by
        intro hkEq
        have : j.val % 2 = 1 := by
          have : (oddEmbed k).val % 2 = 1 := by simp [oddEmbed]
          simpa [hkEq] using this
        exact hj this
      simp [basisVec, hne]
    rw [h0]
    simp [hj]

private theorem specEvenLin_eq_polyEvenLin (i : Fin 128) :
    specEvenLin i = polyEvenLin (Mu.muByIndex i) := by
  classical
  apply (Pi.basisFun K (Fin 256)).ext
  intro j
  -- Reduce to the canonical basis vector.
  simp [Pi.basisFun_apply]
  change specEvenLin i (basisVec j) = polyEvenLin (Mu.muByIndex i) (basisVec j)
  simp [specEvenLin_on_basis, polyEvenLin_on_basis, quadSpecMatrix_even_row]

private theorem specOddLin_eq_polyOddLin (i : Fin 128) :
    specOddLin i = polyOddLin (Mu.muByIndex i) := by
  classical
  apply (Pi.basisFun K (Fin 256)).ext
  intro j
  simp [Pi.basisFun_apply]
  change specOddLin i (basisVec j) = polyOddLin (Mu.muByIndex i) (basisVec j)
  simp [specOddLin_on_basis, polyOddLin_on_basis, quadSpecMatrix_odd_row]

theorem quadraticSpec_even (a : Array K) (i : Fin 128) :
    (quadraticSpec a).getD (even256 i).val 0 = (Split.evenPoly a).eval (Mu.muByIndex i) := by
  classical
  set μ : K := Mu.muByIndex i
  let v : Vec := fun j : Fin 256 => a.getD j.val 0
  have hqfun :
      (fun j : Fin 256 => (quadraticSpec a).getD j.val 0) = quadSpecMatrix.mulVec v := by
    funext j
    simp [NTTBridge.quadraticSpec, v, Array.getD_eq_getD_getElem?]
  have hq :
      (quadraticSpec a).getD (even256 i).val 0 = (quadSpecMatrix.mulVec v) (even256 i) := by
    simpa using congrArg (fun f => f (even256 i)) hqfun
  have hspec : specEvenLin i v = (quadSpecMatrix.mulVec v) (even256 i) := by
    simp [specEvenLin]
  have hLin : specEvenLin i = polyEvenLin μ := by
    simpa [μ] using specEvenLin_eq_polyEvenLin i
  have hMid : specEvenLin i v = polyEvenLin μ v := congrArg (fun L => L v) hLin
  have hR : polyEvenLin μ v = (Split.evenPoly a).eval μ := by
    have heval := SplitEval.evenPoly_eval a μ
    simpa [polyEvenLin, v, evenEmbed] using heval.symm
  calc
    (quadraticSpec a).getD (even256 i).val 0 = (quadSpecMatrix.mulVec v) (even256 i) := hq
    _ = specEvenLin i v := by simp [hspec]
    _ = polyEvenLin μ v := hMid
    _ = (Split.evenPoly a).eval μ := hR
    _ = (Split.evenPoly a).eval (Mu.muByIndex i) := by simp [μ]

theorem quadraticSpec_odd (a : Array K) (i : Fin 128) :
    (quadraticSpec a).getD (odd256 i).val 0 = (Split.oddPoly a).eval (Mu.muByIndex i) := by
  classical
  set μ : K := Mu.muByIndex i
  let v : Vec := fun j : Fin 256 => a.getD j.val 0
  have hqfun :
      (fun j : Fin 256 => (quadraticSpec a).getD j.val 0) = quadSpecMatrix.mulVec v := by
    funext j
    simp [NTTBridge.quadraticSpec, v, Array.getD_eq_getD_getElem?]
  have hq :
      (quadraticSpec a).getD (odd256 i).val 0 = (quadSpecMatrix.mulVec v) (odd256 i) := by
    simpa using congrArg (fun f => f (odd256 i)) hqfun
  have hspec : specOddLin i v = (quadSpecMatrix.mulVec v) (odd256 i) := by
    simp [specOddLin]
  have hLin : specOddLin i = polyOddLin μ := by
    simpa [μ] using specOddLin_eq_polyOddLin i
  have hMid : specOddLin i v = polyOddLin μ v := congrArg (fun L => L v) hLin
  have hR : polyOddLin μ v = (Split.oddPoly a).eval μ := by
    have heval := SplitEval.oddPoly_eval a μ
    simpa [polyOddLin, v, oddEmbed] using heval.symm
  calc
    (quadraticSpec a).getD (odd256 i).val 0 = (quadSpecMatrix.mulVec v) (odd256 i) := hq
    _ = specOddLin i v := by simp [hspec]
    _ = polyOddLin μ v := hMid
    _ = (Split.oddPoly a).eval μ := hR
    _ = (Split.oddPoly a).eval (Mu.muByIndex i) := by simp [μ]

end QuadSpec

namespace CRT

open Index
open Split
open QuadSpec

/-- The coefficient pair (a₀,a₁) representing the image of `poly256 a` modulo `X^2-μ`. -/
noncomputable def polyToPair (a : Array K) (μ : K) : K × K :=
  ((evenPoly a).eval μ, (oddPoly a).eval μ)

theorem mk_poly256_eq_pair (a : Array K) (μ : K) :
    let I : Ideal R := quadIdeal μ
    let mk : R →+* (R ⧸ I) := Ideal.Quotient.mk I
    let x : R ⧸ I := mk (X : R)
    let c : K →+* (R ⧸ I) := mk.comp C
    mk (Split.poly256 a) = c ((Split.evenPoly a).eval μ) + c ((Split.oddPoly a).eval μ) * x := by
  classical
  dsimp
  classical
  let I : Ideal R := quadIdeal μ
  let mk : R →+* (R ⧸ I) := Ideal.Quotient.mk I
  let x : R ⧸ I := mk (X : R)
  let c : K →+* (R ⧸ I) := mk.comp C
  have hx2 : x ^ 2 = c μ := by
    simpa [I, mk, x, c] using (NTTCRTBridge.Quad.x_sq_eq_c (μ := μ))
  -- Expand `poly256` in the quotient and split into even/odd indices.
  have hmkPoly :
      mk (Split.poly256 a) =
        ∑ j : Fin 256, c (a.getD j.val 0) * x ^ j.val := by
    simp [Split.poly256, mk, c, x, map_sum, map_mul, map_pow]
  -- Split the sum by parity.
  let f : Fin 256 → (R ⧸ I) := fun j => c (a.getD j.val 0) * x ^ j.val
  have hsplit :
      (∑ j : Fin 256, f j) =
        (Finset.univ.filter (fun j : Fin 256 => j.val % 2 = 0)).sum f +
          (Finset.univ.filter (fun j : Fin 256 => j.val % 2 = 1)).sum f := by
    -- `Fin 256` indices have `mod 2` equal to `0` or `1`.
    classical
    have h0 :
        (Finset.univ.filter (fun j : Fin 256 => j.val % 2 = 0)).sum f +
            (Finset.univ.filter (fun j : Fin 256 => ¬ (j.val % 2 = 0))).sum f =
          (Finset.univ.sum f) := by
      simpa using
        (Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin 256)))
          (p := fun j : Fin 256 => j.val % 2 = 0) f)
    -- Replace `¬ (j%2=0)` with `(j%2=1)`.
    have hnot :
        (Finset.univ.filter (fun j : Fin 256 => ¬ (j.val % 2 = 0))) =
          (Finset.univ.filter (fun j : Fin 256 => j.val % 2 = 1)) := by
      ext j
      constructor
      · intro hj
        have hj0 : ¬ j.val % 2 = 0 := (Finset.mem_filter.1 hj).2
        have hj' : j.val % 2 = 1 := by
          have := Nat.mod_two_eq_zero_or_one j.val
          rcases this with h0 | h1
          · exact False.elim (hj0 h0)
          · exact h1
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hj'⟩
      · intro hj
        have hj1 : j.val % 2 = 1 := (Finset.mem_filter.1 hj).2
        have hj0 : ¬ j.val % 2 = 0 := by
          intro h0
          have hj1' := hj1
          rw [h0] at hj1'
          exact Nat.zero_ne_one hj1'
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hj0⟩
    -- Rewrite `¬ (j%2=0)` as `(j%2=1)` and flip the equation.
    have h1 :
        (Finset.univ.sum f) =
          (Finset.univ.filter (fun j : Fin 256 => j.val % 2 = 0)).sum f +
            (Finset.univ.filter (fun j : Fin 256 => ¬ (j.val % 2 = 0))).sum f := by
      simpa using h0.symm
    simpa [hnot, add_comm, add_left_comm, add_assoc] using h1
  -- Evaluate the even-index contribution using `X^2 = μ`.
  have heven :
      (Finset.univ.filter (fun j : Fin 256 => j.val % 2 = 0)).sum f =
        c ((Split.evenPoly a).eval μ) := by
    classical
    -- Reindex the even filter by `Fin 128`.
    rw [filter_even_eq_image]
    -- Convert sum over image to sum over `Fin 128`.
    have hsum :
        (Finset.univ.image evenEmbed).sum f = ∑ k : Fin 128, f (evenEmbed k) := by
      simpa using
        (Finset.sum_image (s := (Finset.univ : Finset (Fin 128))) (f := f) (by
          intro x hx y hy hxy
          exact evenEmbed_injective hxy))
    -- Compute the term for an even index `2*k`.
    have hterm :
        (∑ k : Fin 128, f (evenEmbed k)) =
          ∑ k : Fin 128, c (a.getD (2 * k.val) 0 * μ ^ k.val) := by
      classical
      apply Fintype.sum_congr
      intro k
      have hxpow : x ^ (2 * k.val) = c (μ ^ k.val) := by
        calc
          x ^ (2 * k.val) = (x ^ 2) ^ k.val := by
            simp [pow_mul]
          _ = (c μ) ^ k.val := by simp [hx2]
          _ = c (μ ^ k.val) := by
            exact (c.map_pow μ k.val).symm
      dsimp [f, evenEmbed]
      calc
        c (a.getD (2 * k.val) 0) * x ^ (2 * k.val)
            = c (a.getD (2 * k.val) 0) * c (μ ^ k.val) := by simp [hxpow]
        _ = c (a.getD (2 * k.val) 0 * μ ^ k.val) := by
              rw [← c.map_mul (a.getD (2 * k.val) 0) (μ ^ k.val)]
    have heval := SplitEval.evenPoly_eval a μ
    -- Assemble without large `simp` calls (this also avoids commutativity shuffling).
    calc
      (Finset.univ.image evenEmbed).sum f
          = ∑ k : Fin 128, f (evenEmbed k) := hsum
      _ = ∑ k : Fin 128, c (a.getD (2 * k.val) 0 * μ ^ k.val) := hterm
      _ = c (∑ k : Fin 128, a.getD (2 * k.val) 0 * μ ^ k.val) := by
            rw [← map_sum c (fun k : Fin 128 => a.getD (2 * k.val) 0 * μ ^ k.val)
              (Finset.univ : Finset (Fin 128))]
      _ = c ((Split.evenPoly a).eval μ) := by simp [heval]
  -- Evaluate the odd-index contribution similarly.
  have hodd :
      (Finset.univ.filter (fun j : Fin 256 => j.val % 2 = 1)).sum f =
        c ((Split.oddPoly a).eval μ) * x := by
    classical
    rw [filter_odd_eq_image]
    have hsum :
        (Finset.univ.image oddEmbed).sum f = ∑ k : Fin 128, f (oddEmbed k) := by
      simpa using
        (Finset.sum_image (s := (Finset.univ : Finset (Fin 128))) (f := f) (by
          intro x hx y hy hxy
          exact oddEmbed_injective hxy))
    have hterm :
        (∑ k : Fin 128, f (oddEmbed k)) =
          ∑ k : Fin 128, c (a.getD (2 * k.val + 1) 0 * μ ^ k.val) * x := by
      classical
      apply Fintype.sum_congr
      intro k
      have hxpow : x ^ (2 * k.val) = c (μ ^ k.val) := by
        calc
          x ^ (2 * k.val) = (x ^ 2) ^ k.val := by
            simp [pow_mul]
          _ = (c μ) ^ k.val := by simp [hx2]
          _ = c (μ ^ k.val) := by
            exact (c.map_pow μ k.val).symm
      dsimp [f, oddEmbed]
      -- `x^(2*k+1) = x^(2*k) * x` and `x^(2*k) = c(μ^k)`.
      calc
        c (a.getD (2 * k.val + 1) 0) * x ^ (2 * k.val + 1)
            = c (a.getD (2 * k.val + 1) 0) * (x ^ (2 * k.val) * x) := by
              simp [pow_succ]
        _ = (c (a.getD (2 * k.val + 1) 0) * x ^ (2 * k.val)) * x := by
                simp [mul_assoc]
        _ = (c (a.getD (2 * k.val + 1) 0) * c (μ ^ k.val)) * x := by
                simp [hxpow]
        _ = c (a.getD (2 * k.val + 1) 0 * μ ^ k.val) * x := by
              -- Use `map_mul` and then multiply both sides by `x`.
              rw [← c.map_mul (a.getD (2 * k.val + 1) 0) (μ ^ k.val)]
    have heval := SplitEval.oddPoly_eval a μ
    -- Assemble and factor the trailing `* x`.
    calc
      (Finset.univ.image oddEmbed).sum f
          = ∑ k : Fin 128, f (oddEmbed k) := hsum
      _ = ∑ k : Fin 128, c (a.getD (2 * k.val + 1) 0 * μ ^ k.val) * x := hterm
      _ = (∑ k : Fin 128, c (a.getD (2 * k.val + 1) 0 * μ ^ k.val)) * x := by
            -- Rewrite the `Fintype` sum as a `Finset.univ` sum and use `Finset.sum_mul`.
            simpa using
              (Finset.sum_mul (s := (Finset.univ : Finset (Fin 128)))
                (f := fun k : Fin 128 => c (a.getD (2 * k.val + 1) 0 * μ ^ k.val)) (a := x)).symm
      _ = (c (∑ k : Fin 128, a.getD (2 * k.val + 1) 0 * μ ^ k.val)) * x := by
            rw [← map_sum c (fun k : Fin 128 => a.getD (2 * k.val + 1) 0 * μ ^ k.val)
              (Finset.univ : Finset (Fin 128))]
      _ = c ((Split.oddPoly a).eval μ) * x := by simp [heval]
  -- Put everything together.
  calc
    mk (Split.poly256 a)
        = ∑ j : Fin 256, f j := by simp [hmkPoly, f]
    _ = (Finset.univ.filter (fun j : Fin 256 => j.val % 2 = 0)).sum f +
          (Finset.univ.filter (fun j : Fin 256 => j.val % 2 = 1)).sum f := hsplit
    _ = c ((Split.evenPoly a).eval μ) + c ((Split.oddPoly a).eval μ) * x := by
          -- `hodd` is in the form `... = c(...) * x`.
          simp [heven, hodd]

theorem mk_poly256_eq_quadraticSpec (a : Array K) (i : Fin 128) :
    let μ : K := Mu.muByIndex i
    let I : Ideal R := quadIdeal μ
    let mk : R →+* (R ⧸ I) := Ideal.Quotient.mk I
    let x : R ⧸ I := mk (X : R)
    let c : K →+* (R ⧸ I) := mk.comp C
    mk (Split.poly256 a) =
      c ((quadraticSpec a).getD (even256 i).val 0) + c ((quadraticSpec a).getD (odd256 i).val 0) * x := by
  classical
  dsimp
  set μ : K := Mu.muByIndex i
  have he : (Split.evenPoly a).eval μ = (quadraticSpec a).getD (even256 i).val 0 := by
    simpa [μ] using (QuadSpec.quadraticSpec_even (a := a) (i := i)).symm
  have ho : (Split.oddPoly a).eval μ = (quadraticSpec a).getD (odd256 i).val 0 := by
    simpa [μ] using (QuadSpec.quadraticSpec_odd (a := a) (i := i)).symm
  simpa [μ, he, ho] using (mk_poly256_eq_pair (a := a) (μ := μ))

end CRT

end NTTSpecCRTBridge
end Lattice
end Crypto
end HeytingLean
