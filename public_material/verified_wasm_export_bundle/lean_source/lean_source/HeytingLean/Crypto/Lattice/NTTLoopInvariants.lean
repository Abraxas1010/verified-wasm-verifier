import HeytingLean.Crypto.Lattice.NTTBridge
import HeytingLean.Crypto.Lattice.NTTCorrectness
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic

/-!
# Gap 1 helpers: quadratic-factor evaluation points and split polynomials

This file packages the basic facts needed to prove the remaining NTT bridge:

1. The relevant evaluation points are `μ = ζ^(2*bitRev7(i)+1)` (odd exponents), hence primitive
   256th roots.
2. Any polynomial `f(X) = ∑ a_i X^i` splits as `f(X) = f0(X^2) + X*f1(X^2)` where `f0` uses even
   coefficients and `f1` uses odd coefficients.

These are the algebraic building blocks for:
- proving `NTTIterative.nttIterative` matches `NTTBridge.quadraticSpec` (Gap 1 core);
- connecting the quadratic spec to the CRT factors `K[X]/(X^2-μ)` (for multiplication correctness).
-/

namespace HeytingLean
namespace Crypto
namespace Lattice
namespace NTTLoopInvariants

open scoped BigOperators Polynomial
open Polynomial

abbrev q : Nat := NTT.q
abbrev K : Type := ZMod q

instance : Fact (Nat.Prime q) := by
  dsimp [q, NTT.q]
  exact ⟨by native_decide⟩

namespace Mu

open NTTIterative
open NTTCorrectness

abbrev ζ : K := NTT.zeta

/-- The `i`th quadratic-factor evaluation point, in the implementation ordering. -/
def muByIndex (i : Fin 128) : K :=
  ζ ^ (2 * (NTTIterative.bitRev7 i).val + 1)

theorem muByIndex_def (i : Fin 128) :
    muByIndex i = ζ ^ (2 * (NTTIterative.bitRev7 i).val + 1) :=
  rfl

private theorem odd_coprime_256 (n : Nat) (hn : n % 2 = 1) : Nat.Coprime n 256 := by
  -- `n` odd implies `gcd n 256 = 1` since `256 = 2^8`.
  have h2 : Nat.Coprime n 2 := by
    -- `n` odd ↔ coprime with 2.
    exact (Nat.coprime_two_right).2 ((Nat.odd_iff).2 hn)
  -- `Coprime n 2` implies `Coprime n (2^8)` and hence `Coprime n 256`.
  simpa [show (256 : Nat) = 2 ^ 8 by decide] using h2.pow_right 8

theorem muByIndex_isPrimitiveRoot (i : Fin 128) :
    IsPrimitiveRoot (muByIndex i) 256 := by
  -- `ζ` is primitive 256th root, and we raise to an odd exponent.
  have hζ : IsPrimitiveRoot ζ 256 := NTTCorrectness.zeta_isPrimitiveRoot
  have hodd : (2 * (NTTIterative.bitRev7 i).val + 1) % 2 = 1 := by
    simp
  have hcop : Nat.Coprime (2 * (NTTIterative.bitRev7 i).val + 1) 256 :=
    odd_coprime_256 _ hodd
  simpa [muByIndex] using hζ.pow_of_coprime (2 * (NTTIterative.bitRev7 i).val + 1) hcop

theorem muByIndex_pow_256 (i : Fin 128) : muByIndex i ^ 256 = (1 : K) := by
  exact (muByIndex_isPrimitiveRoot i).pow_eq_one

theorem muByIndex_pow_128 (i : Fin 128) : muByIndex i ^ 128 = (-1 : K) := by
  have hprim := muByIndex_isPrimitiveRoot i
  have hsq : (muByIndex i ^ 128) ^ 2 = (1 : K) := by
    -- `(μ^128)^2 = μ^256 = 1`.
    calc
      (muByIndex i ^ 128) ^ 2 = muByIndex i ^ (128 * 2) := by
        simpa using (pow_mul (muByIndex i) 128 2).symm
      _ = muByIndex i ^ 256 := by
        simp [show (128 * 2) = 256 by decide]
      _ = (1 : K) := by simpa using hprim.pow_eq_one
  have hne : muByIndex i ^ 128 ≠ (1 : K) := by
    intro h
    have : (256 : Nat) ∣ 128 := by
      -- primitive root implies `μ^l = 1 → 256 ∣ l`.
      exact hprim.dvd_of_pow_eq_one 128 (by simpa using h)
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < (128 : Nat)) (by decide : 128 < 256) this
  -- In a domain, `a^2 = 1` iff `a = 1 ∨ a = -1`.
  have hcases : muByIndex i ^ 128 = (1 : K) ∨ muByIndex i ^ 128 = (-1 : K) := by
    simpa [sq] using (sq_eq_one_iff (a := (muByIndex i ^ 128))).1 hsq
  exact hcases.resolve_left hne

end Mu

namespace Split

/-- Even-coefficient polynomial: `∑_{k<128} a[2k] * X^k`. -/
noncomputable def evenPoly (a : Array K) : K[X] :=
  ∑ k : Fin 128, C (a.getD (2 * k.val) 0) * X ^ k.val

/-- Odd-coefficient polynomial: `∑_{k<128} a[2k+1] * X^k`. -/
noncomputable def oddPoly (a : Array K) : K[X] :=
  ∑ k : Fin 128, C (a.getD (2 * k.val + 1) 0) * X ^ k.val

/-- The length-256 polynomial `∑_{i<256} a[i] * X^i`. -/
noncomputable def poly256 (a : Array K) : K[X] :=
  ∑ i : Fin 256, C (a.getD i.val 0) * X ^ i.val

end Split

namespace Mu

open scoped Nat

theorem muByIndex_mem_roots256 (i : Fin 128) : muByIndex i ∈ NTTCorrectness.roots256 := by
  have hpos : 0 < (256 : Nat) := by decide
  have hprim : IsPrimitiveRoot (muByIndex i) 256 := muByIndex_isPrimitiveRoot i
  -- Avoid `simp` rewriting the membership goal into `IsPrimitiveRoot ...` implicitly.
  dsimp [NTTCorrectness.roots256]
  exact (mem_primitiveRoots (k := 256) (R := K) hpos).2 hprim

theorem bitRev7_involutive : Function.Involutive (NTTIterative.bitRev7) := by
  intro i
  fin_cases i <;> native_decide

theorem bitRev7_injective : Function.Injective (NTTIterative.bitRev7) :=
  bitRev7_involutive.injective

private lemma exp_lt_256 (i : Fin 128) : 2 * (NTTIterative.bitRev7 i).val + 1 < 256 := by
  have hlt : (NTTIterative.bitRev7 i).val < 128 := (NTTIterative.bitRev7 i).isLt
  omega

theorem muByIndex_injective : Function.Injective muByIndex := by
  intro i j hij
  have hζ : IsPrimitiveRoot ζ 256 := NTTCorrectness.zeta_isPrimitiveRoot
  have hi : 2 * (NTTIterative.bitRev7 i).val + 1 < 256 := exp_lt_256 i
  have hj : 2 * (NTTIterative.bitRev7 j).val + 1 < 256 := exp_lt_256 j
  have hexp :
      (2 * (NTTIterative.bitRev7 i).val + 1) =
        (2 * (NTTIterative.bitRev7 j).val + 1) := by
    -- Use injectivity of powers for a primitive root within `[0,256)`.
    exact hζ.pow_inj hi hj (by simpa [muByIndex] using hij)
  have hmul : 2 * (NTTIterative.bitRev7 i).val = 2 * (NTTIterative.bitRev7 j).val :=
    Nat.add_right_cancel hexp
  have hrev : (NTTIterative.bitRev7 i).val = (NTTIterative.bitRev7 j).val := by
    -- cancel multiplication by 2
    exact Nat.mul_left_cancel (by decide : 0 < 2) hmul
  have hbr : NTTIterative.bitRev7 i = NTTIterative.bitRev7 j :=
    Fin.ext hrev
  exact bitRev7_injective hbr

theorem muByIndex_surjective_roots256 :
    ∀ μ ∈ NTTCorrectness.roots256, ∃ i : Fin 128, muByIndex i = μ := by
  classical
  intro μ hμ
  let muSet : Finset K := Finset.univ.image muByIndex
  have hsubset : muSet ⊆ NTTCorrectness.roots256 := by
    intro x hx
    rcases Finset.mem_image.1 hx with ⟨i, _hi, rfl⟩
    exact muByIndex_mem_roots256 i
  have hcardRoots : NTTCorrectness.roots256.card = 128 := by
    have h :=
      (NTTCorrectness.zeta_isPrimitiveRoot.card_primitiveRoots (k := 256) (R := K))
    have ht : (φ 256) = 128 := by native_decide
    simpa [NTTCorrectness.roots256, ht] using h
  have hcardMuSet : muSet.card = 128 := by
    -- `muByIndex` is injective on `Fin 128`, so the image has full size.
    simpa [muSet] using (Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin 128))) muByIndex_injective)
  have hEq : muSet = NTTCorrectness.roots256 :=
    Finset.eq_of_subset_of_card_le hsubset (by simp [hcardRoots, hcardMuSet])
  have hmemMuSet : μ ∈ muSet := by simpa [hEq] using hμ
  rcases Finset.mem_image.1 hmemMuSet with ⟨i, _hi, rfl⟩
  exact ⟨i, rfl⟩

end Mu

end NTTLoopInvariants
end Lattice
end Crypto
end HeytingLean
