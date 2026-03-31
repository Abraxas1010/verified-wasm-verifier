import HeytingLean.Crypto.KEM.MLKEM203Params
import HeytingLean.Crypto.KEM.MLKEMCompressBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# ML-KEM residual model (accurate algebraic shape; probability-free)

This file defines an **accurate shape** for the ML-KEM decryption residual at the coefficient level:

- multiplication in `Z[X]/(X^n+1)` induces **negacyclic convolution** (sign flip on wrap-around);
- the K-PKE residual per coefficient has the form `⟨e,r⟩ + e₂ - ⟨s,e₁⟩`;
- compression/decompression injects an additional (bounded) error term.

This is intentionally probability-free: it does not claim independence, does not build a full
distribution, and does not attempt to reproduce the exact NIST exponents yet. It is the correct
algebraic target for connecting:

- the iterative NTT algorithm bridge (Gap 1, via `MLKEMResidualNTTBridge.lean`), and
- the failure probability computation pipeline (Gap 3).
-/

namespace HeytingLean
namespace Crypto
namespace KEM
namespace FIPS203

open scoped BigOperators

namespace ResidualAccurate

variable {n : Nat}

/-- Negacyclic convolution coefficient (mod `X^n + 1`) for coefficient function `a,b : Fin n → ℤ`. -/
noncomputable def negacyclicConvCoeff (n : Nat) (hn : 0 < n) (a b : Fin n → ℤ) (i : Fin n) : ℤ :=
  ∑ j : Fin n,
    let k : Fin n := ⟨(i.1 + n - j.1) % n, Nat.mod_lt _ hn⟩
    let sgn : ℤ := if j ≤ i then 1 else -1
    sgn * a j * b k

theorem natAbs_negacyclicConvCoeff_le (n : Nat) (hn : 0 < n) (a b : Fin n → ℤ) (i : Fin n)
    (A B : Nat)
    (ha : ∀ j, (a j).natAbs ≤ A)
    (hb : ∀ j, (b j).natAbs ≤ B) :
    (negacyclicConvCoeff n hn a b i).natAbs ≤ n * A * B := by
  classical
  let kIdx : Fin n → Fin n :=
    fun j => ⟨(i.1 + n - j.1) % n, Nat.mod_lt _ hn⟩
  let sgn : Fin n → ℤ :=
    fun j => if j ≤ i then 1 else -1

  have h1 :
      (negacyclicConvCoeff n hn a b i).natAbs ≤
        ∑ j : Fin n, ((sgn j) * a j * b (kIdx j)).natAbs := by
    simpa [negacyclicConvCoeff, kIdx, sgn] using
      (nat_abs_sum_le (s := (Finset.univ : Finset (Fin n)))
        (f := fun j : Fin n => (sgn j) * a j * b (kIdx j)))

  have hterm : ∀ j : Fin n, ((sgn j) * a j * b (kIdx j)).natAbs ≤ A * B := by
    intro j
    have hsgn : (sgn j).natAbs = 1 := by
      by_cases hji : j ≤ i <;> simp [sgn, hji]
    have hmul :
        ((sgn j) * a j * b (kIdx j)).natAbs = (a j).natAbs * (b (kIdx j)).natAbs := by
      simp [Int.natAbs_mul, hsgn, mul_left_comm, mul_comm]
    have ha' : (a j).natAbs ≤ A := ha j
    have hb' : (b (kIdx j)).natAbs ≤ B := hb (kIdx j)
    have hab : (a j).natAbs * (b (kIdx j)).natAbs ≤ A * B :=
      Nat.mul_le_mul ha' hb'
    simpa [hmul] using hab

  have h2 :
      (∑ j : Fin n, ((sgn j) * a j * b (kIdx j)).natAbs) ≤ n * (A * B) := by
    have :
        (∑ j : Fin n, ((sgn j) * a j * b (kIdx j)).natAbs) ≤ ∑ _j : Fin n, (A * B) := by
      refine Finset.sum_le_sum ?_
      intro j _hj
      exact hterm j
    simpa using (this.trans_eq (by simp))

  -- Combine the bounds and re-associate the RHS to `n*A*B`.
  have : n * (A * B) = n * A * B := by simp [Nat.mul_assoc]
  exact le_trans h1 (by simpa [this] using h2)

/-!
## Compression-error hooks (already proved elsewhere)

We record the “public API” facts here so the residual model can incorporate compression bounds
without re-proving them.
-/

open HeytingLean.Crypto.KEM.FIPS203.CompressBounds

abbrev q : Nat := 3329
abbrev F : Type := ZMod q

theorem du10_error_le2 (x : F) : Compress.compressionError (q := q) (d := 10) x ≤ 2 :=
  compressionError_du10_le2 x

theorem dv4_error_le105 (x : F) : Compress.compressionError (q := q) (d := 4) x ≤ 105 :=
  compressionError_dv4_le105 x

end ResidualAccurate

end FIPS203
end KEM
end Crypto
end HeytingLean
