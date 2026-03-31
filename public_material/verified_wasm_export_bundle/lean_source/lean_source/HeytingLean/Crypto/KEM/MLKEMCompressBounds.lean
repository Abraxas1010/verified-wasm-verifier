import HeytingLean.Crypto.KEM.MLKEM203Params
import HeytingLean.Crypto.KEM.MLKEMCompress

/-!
# ML-KEM compression error bounds (coefficient-wise)

This module provides **concrete, machine-checked** upper bounds on the coefficient-wise
compression error induced by `MLKEMCompress` for the ML-KEM modulus `q = 3329` at the FIPS 203
bit-depths `d_u ∈ {10,11}` and `d_v ∈ {4,5}`.

These bounds are used downstream to justify “good noise” hypotheses by separating:

- the algebraic residual noise (from K-PKE correctness) and
- the deterministic compression noise injected by (de)compression.

External reference context (not ported here):
- FIPS 203 §4.2.1 (Compress/Decompress definition).
- Formosa Crypto EasyCrypt artifact (CRYPTO 2024): tight error-bound lemmas for compression.

Repo policy note:
We avoid axioms and placeholder proofs. The key theorems below are discharged by computation
(`native_decide`) over the finite type `ZMod 3329`.
-/

namespace HeytingLean
namespace Crypto
namespace KEM
namespace FIPS203

open HeytingLean.Crypto.KEM.FIPS203.Compress

abbrev q : Nat := 3329
abbrev F : Type := ZMod q

instance : NeZero q := by
  exact ⟨by decide⟩

namespace CompressBounds

theorem compressionError_du10_le2 :
    ∀ x : F, compressionError (q := q) (d := 10) x ≤ 2 := by
  native_decide

theorem compressionError_dv4_le105 :
    ∀ x : F, compressionError (q := q) (d := 4) x ≤ 105 := by
  native_decide

theorem compressionError_du11_le1 :
    ∀ x : F, compressionError (q := q) (d := 11) x ≤ 1 := by
  native_decide

theorem compressionError_dv5_le53 :
    ∀ x : F, compressionError (q := q) (d := 5) x ≤ 53 := by
  native_decide

theorem compressionError_u_le {p : MLKEM203Params} (hp : p = mlkem512 ∨ p = mlkem768 ∨ p = mlkem1024)
    (x : ZMod p.q) :
    compressionError (q := p.q) (d := p.du) x ≤ 2 := by
  rcases hp with rfl | hp'
  · simpa [mlkem512] using (compressionError_du10_le2 (x := x))
  rcases hp' with rfl | rfl
  · simpa [mlkem768] using (compressionError_du10_le2 (x := x))
  · -- For ML-KEM-1024, `d_u = 11` and the tighter bound is `1`.
    have hx : compressionError (q := q) (d := 11) (show F from x) ≤ 1 :=
      compressionError_du11_le1 (x := (show F from x))
    exact le_trans hx (by decide)

theorem compressionError_v_le {p : MLKEM203Params} (hp : p = mlkem512 ∨ p = mlkem768 ∨ p = mlkem1024)
    (x : ZMod p.q) :
    compressionError (q := p.q) (d := p.dv) x ≤ 105 := by
  rcases hp with rfl | hp'
  · simpa [mlkem512] using (compressionError_dv4_le105 (x := x))
  rcases hp' with rfl | rfl
  · simpa [mlkem768] using (compressionError_dv4_le105 (x := x))
  · -- For ML-KEM-1024, `d_v = 5` and the tighter bound is `53`.
    have hx : compressionError (q := q) (d := 5) (show F from x) ≤ 53 :=
      compressionError_dv5_le53 (x := (show F from x))
    exact le_trans hx (by decide)

end CompressBounds

end FIPS203
end KEM
end Crypto
end HeytingLean
