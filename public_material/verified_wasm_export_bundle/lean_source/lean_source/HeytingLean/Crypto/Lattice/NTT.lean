import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# NTT (ML-KEM parameter facts; spec-first)

This file provides small, **machine-checkable arithmetic facts** used by ML-KEM-style NTT
descriptions:

- the canonical ML-KEM modulus `q = 3329`;
- the usual choice `ζ = 17` as a primitive 256th root of unity mod `q`;
- basic power facts (`ζ^128 = -1`, `ζ^256 = 1`).

We do **not** implement a full NTT algorithm here. Those components belong in a dedicated,
performance-aware development track (and should be tracked as conjectures before landing).
-/

namespace HeytingLean
namespace Crypto
namespace Lattice
namespace NTT

/-- ML-KEM modulus `q` (FIPS 203). -/
def q : Nat := 3329

/-- ML-KEM NTT root `ζ` (FIPS 203). -/
def zeta : ZMod q := (17 : ZMod q)

theorem zeta_pow_256 : zeta ^ 256 = (1 : ZMod q) := by
  -- Reduce to an integer equality and discharge by computation.
  norm_num [q, zeta]
  decide

theorem zeta_pow_128 : zeta ^ 128 = (-1 : ZMod q) := by
  norm_num [q, zeta]
  decide

theorem zeta_pow_128_ne_one : zeta ^ 128 ≠ (1 : ZMod q) := by
  haveI : Fact (2 < q) := ⟨by decide⟩
  simpa [zeta_pow_128] using (ZMod.neg_one_ne_one (n := q))

/-- Minimal "primitive root" witness sufficient for the `2^8` ML-KEM NTT story. -/
def primitive256 : Prop :=
  zeta ^ 256 = (1 : ZMod q) ∧ zeta ^ 128 = (-1 : ZMod q)

instance : Decidable primitive256 := by
  unfold primitive256
  infer_instance

theorem primitive256_holds : primitive256 := by
  exact ⟨zeta_pow_256, zeta_pow_128⟩

end NTT
end Lattice
end Crypto
end HeytingLean
