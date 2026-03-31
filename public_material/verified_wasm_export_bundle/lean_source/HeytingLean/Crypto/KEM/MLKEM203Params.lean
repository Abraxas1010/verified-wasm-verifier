import HeytingLean.Crypto.KEM.MLKEM
import HeytingLean.Crypto.Lattice.Problems

/-!
# FIPS 203 ML-KEM parameter sets (machine-checkable bundle)

This file records the ML-KEM parameter table from NIST FIPS 203 (ML-KEM), Section 8 / Appendix A,
as a Lean structure with decidable validity checks.

Scope:
- parameter bookkeeping and basic well-formedness checks;
- light conversions into existing HeytingLean parameter carriers (`MLWEParams`, `MLKEMParams`).

Non-goals:
- implementing real ML-KEM/K-PKE/NTT;
- proving cryptographic security (handled elsewhere as spec shells / conjectures).
-/

namespace HeytingLean
namespace Crypto
namespace KEM
namespace FIPS203

open HeytingLean.Crypto.Lattice

/-- FIPS 203 (ML-KEM) parameter set bundle. -/
structure MLKEM203Params where
  /-- Human name (e.g. `ML-KEM-512`). -/
  name : String
  /-- Module rank `k` (2/3/4 for 512/768/1024). -/
  k : Nat
  /-- Polynomial degree `n` (fixed to 256 in ML-KEM). -/
  n : Nat := 256
  /-- Modulus `q` (fixed to 3329 in ML-KEM). -/
  q : Nat := 3329
  /-- CBD parameter for secrets (`η₁`). -/
  eta1 : Nat
  /-- CBD parameter for noise (`η₂`). -/
  eta2 : Nat
  /-- Compression bits for `u` (`d_u`). -/
  du : Nat
  /-- Compression bits for `v` (`d_v`). -/
  dv : Nat
  /-- Encapsulation key size (bytes). -/
  ekSize : Nat
  /-- Decapsulation key size (bytes). -/
  dkSize : Nat
  /-- Ciphertext size (bytes). -/
  ctSize : Nat
  deriving Repr, DecidableEq

/-!
## Concrete parameter sets (FIPS 203 Appendix A)
-/

/-- ML-KEM-512 (NIST security category 1). -/
def mlkem512 : MLKEM203Params where
  name := "ML-KEM-512"
  k := 2
  eta1 := 3
  eta2 := 2
  du := 10
  dv := 4
  ekSize := 800
  dkSize := 1632
  ctSize := 768

/-- ML-KEM-768 (NIST security category 3). -/
def mlkem768 : MLKEM203Params where
  name := "ML-KEM-768"
  k := 3
  eta1 := 2
  eta2 := 2
  du := 10
  dv := 4
  ekSize := 1184
  dkSize := 2400
  ctSize := 1088

/-- ML-KEM-1024 (NIST security category 5). -/
def mlkem1024 : MLKEM203Params where
  name := "ML-KEM-1024"
  k := 4
  eta1 := 2
  eta2 := 2
  du := 11
  dv := 5
  ekSize := 1568
  dkSize := 3168
  ctSize := 1568

def all : Array MLKEM203Params :=
  #[mlkem512, mlkem768, mlkem1024]

/-!
## Validity predicate (cheap, decidable)
-/

/-- Parameter validity predicate capturing the FIPS 203 table constraints. -/
def validParams (p : MLKEM203Params) : Prop :=
  p.n = 256 ∧
  p.q = 3329 ∧
  (p.k = 2 ∨ p.k = 3 ∨ p.k = 4) ∧
  (p.eta1 = 2 ∨ p.eta1 = 3) ∧
  p.eta2 = 2 ∧
  (p.du = 10 ∨ p.du = 11) ∧
  (p.dv = 4 ∨ p.dv = 5) ∧
  (p.dkSize = 1632 ∨ p.dkSize = 2400 ∨ p.dkSize = 3168)

instance (p : MLKEM203Params) : Decidable (validParams p) := by
  unfold validParams
  infer_instance

theorem mlkem512_valid : validParams mlkem512 := by decide
theorem mlkem768_valid : validParams mlkem768 := by decide
theorem mlkem1024_valid : validParams mlkem1024 := by decide

/-!
## Bridges into existing HeytingLean parameter carriers
-/

/-- Convert a FIPS 203 ML-KEM parameter set to the existing `MLWEParams` carrier. -/
def toMLWEParams (p : MLKEM203Params) : MLWEParams :=
  { n := p.n, q := p.q, k := p.k }

/-- Convert a FIPS 203 parameter set to the existing *toy* `MLKEMParams` bundle (KAT wiring). -/
def toToyMLKEMParams (p : MLKEM203Params) : HeytingLean.Crypto.KEM.MLKEMParams :=
  { name := p.name, k := p.k, katBits := p.dkSize }

end FIPS203
end KEM
end Crypto
end HeytingLean
