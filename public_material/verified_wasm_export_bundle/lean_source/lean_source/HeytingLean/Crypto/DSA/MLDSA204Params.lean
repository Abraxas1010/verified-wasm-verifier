import Mathlib.Data.ZMod.Basic

/-!
# FIPS 204 ML-DSA (Dilithium) parameter sets (bundle)

This file records a *machine-checkable* parameter bundle for NIST FIPS 204 (ML-DSA), matching the
shape needed for:

- documentation / CLI reporting; and
- later connections to MLWE/MSIS carriers in the lattice workbench.

This does **not** implement ML-DSA nor prove EUF-CMA security; it is parameter bookkeeping.

Reference: NIST FIPS 204 (ML-DSA), parameter table.
-/

namespace HeytingLean
namespace Crypto
namespace DSA
namespace FIPS204

open scoped BigOperators

/-- FIPS 204 (ML-DSA) parameter bundle (shape only). -/
structure MLDSA204Params where
  name : String
  k : Nat
  ℓ : Nat
  n : Nat := 256
  q : Nat := 8380417
  η : Nat
  τ : Nat
  γ₁ : Nat
  γ₂ : Nat
  β : Nat
  ω : Nat
  deriving Repr, DecidableEq

def mldsa44 : MLDSA204Params :=
  { name := "ML-DSA-44"
  , k := 4
  , ℓ := 4
  , η := 2
  , τ := 39
  , γ₁ := 2 ^ 17
  , γ₂ := (8380417 - 1) / 88
  , β := 78
  , ω := 80
  }

def mldsa65 : MLDSA204Params :=
  { name := "ML-DSA-65"
  , k := 6
  , ℓ := 5
  , η := 4
  , τ := 49
  , γ₁ := 2 ^ 19
  , γ₂ := (8380417 - 1) / 32
  , β := 196
  , ω := 55
  }

def mldsa87 : MLDSA204Params :=
  { name := "ML-DSA-87"
  , k := 8
  , ℓ := 7
  , η := 2
  , τ := 60
  , γ₁ := 2 ^ 19
  , γ₂ := (8380417 - 1) / 32
  , β := 120
  , ω := 75
  }

def all : Array MLDSA204Params :=
  #[mldsa44, mldsa65, mldsa87]

/-- Minimal internal consistency checks used by the CLI. -/
def validParams (p : MLDSA204Params) : Prop :=
  p.n = 256 ∧
  p.q = 8380417 ∧
  p.β = p.τ * p.η ∧
  p.q % 256 = 1

instance (p : MLDSA204Params) : Decidable (validParams p) := by
  unfold validParams
  infer_instance

theorem mldsa44_valid : validParams mldsa44 := by decide
theorem mldsa65_valid : validParams mldsa65 := by decide
theorem mldsa87_valid : validParams mldsa87 := by decide

end FIPS204
end DSA
end Crypto
end HeytingLean

