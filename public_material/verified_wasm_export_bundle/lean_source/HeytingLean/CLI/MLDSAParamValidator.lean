import HeytingLean.Crypto.DSA.MLDSA204Params
import Lean.Data.Json

/-!
# ML-DSA parameter validator (FIPS 204)

This executable-style library module prints a JSON report describing the ML-DSA parameter sets
from NIST FIPS 204 and runs a small set of internal consistency checks (`validParams`).

It does not claim any security theorem.
-/

namespace HeytingLean
namespace CLI

open HeytingLean.Crypto.DSA.FIPS204

namespace MLDSAValidator

structure ValidationReport where
  paramSet : String
  valid : Bool
  n : Nat
  q : Nat
  k : Nat
  ell : Nat
  eta : Nat
  tau : Nat
  gamma1 : Nat
  gamma2 : Nat
  beta : Nat
  omega : Nat
  deriving Repr

def validateParams (p : MLDSA204Params) : ValidationReport :=
  { paramSet := p.name
  , valid := decide (validParams p)
  , n := p.n
  , q := p.q
  , k := p.k
  , ell := p.ℓ
  , eta := p.η
  , tau := p.τ
  , gamma1 := p.γ₁
  , gamma2 := p.γ₂
  , beta := p.β
  , omega := p.ω
  }

def toJson (r : ValidationReport) : Lean.Json :=
  Lean.Json.mkObj
    [ ("paramSet", Lean.Json.str r.paramSet)
    , ("valid", Lean.Json.bool r.valid)
    , ("n", Lean.Json.num (Lean.JsonNumber.fromNat r.n))
    , ("q", Lean.Json.num (Lean.JsonNumber.fromNat r.q))
    , ("k", Lean.Json.num (Lean.JsonNumber.fromNat r.k))
    , ("ell", Lean.Json.num (Lean.JsonNumber.fromNat r.ell))
    , ("eta", Lean.Json.num (Lean.JsonNumber.fromNat r.eta))
    , ("tau", Lean.Json.num (Lean.JsonNumber.fromNat r.tau))
    , ("gamma1", Lean.Json.num (Lean.JsonNumber.fromNat r.gamma1))
    , ("gamma2", Lean.Json.num (Lean.JsonNumber.fromNat r.gamma2))
    , ("beta", Lean.Json.num (Lean.JsonNumber.fromNat r.beta))
    , ("omega", Lean.Json.num (Lean.JsonNumber.fromNat r.omega))
    ]

def reportJson : Lean.Json :=
  Lean.Json.arr <| HeytingLean.Crypto.DSA.FIPS204.all.map fun p => toJson (validateParams p)

def main (_argv : List String) : IO Unit := do
  IO.println (toString reportJson)

end MLDSAValidator

end CLI
end HeytingLean

-- Intentionally no top-level `main`: this module is imported by other executables.

