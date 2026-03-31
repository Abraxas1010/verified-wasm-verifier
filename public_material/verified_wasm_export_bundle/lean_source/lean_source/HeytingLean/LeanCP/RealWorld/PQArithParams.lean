import HeytingLean.Crypto.KEM.MLKEM203Params
import HeytingLean.Crypto.DSA.MLDSA204Params

namespace HeytingLean.LeanCP.RealWorld

/-- Shared arithmetic carrier for PQ lattice parameter sets that use 256-coefficient polynomials. -/
structure PQArithParams where
  name : String
  n : Nat
  q : Nat
  montgomeryBits : Nat := 16
  deriving Repr, DecidableEq

def PQArithParams.valid (p : PQArithParams) : Prop :=
  p.n = 256 ∧ 0 < p.q ∧ p.q % 2 = 1 ∧ p.q < 2 ^ 31

instance (p : PQArithParams) : Decidable p.valid := by
  unfold PQArithParams.valid
  infer_instance

def PQArithParams.centeredBoundNat (p : PQArithParams) : Nat :=
  (p.q - 1) / 2

def PQArithParams.centeredBound (p : PQArithParams) : Int :=
  p.centeredBoundNat

def pqArithOfMLKEM203 (p : Crypto.KEM.FIPS203.MLKEM203Params) : PQArithParams :=
  { name := p.name, n := p.n, q := p.q }

def pqArithOfMLDSA204 (p : Crypto.DSA.FIPS204.MLDSA204Params) : PQArithParams :=
  { name := p.name, n := p.n, q := p.q }

theorem mlkem512_valid :
    (pqArithOfMLKEM203 Crypto.KEM.FIPS203.mlkem512).valid := by
  decide

theorem mlkem768_valid :
    (pqArithOfMLKEM203 Crypto.KEM.FIPS203.mlkem768).valid := by
  decide

theorem mlkem1024_valid :
    (pqArithOfMLKEM203 Crypto.KEM.FIPS203.mlkem1024).valid := by
  decide

theorem mldsa44_valid :
    (pqArithOfMLDSA204 Crypto.DSA.FIPS204.mldsa44).valid := by
  decide

theorem mldsa65_valid :
    (pqArithOfMLDSA204 Crypto.DSA.FIPS204.mldsa65).valid := by
  decide

theorem mldsa87_valid :
    (pqArithOfMLDSA204 Crypto.DSA.FIPS204.mldsa87).valid := by
  decide

theorem mlkem_centeredBound_eq :
    (pqArithOfMLKEM203 Crypto.KEM.FIPS203.mlkem512).centeredBound = 1664 := by
  decide

theorem mldsa_centeredBound_eq :
    (pqArithOfMLDSA204 Crypto.DSA.FIPS204.mldsa44).centeredBound = 4190208 := by
  decide

end HeytingLean.LeanCP.RealWorld
