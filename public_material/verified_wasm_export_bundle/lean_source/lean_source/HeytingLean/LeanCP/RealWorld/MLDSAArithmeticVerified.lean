import HeytingLean.LeanCP.RealWorld.PQArithParams

namespace HeytingLean.LeanCP.RealWorld

namespace MLDSAArithmeticVerified

def params (p : Crypto.DSA.FIPS204.MLDSA204Params) : PQArithParams :=
  pqArithOfMLDSA204 p

theorem params_modulus_eq (p : Crypto.DSA.FIPS204.MLDSA204Params)
    (hp : Crypto.DSA.FIPS204.validParams p) :
    (params p).q = 8380417 := by
  rcases hp with ⟨-, hq, -, -⟩
  simpa [params, pqArithOfMLDSA204] using hq

theorem mldsa44_params_valid : (params Crypto.DSA.FIPS204.mldsa44).valid := by
  simpa [params] using mldsa44_valid

theorem mldsa65_params_valid : (params Crypto.DSA.FIPS204.mldsa65).valid := by
  simpa [params] using mldsa65_valid

theorem mldsa87_params_valid : (params Crypto.DSA.FIPS204.mldsa87).valid := by
  simpa [params] using mldsa87_valid

theorem mldsa44_centeredBound_eq :
    (params Crypto.DSA.FIPS204.mldsa44).centeredBound = 4190208 := by
  decide

theorem mldsa65_centeredBound_eq :
    (params Crypto.DSA.FIPS204.mldsa65).centeredBound = 4190208 := by
  decide

theorem mldsa87_centeredBound_eq :
    (params Crypto.DSA.FIPS204.mldsa87).centeredBound = 4190208 := by
  decide

end MLDSAArithmeticVerified

end HeytingLean.LeanCP.RealWorld
