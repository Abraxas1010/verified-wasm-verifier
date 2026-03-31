import HeytingLean.OpenCLAW.Dialectica.ProtocolLayer
import HeytingLean.OpenCLAW.Crypto.ReedSolomonBound

namespace HeytingLean.OpenCLAW.Dialectica

/-!
# Dialectica Wrappers for Data-Integrity Claims

- source_type: textbook coding theory
- attribution_status: n/a (background)
- claim_status: B-pass (background, dialectica instantiation)
- proof_status: proved
-/

/-- RS code parameters with validity guard. -/
structure RSParams where
  n : Nat
  k : Nat
  hk : k <= n

/-- SH-003 as a dialectica integrity layer. -/
def rsIntegrityLayer : ProtocolLayer.{0} where
  Witness := RSParams
  Challenge := Nat
  secure := fun params numCorrupted =>
    numCorrupted <= HeytingLean.OpenCLAW.Crypto.rsCorrectableSymbols params.n params.k

/-- Capacity theorem delegated to `rs_correctable_symbols`. -/
theorem rsIntegrityLayer_capacity (params : RSParams) :
    HeytingLean.OpenCLAW.Crypto.rsCorrectableSymbols params.n params.k = (params.n - params.k) / 2 :=
  HeytingLean.OpenCLAW.Crypto.rs_correctable_symbols params.n params.k

/-- RS(255,223) corrects 16 symbols. -/
example :
    rsIntegrityLayer.secure
      ({ n := 255, k := 223, hk := by decide } : RSParams)
      (HeytingLean.OpenCLAW.Crypto.rsCorrectableSymbols 255 223) := by
  simp [rsIntegrityLayer]

end HeytingLean.OpenCLAW.Dialectica
