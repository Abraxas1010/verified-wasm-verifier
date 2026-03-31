import HeytingLean.OpenCLAW.Dialectica.ProtocolLayer
import HeytingLean.OpenCLAW.Crypto.PoW

namespace HeytingLean.OpenCLAW.Dialectica

/-!
# Dialectica Wrappers for Computational-Security Claims

- source_paper_url: https://arxiv.org/abs/2601.09557
- attribution_status: A-conditional
- claim_status: B-pass (dialectica instantiation of PoW theorems)
- proof_status: proved
-/

/-- PoW parameter witness with validity guards. -/
structure PoWParams where
  b : Nat
  target : Nat
  H : Rat
  ht : 0 < target
  hH : H ≠ 0

/-- SH-001/SH-002 PoW layer. -/
def powTimeLayer : ProtocolLayer.{0} where
  Witness := PoWParams
  Challenge := Unit
  secure := fun params _ =>
    HeytingLean.OpenCLAW.Crypto.expectedWallTime params.H params.b params.target =
      (2 ^ params.b : Rat) / (params.target * params.H)

/-- SH-002 witness theorem delegated to `expected_wall_time_formula`. -/
theorem powTimeLayer_secure (w : powTimeLayer.Witness) (c : powTimeLayer.Challenge) :
    powTimeLayer.secure w c := by
  simpa [powTimeLayer] using
    (HeytingLean.OpenCLAW.Crypto.expected_wall_time_formula w.H w.b w.target w.ht w.hH)

/-- SH-001 definitional predicate theorem delegated to `powValid_iff`. -/
theorem pow_acceptance_definitional (hash target : Nat) :
    HeytingLean.OpenCLAW.Crypto.powValid hash target ↔ hash < target :=
  HeytingLean.OpenCLAW.Crypto.powValid_iff hash target

end HeytingLean.OpenCLAW.Dialectica
