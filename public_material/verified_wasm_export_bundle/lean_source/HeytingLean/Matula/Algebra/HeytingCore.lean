import HeytingLean.Contracts.RoundTrip
import HeytingLean.Matula.Algebra.Nucleus

namespace HeytingLean
namespace Matula
namespace Algebra
namespace HeytingCore

open HeytingLean.LoF
open HeytingLean.Contracts

abbrev Carrier := MatulaNucleus.Carrier
noncomputable abbrev R := MatulaNucleus.reentry
abbrev Omega := R.Omega

noncomputable def encode (a : Omega) : Carrier := a

noncomputable def decode (x : Carrier) : Omega :=
  Reentry.Omega.mk (R := R) (R x) (R.idempotent _)

noncomputable def contract : RoundTrip (R := R) Carrier where
  encode := encode
  decode := decode
  round := by
    intro a
    apply Subtype.ext
    simp [encode, decode]

@[simp] theorem decode_encode (a : Omega) : decode (encode a) = a := by
  simpa [contract, encode, decode] using contract.round a

/-- The fixed-point implication aligns with ambient implication after encoding. -/
@[simp] theorem encode_himp (a b : Omega) :
    encode (a ⇨ b) = ((a : Carrier) ⇨ (b : Carrier)) := by
  -- For this Phase II candidate, `R` is identity on the carrier.
  rfl

@[simp] theorem eulerBoundary_eq_process :
    R.eulerBoundary = R.process := by
  exact Reentry.eulerBoundary_eq_process (R := R)

@[simp] theorem process_carrier :
    ((R.process : Omega) : Carrier) = MatulaNucleus.primordial := by
  simpa using MatulaNucleus.process_carrier

@[simp] theorem counter_carrier :
    ((R.counterProcess : Omega) : Carrier) = MatulaNucleus.counter := by
  simpa using MatulaNucleus.counterProcess_carrier

@[simp] theorem eulerBoundary_carrier :
    ((R.eulerBoundary : Omega) : Carrier) = MatulaNucleus.primordial := by
  simpa using MatulaNucleus.eulerBoundary_carrier

end HeytingCore
end Algebra
end Matula
end HeytingLean
