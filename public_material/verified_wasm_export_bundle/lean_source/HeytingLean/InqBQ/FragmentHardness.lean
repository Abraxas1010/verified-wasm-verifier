import HeytingLean.InqBQ.HardnessSurfaces
import HeytingLean.InqBQ.HardnessTransportSchema
import HeytingLean.InqBQ.Imported.H10UPCPatch31Undecidability

namespace HeytingLean
namespace InqBQ

open Nat.Partrec

/--
Pointwise transport from the imported H10UPC complement-hardness witness to the
fixed-signature classical finite-validity family.

This is the first honest fragment theorem in the research program: it stays on
the classical finite-validity side rather than transporting all the way into the
InqBQ validity surface.
-/
def h10upcToFiniteValidityBridge : PointwiseHardnessBridge (List H10UPC) where
  sourcePred := fun cs => ¬ H10UPCSat cs
  targetPred := finiteValidityFamily
  target_iff_source := finiteValidityFamily_correct

/--
Pointwise transport from the imported H10UPC complement-hardness witness to the
InqBQ validity family induced by the finite-validity bridge.
-/
def h10upcToInqbqValidityBridge : PointwiseHardnessBridge (List H10UPC) where
  sourcePred := fun cs => ¬ H10UPCSat cs
  targetPred := inqbqValidityFamily
  target_iff_source := reductionValidityFormula_correct

/--
Classical fixed-signature fragment result.

This is not yet a full fragment classification for InqBQ. It is the theorem that
the transported finite-validity family on the fixed binary signature `ReductionSig`
is already not recursively enumerable.
-/
theorem finite_validity_family_not_re :
    ¬ REPred finiteValidityFamily :=
  h10upcToFiniteValidityBridge.target_not_re_of_source_not_re
    imported_h10upcSat_compl_not_re

/-- The shared transport proof of the existing InqBQ validity endpoint. -/
theorem inqbq_validity_family_not_re_via_transport :
    ¬ REPred inqbqValidityFamily :=
  h10upcToInqbqValidityBridge.target_not_re_of_source_not_re
    imported_h10upcSat_compl_not_re

end InqBQ
end HeytingLean
