import HeytingLean.AsymptoticSafety.ScaleSymmetry
import HeytingLean.AsymptoticSafety.Extraction.NumericalRG

namespace HeytingLean
namespace AsymptoticSafety
namespace Extraction

structure ProjectionCertificate (sys : BetaSystem) where
  initial : CouplingPoint
  final : CouplingPoint
  steps : Nat
  exact_projection : projectToUVSafe sys initial = final
  safe_final : isUVSafe sys final

noncomputable def certifyProjectionRun (sys : BetaSystem) (g : CouplingPoint) :
    ProjectionCertificate sys where
  initial := g
  final := projectToUVSafe sys g
  steps := 1
  exact_projection := rfl
  safe_final := by
    unfold isUVSafe
    exact projectToUVSafe_idempotent sys g

theorem certificate_has_single_step (sys : BetaSystem) (g : CouplingPoint) :
    (certifyProjectionRun sys g).steps = 1 :=
  rfl

theorem certificate_exact_projection (sys : BetaSystem) (g : CouplingPoint) :
    projectToUVSafe sys g = (certifyProjectionRun sys g).final :=
  (certifyProjectionRun sys g).exact_projection

theorem certificate_safe_final (sys : BetaSystem) (g : CouplingPoint) :
    isUVSafe sys (certifyProjectionRun sys g).final :=
  (certifyProjectionRun sys g).safe_final

end Extraction
end AsymptoticSafety
end HeytingLean
