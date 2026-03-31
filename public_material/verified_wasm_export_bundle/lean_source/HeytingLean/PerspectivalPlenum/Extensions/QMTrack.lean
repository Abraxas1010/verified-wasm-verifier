import HeytingLean.PerspectivalPlenum.Lens.Profile
import HeytingLean.Quantum.Contextuality.Witness
import HeytingLean.Quantum.Contextuality.Triangle

namespace HeytingLean
namespace PerspectivalPlenum
namespace Extensions
namespace QMTrack

open HeytingLean.Quantum.Contextuality

/-- QM extension binding: a lens policy paired with a contextuality witness. -/
structure QMLensBinding where
  profile : Lens.LensProfile
  witness : Witness
  policyCompatible : Lens.allowsContradictions profile

/-- Default QM lens profile (paraconsistent, contradiction-tolerant). -/
def defaultQMProfile : Lens.LensProfile :=
  { name := "QM-Contextual"
    contradictionPolicy := Lens.ContradictionPolicy.paraconsistent
    dimension := 2
    languageTag := "quantum-contextual"
    metricTag := "hilbert" }

@[simp] theorem defaultQMProfile_allowsContradictions :
    Lens.allowsContradictions defaultQMProfile := by
  simp [defaultQMProfile, Lens.allowsContradictions]

/-- Canonical triangle-based QM binding. -/
def triangleBinding : QMLensBinding :=
  { profile := defaultQMProfile
    witness := Triangle.witness
    policyCompatible := defaultQMProfile_allowsContradictions }

/-- Any QM binding carries a certified global obstruction witness. -/
theorem witness_global_obstruction (B : QMLensBinding) :
    NoGlobalSection B.witness.X B.witness.cover B.witness.e
      (fun {C} hC => B.witness.coverSubX (C := C) hC) :=
  B.witness.noGlobal

/-- Triangle binding specialization. -/
theorem triangleBinding_global_obstruction :
    NoGlobalSection triangleBinding.witness.X
      triangleBinding.witness.cover
      triangleBinding.witness.e
      (fun {C} hC => triangleBinding.witness.coverSubX (C := C) hC) :=
  witness_global_obstruction triangleBinding

end QMTrack
end Extensions
end PerspectivalPlenum
end HeytingLean
