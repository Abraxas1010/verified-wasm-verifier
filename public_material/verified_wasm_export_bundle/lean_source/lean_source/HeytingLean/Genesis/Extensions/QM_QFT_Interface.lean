import HeytingLean.Genesis.WitnessInterior
import HeytingLean.Genesis.ObserverV2
import HeytingLean.PerspectivalPlenum.Extensions

/-!
# Genesis.Extensions.QM_QFT_Interface

Phase-12 interface-safe extension bridges from Genesis witness interiors into
existing Perspectival Plenum QM/QFT extension tracks.
-/

namespace HeytingLean.Genesis.Extensions

open HeytingLean.PerspectivalPlenum
open HeytingLean.PerspectivalPlenum.Extensions
open HeytingLean.Quantum.Contextuality

/-- Minimal precondition required for extension exports from Genesis interiors. -/
def minimalPrecondition (W : WitnessInterior) : Prop :=
  0 < W.depth

theorem minimalPrecondition_holds (W : WitnessInterior) : minimalPrecondition W :=
  W.postReentry

/-- Canonical obstruction proposition carried by the QM track triangle witness. -/
abbrev TriangleObstruction : Prop :=
  NoGlobalSection
    QMTrack.triangleBinding.witness.X
    QMTrack.triangleBinding.witness.cover
    QMTrack.triangleBinding.witness.e
    (fun {C} hC => QMTrack.triangleBinding.witness.coverSubX (C := C) hC)

/-- Interface object for QM-facing exports. -/
structure QMInterface where
  profile : Lens.LensProfile
  allowsContradictions : Lens.allowsContradictions profile
  obstruction : TriangleObstruction

/-- Witness-interior export into the QM extension interface. -/
def witnessInterior_toQMInterface (_W : WitnessInterior) : QMInterface :=
  { profile := QMTrack.defaultQMProfile
    allowsContradictions := QMTrack.defaultQMProfile_allowsContradictions
    obstruction := QMTrack.triangleBinding_global_obstruction }

theorem witnessInterior_toQMInterface_policy (W : WitnessInterior) :
    Lens.allowsContradictions (witnessInterior_toQMInterface W).profile :=
  (witnessInterior_toQMInterface W).allowsContradictions

theorem witnessInterior_toQMInterface_obstruction (W : WitnessInterior) :
    TriangleObstruction :=
  (witnessInterior_toQMInterface W).obstruction

/-- Interface object for QFT-facing exports on the current concrete scaffold. -/
structure QFTInterface where
  scaffold : QFTTrack.QFTScaffold (Set Unit)
  profileDimensionPositive : 0 < scaffold.observerProfile.dimension

/-- Witness-interior export into the QFT extension interface. -/
def witnessInterior_toQFTInterface (_W : WitnessInterior) : QFTInterface :=
  { scaffold := QFTTrack.toyScaffold
    profileDimensionPositive := by decide }

theorem witnessInterior_toQFTInterface_counterterms_disallowed (W : WitnessInterior) :
    ¬ QFTTrack.policyAllowsCounterterms (witnessInterior_toQFTInterface W).scaffold := by
  simp [witnessInterior_toQFTInterface, QFTTrack.strictToyProfile_disallows_counterterms]

/--
Conditional bridge theorem: if a QFT scaffold disallows contradiction policies,
the Genesis export remains in the strict counterterm-disallowed regime.
-/
theorem qft_bridge_strict_policy (W : WitnessInterior) :
    ¬ QFTTrack.policyAllowsCounterterms (witnessInterior_toQFTInterface W).scaffold :=
  witnessInterior_toQFTInterface_counterterms_disallowed W

end HeytingLean.Genesis.Extensions
