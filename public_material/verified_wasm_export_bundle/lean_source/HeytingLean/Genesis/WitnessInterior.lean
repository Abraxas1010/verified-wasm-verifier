import HeytingLean.Genesis.Stabilization
import HeytingLean.ClosingTheLoop.Semantics.NucleusBridge

/-!
# Genesis.WitnessInterior

Phase-3 post-re-entry interior:
- interior exists only after re-entry (`0 < depth`)
- built from stabilized approximants (`unroll`)
- canonical morphism interfaces toward LensSection and BeliefState
- stabilization compatibility theorem
-/

namespace HeytingLean.Genesis

/-- Post-re-entry witness interior (depth must be strictly positive). -/
structure WitnessInterior where
  source : CoGame.{0}
  depth : Nat
  postReentry : 0 < depth

namespace WitnessInterior

/-- Stabilized approximant extracted from the source witness process. -/
noncomputable def stabilizedApprox (W : WitnessInterior) : SetTheory.PGame.{0} :=
  unroll W.depth W.source

/-- LoF-level interpreted approximant. -/
def interpretedApprox (W : WitnessInterior) : LoFExpr0 :=
  interpretUnroll W.depth W.stabilizedApprox

/-- Nucleus-closed support associated to the interpreted approximant. -/
def support (W : WitnessInterior) : Support :=
  collapseNucleus (exprSupport W.interpretedApprox)

@[simp] theorem depth_ne_zero (W : WitnessInterior) : W.depth ≠ 0 :=
  Nat.ne_of_gt W.postReentry

end WitnessInterior

/-- Canonical lens-section payload exported from a witness interior. -/
structure LensSection where
  depth : Nat
  game : SetTheory.PGame.{0}

/-- Canonical belief-state payload exported from a witness interior. -/
structure BeliefState where
  depth : Nat
  expr : LoFExpr0
  support : Support

/-- Morphism interface: targets that can ingest canonical lens sections. -/
class LensSectionLike (L : Type*) where
  ofLensSection : LensSection → L

/-- Morphism interface: targets that can ingest canonical belief states. -/
class BeliefStateLike (B : Type*) where
  ofBeliefState : BeliefState → B

/-- Canonical map `WitnessInterior → LensSection`. -/
noncomputable def toLensSection (W : WitnessInterior) : LensSection where
  depth := W.depth
  game := W.stabilizedApprox

/-- Canonical map `WitnessInterior → BeliefState`. -/
noncomputable def toBeliefState (W : WitnessInterior) : BeliefState where
  depth := W.depth
  expr := W.interpretedApprox
  support := W.support

/-- Interface-level map into any lens-section-like codomain. -/
noncomputable def toLensSectionLike (W : WitnessInterior) (L : Type*) [LensSectionLike L] : L :=
  LensSectionLike.ofLensSection (toLensSection W)

/-- Interface-level map into any belief-state-like codomain. -/
noncomputable def toBeliefStateLike (W : WitnessInterior) (B : Type*) [BeliefStateLike B] : B :=
  BeliefStateLike.ofBeliefState (toBeliefState W)

/-- Stabilization compatibility: belief-state support is a fixed point of closure. -/
theorem stabilization_compatibility (W : WitnessInterior) :
    collapseNucleus (toBeliefState W).support = (toBeliefState W).support := by
  change collapseNucleus (collapseNucleus (exprSupport W.interpretedApprox))
      = collapseNucleus (exprSupport W.interpretedApprox)
  exact collapse_idempotent (exprSupport W.interpretedApprox)

/--
Retraction bridge compatibility (conditional):
if a meet-retraction over `Support` encodes by `collapseNucleus` and decodes by identity,
its induced retraction nucleus is fixed on witness-interior support.
-/
theorem retraction_bridge_support_fixed
    (W : WitnessInterior)
    (r : HeytingLean.ClosingTheLoop.Semantics.MeetRetraction
      (α := Support) (β := Support))
    (henc : r.enc = collapseNucleus)
    (hdec : r.dec = id) :
    r.retractionNucleus W.support = W.support := by
  have hcollapse : collapseNucleus W.support = W.support :=
    stabilization_compatibility W
  calc
    r.retractionNucleus W.support = r.dec (r.enc W.support) := rfl
    _ = (id (collapseNucleus W.support)) := by simp [henc, hdec]
    _ = W.support := by simp [hcollapse]

/--
Belief-state projection variant of `retraction_bridge_support_fixed`.
-/
theorem retraction_bridge_belief_projection_fixed
    (W : WitnessInterior)
    (r : HeytingLean.ClosingTheLoop.Semantics.MeetRetraction
      (α := Support) (β := Support))
    (henc : r.enc = collapseNucleus)
    (hdec : r.dec = id) :
    r.retractionNucleus (toBeliefState W).support = (toBeliefState W).support := by
  simpa [toBeliefState] using retraction_bridge_support_fixed W r henc hdec

/-- Canonical constructor for the Life witness interior at depth `n+1`. -/
def lifeInterior (n : Nat) : WitnessInterior where
  source := CoGame.Life
  depth := n.succ
  postReentry := Nat.succ_pos n

@[simp] theorem lifeInterior_depth (n : Nat) :
    (lifeInterior n).depth = n.succ := rfl

end HeytingLean.Genesis

/--
Queue anchor theorem for `ontology_retraction_witness_interior_20260219`:
for witness interiors, meet-retraction support remains retracted fixed.
-/
theorem ontology_retraction_witness_interior_20260219
    (W : HeytingLean.Genesis.WitnessInterior)
    (r : HeytingLean.ClosingTheLoop.Semantics.MeetRetraction
      (α := HeytingLean.Genesis.Support) (β := HeytingLean.Genesis.Support))
    (henc : r.enc = HeytingLean.Genesis.collapseNucleus)
    (hdec : r.dec = id) :
    r.retractionNucleus (HeytingLean.Genesis.WitnessInterior.support W) =
      HeytingLean.Genesis.WitnessInterior.support W :=
  HeytingLean.Genesis.retraction_bridge_support_fixed (W := W) r henc hdec
