import HeytingLean.FractalUniverse.NucleusConnection.DimFlowAsNucleus
import HeytingLean.AsymptoticSafety.NucleusInstance
import HeytingLean.AsymptoticSafety.RGFlow
import HeytingLean.Core.Nucleus

/-!
# Nucleus Convergence Bridge: FractalUniverse → AsymptoticSafety

GENUINE BRIDGE: imports from both FractalUniverse and AsymptoticSafety.

The FractalUniverse's `image_has_dim_four` proof technique is:
contraction + bounded + idempotent → lt_irrefl contradiction → equality.

This module applies the same technique to AsymptoticSafety's UV-safe
projection: given a measure on `CouplingRegion` that contracts under
`rgRestrict`, the idempotency of `rgRestrict` forces the measure to
its target value — the exact same proof structure as `image_has_dim_four`.

## Bridge content

- `UVSafeContraction`: structure bundling the contraction/bounded hypotheses
  for a measure on `CouplingRegion` under `rgRestrict` (from AsymptoticSafety)
- `uvSafe_forces_target`: the image_has_dim_four technique forces equality
- `fractal_image_has_dim_four_reexport`: direct re-export of the FractalUniverse theorem
-/

namespace HeytingLean.FractalUniverse.Bridges

open NucleusConnection AsymptoticSafety

/-- The FractalUniverse contraction-to-fixed-point argument applied to
    AsymptoticSafety's UV-safe projection. Given a measure on CouplingRegion
    and contraction/bounded hypotheses analogous to NucleusCoarseGraining,
    `rgRestrict`'s idempotency forces the measure to its target.

    This is a GENUINE BRIDGE: the theorem statement references
    `BetaSystem` and `CouplingRegion` (AsymptoticSafety) and the proof
    technique comes from `image_has_dim_four` (FractalUniverse). -/
structure UVSafeContraction (sys : BetaSystem) where
  /-- Observable measure on coupling regions. -/
  measure : CouplingRegion → ℝ
  /-- Target value for the measure. -/
  target : ℝ
  /-- UV-safe restriction strictly moves the measure toward target. -/
  strict_increase : ∀ U, measure U < target →
    measure U < measure (rgRestrict sys U)
  /-- UV-safe restriction never exceeds target. -/
  bounded : ∀ U, measure (rgRestrict sys U) ≤ target

/-- The UV-safe restriction forces the measure to the target value.
    Proof reuses the exact technique from `image_has_dim_four`:
    contraction + idempotency → lt_irrefl contradiction.

    If measure(rgRestrict sys U) < target, then strict_increase gives
    measure(rgRestrict sys U) < measure(rgRestrict sys (rgRestrict sys U)).
    But rgRestrict is idempotent (from `orderNucleus`), so
    rgRestrict sys (rgRestrict sys U) = rgRestrict sys U — contradiction. -/
theorem uvSafe_forces_target (sys : BetaSystem)
    (uvc : UVSafeContraction sys) (U : CouplingRegion) :
    uvc.measure (rgRestrict sys U) = uvc.target := by
  by_contra h
  have hlt : uvc.measure (rgRestrict sys U) < uvc.target :=
    lt_of_le_of_ne (uvc.bounded U) h
  have hstrict := uvc.strict_increase (rgRestrict sys U) hlt
  -- Key step: rgRestrict is idempotent (from coreNucleus.idempotent)
  have hidemp : rgRestrict sys (rgRestrict sys U) = rgRestrict sys U :=
    (coreNucleus sys).idempotent U
  rw [hidemp] at hstrict
  exact lt_irrefl _ hstrict

/-- The FractalUniverse proof of image_has_dim_four, re-exported for
    cross-project consumption. The shared pattern is explicit:
    NucleusCoarseGraining + contraction + bounded → D_s = 4. -/
theorem fractal_image_has_dim_four_reexport
    {Geom : Type} [SemilatticeInf Geom] [OrderBot Geom]
    [HasSpectralDim Geom] (cg : NucleusCoarseGraining Geom) (G : Geom) :
    HasSpectralDim.spectral_dim (cg.coarsen G) = 4 :=
  image_has_dim_four cg G

/-- The AsymptoticSafety nucleus (coreNucleus) is a Core.Nucleus —
    making the connection to FractalUniverse's toNucleus explicit.
    Both subsystems produce Core.Nucleus instances; the bridge makes
    this shared structure visible. -/
theorem asymSafety_produces_core_nucleus (sys : BetaSystem) :
    (coreNucleus sys).R = rgRestrict sys :=
  rfl

end HeytingLean.FractalUniverse.Bridges
