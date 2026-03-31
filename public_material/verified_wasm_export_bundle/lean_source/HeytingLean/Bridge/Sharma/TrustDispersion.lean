import HeytingLean.Bridge.Sharma.AetherGovernor
import HeytingLean.Bridge.Sharma.AetherGovernorConvergence
import HeytingLean.PDE.Madelung.MadelungTypes

/-!
# Trust Dispersion Adapter

Bridge-local adapter types that interpret Aether governor parameters as a
Madelung-style trust-density medium without modifying the audited governor or
PDE modules.
-/

namespace HeytingLean.Bridge.Sharma.TrustDispersion

open HeytingLean.Bridge.Sharma.AetherGovernor
open HeytingLean.Bridge.Sharma.AetherGovernorConvergence
open HeytingLean.PDE.Madelung

noncomputable section

/-- Extra positivity assumptions required to interpret the governor as a
dispersive trust-density medium. These assumptions stay local to the bridge. -/
structure TrustBridgeAssumptions (p : GovParams) (dt : ℝ) where
  hDt : 0 < dt
  hValidator : validatorRegime p dt
  hBetaPos : 0 < p.beta
  hTargetPos : 0 < p.target

/-- Parameters of the trust-density medium induced by the governor. -/
structure TrustPhysicsParams where
  trustElasticity : ℝ
  infoFriction : ℝ
  equilibriumTrust : ℝ
  hTrustElasticityPos : 0 < trustElasticity
  hInfoFrictionPos : 0 < infoFriction
  hEquilibriumTrustPos : 0 < equilibriumTrust

/-- Map governor parameters to trust-medium parameters.

This is a bridge definition rather than a theorem about the original governor:
- `sqrt alpha` is interpreted as the trust-wave speed.
- `beta / (2 * dt)` is interpreted as the dispersive information-friction term.
- `target` is interpreted as the equilibrium trust density. -/
noncomputable def govParamsToTrustPhysics
    (p : GovParams) (dt : ℝ) (h : TrustBridgeAssumptions p dt) :
    TrustPhysicsParams where
  trustElasticity := Real.sqrt p.alpha
  infoFriction := p.beta / (2 * dt)
  equilibriumTrust := p.target
  hTrustElasticityPos := Real.sqrt_pos_of_pos p.hAlpha
  hInfoFrictionPos := by
    have hDen : 0 < 2 * dt := by nlinarith [h.hDt]
    exact div_pos h.hBetaPos hDen
  hEquilibriumTrustPos := h.hTargetPos

/-- Governor data packaged with the bridge-local assumptions needed to interpret
it as a trust-density field. -/
structure TrustDensityField where
  govParams : GovParams
  dt : ℝ
  assumptions : TrustBridgeAssumptions govParams dt

namespace TrustDensityField

/-- Physical trust-medium parameters derived from the governor. -/
noncomputable def physics (field : TrustDensityField) : TrustPhysicsParams :=
  govParamsToTrustPhysics field.govParams field.dt field.assumptions

/-- The validator-side contraction proxy reused by the trust bridge. -/
def proxyContraction (field : TrustDensityField) : ℝ :=
  candidateRho field.govParams

theorem proxyContraction_mem_Ioo (field : TrustDensityField) :
    0 < field.proxyContraction ∧ field.proxyContraction < 1 := by
  simpa [proxyContraction] using
    candidateRho_mem_Ioo_of_validatorRegime
      field.govParams field.dt field.assumptions.hValidator

theorem trustElasticity_sq (field : TrustDensityField) :
    field.physics.trustElasticity ^ 2 = field.govParams.alpha := by
  unfold physics govParamsToTrustPhysics
  simpa using Real.sq_sqrt (le_of_lt field.govParams.hAlpha)

/-- Trust-medium constants repackaged as a Madelung equilibrium state. The
choice `mu = 1` makes the dispersive coefficient equal to `infoFriction`. -/
noncomputable def toEquilibriumState (field : TrustDensityField) : EquilibriumState where
  rho0 := field.physics.equilibriumTrust
  density0 := { name := "trust_density_0" }
  velocity0 := { name := "trust_flow_0" }
  consts := {
    hbar := 2 * field.physics.infoFriction
    mu := 1
    h_hbar_pos := by
      have hInfo : 0 < field.physics.infoFriction := field.physics.hInfoFrictionPos
      nlinarith
    h_mu_pos := by norm_num
  }
  h_rho0_pos := field.physics.hEquilibriumTrustPos

/-- Trust-medium sound speed as a barotropic equation-of-state witness. -/
noncomputable def toBarotropicEOS (field : TrustDensityField) : BarotropicEOS where
  cL := field.physics.trustElasticity
  h_cL_pos := field.physics.hTrustElasticityPos

end TrustDensityField

end

end HeytingLean.Bridge.Sharma.TrustDispersion
