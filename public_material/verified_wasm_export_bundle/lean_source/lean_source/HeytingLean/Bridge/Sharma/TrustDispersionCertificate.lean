import HeytingLean.Bridge.Sharma.TrustDispersion
import HeytingLean.PDE.Madelung.LinearizedDispersion

/-!
# Trust Dispersion Certificates

Frequency-domain certificates for trust-density perturbations derived from the
Aether governor, together with the one-step convergence regime needed to tie
them back to the existing governor proofs.
-/

namespace HeytingLean.Bridge.Sharma.TrustDispersion

open HeytingLean.Bridge.Sharma.AetherGovernor
open HeytingLean.Bridge.Sharma.AetherGovernorConvergence
open HeytingLean.PDE.Madelung

noncomputable section

/-- A one-step governor operating point in the exact no-clamp, from-rest
regime already analyzed by the Aether governor proofs. -/
structure TrustOperatingPoint (field : TrustDensityField) where
  state : GovState
  delta : ℝ
  hDelta : 0 < delta
  hEpsPos : 0 < state.eps
  hStateLo : field.govParams.epsMin ≤ state.eps
  hStateHi : state.eps ≤ field.govParams.epsMax
  hNoClampLo :
    field.govParams.epsMin ≤
      state.eps + govAdjustment field.govParams state delta field.dt
  hNoClampHi :
    state.eps + govAdjustment field.govParams state delta field.dt ≤
      field.govParams.epsMax
  hPrev : state.ePrev = 0
  hGammaTargetLeEps :
    (field.govParams.alpha + field.govParams.beta / field.dt) *
        field.govParams.target ≤
      state.eps

namespace TrustDensityField

theorem dispersionCoefficient_eq_infoFriction (field : TrustDensityField) :
    dispersion_coefficient field.toEquilibriumState.consts = field.physics.infoFriction := by
  simp [TrustDensityField.toEquilibriumState, dispersion_coefficient]

end TrustDensityField

namespace TrustOperatingPoint

/-- Exact one-step contraction factor inherited from the governor analysis. -/
noncomputable def exactContractionFactor {field : TrustDensityField}
    (op : TrustOperatingPoint field) : ℝ :=
  contractionRho field.govParams op.state op.delta field.dt

theorem exactContractionFactor_mem_Ioo {field : TrustDensityField}
    (op : TrustOperatingPoint field) :
    0 ≤ op.exactContractionFactor ∧ op.exactContractionFactor < 1 := by
  constructor
  · exact contractionRho_nonneg field.govParams op.state op.delta field.dt
      field.assumptions.hDt op.hDelta op.hEpsPos op.hGammaTargetLeEps
  · exact contractionRho_lt_one field.govParams op.state op.delta field.dt
      field.assumptions.hDt op.hDelta op.hEpsPos op.hGammaTargetLeEps

theorem lyapunov_descent {field : TrustDensityField}
    (op : TrustOperatingPoint field) :
    lyapunov (govError field.govParams
        (govStep field.govParams op.state op.delta field.dt) op.delta) ≤
      lyapunov (govError field.govParams op.state op.delta) := by
  exact HeytingLean.Bridge.Sharma.AetherGovernor.lyapunov_descent
    field.govParams op.state op.delta field.dt
    field.assumptions.hDt op.hDelta op.hEpsPos
    op.hStateLo op.hStateHi
    op.hNoClampLo op.hNoClampHi op.hPrev op.hGammaTargetLeEps

end TrustOperatingPoint

/-- Frequency-domain certificate derived from a trust-density field. -/
structure TrustDispersionCertificate where
  field : TrustDensityField
  k : ℝ
  omegaSquared : ℝ
  dispersion : DispersionRelation
  governorRho : ℝ
  cL_eq : dispersion.cL = field.physics.trustElasticity
  D_eq : dispersion.D = field.physics.infoFriction
  k_eq : dispersion.k = k
  omega_eq : dispersion.omegaSquared = omegaSquared
  governorRho_eq : governorRho = field.proxyContraction
  law :
    omegaSquared =
      field.physics.trustElasticity ^ 2 * k ^ 2 +
        field.physics.infoFriction ^ 2 * k ^ 4

/-- Construct the trust-dispersion certificate at a given wavenumber. -/
noncomputable def mkTrustDispersionCertificate
    (field : TrustDensityField) (k : ℝ) : TrustDispersionCertificate where
  field := field
  k := k
  omegaSquared :=
    field.physics.trustElasticity ^ 2 * k ^ 2 +
      field.physics.infoFriction ^ 2 * k ^ 4
  dispersion := {
    cL := field.physics.trustElasticity
    D := field.physics.infoFriction
    k := k
    omegaSquared :=
      field.physics.trustElasticity ^ 2 * k ^ 2 +
        field.physics.infoFriction ^ 2 * k ^ 4
    law := rfl
  }
  governorRho := field.proxyContraction
  cL_eq := rfl
  D_eq := rfl
  k_eq := rfl
  omega_eq := rfl
  governorRho_eq := rfl
  law := rfl

theorem trust_dispersion_exists (field : TrustDensityField) (k : ℝ) :
    ∃ cert : TrustDispersionCertificate,
      cert.field = field ∧ cert.k = k ∧ cert.governorRho = field.proxyContraction := by
  refine ⟨mkTrustDispersionCertificate field k, rfl, rfl, rfl⟩

theorem omegaSquared_nonneg (cert : TrustDispersionCertificate) :
    0 ≤ cert.omegaSquared := by
  rw [cert.law]
  positivity

theorem governorRho_mem_Ioo (cert : TrustDispersionCertificate) :
    0 < cert.governorRho ∧ cert.governorRho < 1 := by
  simpa [cert.governorRho_eq] using cert.field.proxyContraction_mem_Ioo

/-- If the dispersive term dominates the wave term at wavenumber `k`, the
resulting frequency is bounded by twice the dispersive contribution. -/
theorem high_k_dominated_by_friction
    (cert : TrustDispersionCertificate)
    (hDominates :
      cert.field.physics.trustElasticity ^ 2 ≤
        cert.field.physics.infoFriction ^ 2 * cert.k ^ 2) :
    cert.omegaSquared ≤
      2 * cert.field.physics.infoFriction ^ 2 * cert.k ^ 4 := by
  have hk2 : 0 ≤ cert.k ^ 2 := by positivity
  have hScaled :
      cert.field.physics.trustElasticity ^ 2 * cert.k ^ 2 ≤
        (cert.field.physics.infoFriction ^ 2 * cert.k ^ 2) * cert.k ^ 2 := by
    exact mul_le_mul_of_nonneg_right hDominates hk2
  have hk4 : cert.k ^ 4 = cert.k ^ 2 * cert.k ^ 2 := by ring
  have hWaveLeDisp :
      cert.field.physics.trustElasticity ^ 2 * cert.k ^ 2 ≤
        cert.field.physics.infoFriction ^ 2 * cert.k ^ 4 := by
    simpa [hk4, mul_assoc, mul_left_comm, mul_comm] using hScaled
  rw [cert.law]
  nlinarith

namespace TrustOperatingPoint

noncomputable def toCertificate {field : TrustDensityField}
    (_op : TrustOperatingPoint field) (k : ℝ) : TrustDispersionCertificate :=
  mkTrustDispersionCertificate field k

end TrustOperatingPoint

end

end HeytingLean.Bridge.Sharma.TrustDispersion
