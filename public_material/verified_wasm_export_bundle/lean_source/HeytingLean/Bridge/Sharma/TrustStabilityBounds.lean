import HeytingLean.Bridge.Sharma.TrustDispersionCertificate
import Lean.Data.Json

/-!
# Trust Stability Bounds

Dashboard-facing stability bounds extracted from trust-dispersion certificates.
The proof-facing layer stays in `ℝ`; the export-facing layer uses `Float`.
-/

namespace HeytingLean.Bridge.Sharma.TrustDispersion

open Lean

noncomputable section

/-- A quantitative frequency-domain stability bound at a fixed wavenumber. -/
structure StabilityBound where
  k : ℝ
  omegaSquaredBound : ℝ
  trustElasticity : ℝ
  infoFriction : ℝ
  candidateRho : ℝ
  hBound :
    omegaSquaredBound =
      trustElasticity ^ 2 * k ^ 2 + infoFriction ^ 2 * k ^ 4

/-- Extract a stability bound from a dispersion certificate. -/
noncomputable def TrustDispersionCertificate.toStabilityBound
    (cert : TrustDispersionCertificate) : StabilityBound where
  k := cert.k
  omegaSquaredBound := cert.omegaSquared
  trustElasticity := cert.field.physics.trustElasticity
  infoFriction := cert.field.physics.infoFriction
  candidateRho := cert.governorRho
  hBound := cert.law

/-- The wavenumber where the wave and dispersive contributions are equal. -/
noncomputable def crossoverWavenumber (cL D : ℝ) (_hD : 0 < D) : ℝ :=
  cL / D

theorem crossover_is_balance_point
    (cL D : ℝ) (h_cL : 0 < cL) (h_D : 0 < D) :
    let k_c := crossoverWavenumber cL D h_D
    cL ^ 2 * k_c ^ 2 = D ^ 2 * k_c ^ 4 := by
  dsimp [crossoverWavenumber]
  have hD0 : D ≠ 0 := ne_of_gt h_D
  have h2D0 : 2 * D ≠ 0 := by positivity
  field_simp [hD0, h2D0]

def stabilityRegime (k crossoverK : Float) : String :=
  if k < crossoverK then "wave-like" else "dispersion-dominated"

/-- Computable dashboard export for the stability bound. -/
structure StabilityBoundExport where
  wavenumberK : Float
  omegaSquared : Float
  trustElasticity : Float
  infoFriction : Float
  candidateRho : Float
  crossoverK : Float
  regime : String
  deriving Repr, ToJson, FromJson

def mkStabilityBoundExport
    (trustElasticity infoFriction candidateRho k : Float) :
    StabilityBoundExport :=
  let crossoverK := trustElasticity / infoFriction
  {
    wavenumberK := k
    omegaSquared := trustElasticity ^ 2 * k ^ 2 + infoFriction ^ 2 * k ^ 4
    trustElasticity := trustElasticity
    infoFriction := infoFriction
    candidateRho := candidateRho
    crossoverK := crossoverK
    regime := stabilityRegime k crossoverK
  }

end

end HeytingLean.Bridge.Sharma.TrustDispersion
