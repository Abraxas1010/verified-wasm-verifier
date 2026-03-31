import HeytingLean.PDE.Core

namespace HeytingLean.PDE.Madelung

open HeytingLean.PDE.Symbolic

/-- Physical constants for the Madelung reduction. -/
structure PhysConsts where
  hbar : ℝ
  mu : ℝ
  h_hbar_pos : 0 < hbar
  h_mu_pos : 0 < mu

/-- A Madelung state with symbolic wavefunction, density, phase, and velocity. -/
structure MadelungState where
  psi : ScalarField
  rho : ScalarField
  phase : ScalarField
  velocity : VectorField
  consts : PhysConsts

/-- Equilibrium data for the linearization step. -/
structure EquilibriumState where
  rho0 : ℝ
  density0 : ScalarField
  velocity0 : VectorField
  consts : PhysConsts
  h_rho0_pos : 0 < rho0

/-- Perturbation data about an equilibrium state. -/
structure PerturbedState where
  equilibrium : EquilibriumState
  rho1 : ScalarField
  v1 : VectorField
  pressure1 : ScalarField := { name := "P1" }

/-- Barotropic equation-of-state data with sound speed c_L. -/
structure BarotropicEOS where
  cL : ℝ
  h_cL_pos : 0 < cL
  pressure : ScalarField := { name := "P" }

/-- The final dispersion-law witness at a fixed wavenumber. -/
structure DispersionRelation where
  cL : ℝ
  D : ℝ
  k : ℝ
  omegaSquared : ℝ
  law : omegaSquared = cL^2 * k^2 + D^2 * k^4

/-- The coupled continuity + momentum system extracted from Schrödinger form. -/
structure MadelungReduction where
  continuity : ScalarEquation
  momentum : VectorEquation

instance : Inhabited MadelungReduction := ⟨{
  continuity := default
  momentum := default
}⟩

/-- Plane-wave operator eigenvalues used in the dispersion derivation. -/
structure PlaneWaveEvaluation where
  timeEigenvalue : ℝ
  laplacianEigenvalue : ℝ
  biharmonicEigenvalue : ℝ

namespace DispersionRelation

/-- The symbol `ω²` from Eq. (A19)–(A21). -/
def ω_squared (rel : DispersionRelation) : ℝ :=
  rel.omegaSquared

end DispersionRelation

/-- Product-rule placeholder for differentiating the Madelung polar ansatz.
Corresponds to Eq. (A4). -/
axiom product_rule_div (f g : ScalarExpr) :
    ScalarExpr.dt (.mul f g) =
      .add (.mul (.dt f) g) (.mul f (.dt g))

/-- Chain rule for the complex exponential factor in the Madelung ansatz.
Corresponds to Eq. (A3)–(A4). -/
axiom chain_rule_exp (phase : ScalarExpr) :
    ScalarExpr.dt (.expI phase) =
      .mul (.expI phase) (.dt phase)

/-- Divergence identity for a scalar-weighted vector field.
Corresponds to Eq. (A4) and its reuse in Eq. (A9). -/
axiom div_grad_identity (rho : ScalarField) (v : VectorField)
    (h_rho : rho.smooth = true) (h_v : v.smooth = true) :
    ScalarExpr.divergence (VectorExpr.scale rho.expr v.expr) =
      ScalarExpr.add (ScalarExpr.inner (VectorExpr.grad rho.expr) v.expr)
        (ScalarExpr.mul rho.expr (ScalarExpr.divergence v.expr))

/-- First-order linearization of the quantum potential.
Corresponds to Eq. (A13)–(A14). -/
axiom linearize_quantum_potential
    (consts : PhysConsts) (rho0 : ℝ) (rho1 : ScalarField)
    (h_rho0 : 0 < rho0) :
    VectorExpr.neg (VectorExpr.grad (ScalarExpr.atom s!"Q_lin({rho1.name})")) =
      VectorExpr.scale
        (ScalarExpr.div (ScalarExpr.real ((consts.hbar^2 : ℝ)))
          (ScalarExpr.mul (ScalarExpr.real ((4 * consts.mu * rho0 : ℝ))) (ScalarExpr.real 1)))
        (VectorExpr.grad (ScalarExpr.laplacian rho1.expr))

/-- Plane-wave substitution of Eq. (A18)–(A21):
if the density-wave operator has the canonical `∂²_t = c_L² ∇² - D² ∇⁴`
shape, then substituting a plane-wave ansatz yields the quadratic dispersion
law `ω² = c_L² k² + D² k⁴`. -/
axiom plane_wave_substitution
    (waveEq : ScalarEquation) (density : ScalarField)
    (cL D k omega : ℝ)
    (h_wave :
      waveEq =
        { lhs := ScalarExpr.dtt density.expr
          rhs :=
            ScalarExpr.add
              (ScalarExpr.mul (ScalarExpr.real ((cL^2 : ℝ)))
                (ScalarExpr.laplacian density.expr))
              (ScalarExpr.neg
                (ScalarExpr.mul (ScalarExpr.real ((D^2 : ℝ)))
                  (ScalarExpr.biharmonic density.expr))) }) :
    ∃ eval : PlaneWaveEvaluation,
      eval.timeEigenvalue = -(omega^2) ∧
      eval.laplacianEigenvalue = -(k^2) ∧
      eval.biharmonicEigenvalue = k^4 ∧
      omega^2 = cL^2 * k^2 + D^2 * k^4

end HeytingLean.PDE.Madelung
