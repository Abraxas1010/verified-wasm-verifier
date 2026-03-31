import HeytingLean.PDE.Madelung.MadelungTypes

namespace HeytingLean.PDE.Madelung

open HeytingLean.PDE.Symbolic

noncomputable section

/-- Eq. (A1): symbolic time-dependent Schrödinger specification. -/
structure SchrodingerEq where
  psi : ScalarField
  potential : ScalarField
  consts : PhysConsts
  pdeClass : HeytingLean.PDE.PDEClass := .parabolic

/-- Eq. (A1): symbolic Schrödinger equation
`iℏ ∂ψ/∂t = -(ℏ²/2μ) ∇² ψ + V ψ`. -/
def schrodinger_eq (eq : SchrodingerEq) : ScalarEquation :=
  { lhs := .mul (.atom "i_hbar") (.dt eq.psi.expr)
    rhs :=
      .add
        (.neg
          (.mul
            (.div (.real ((eq.consts.hbar^2 : ℝ))) (.real ((2 * eq.consts.mu : ℝ))))
            (.laplacian eq.psi.expr)))
        (.mul eq.potential.expr eq.psi.expr) }

/-- Eq. (A2)–(A3): Madelung polar ansatz `ψ = √ρ exp(i S / ℏ)` with
velocity `v = ∇S / μ`. -/
def madelungDecomposition (st : MadelungState) : Prop :=
  st.psi.expr =
      .mul (.sqrt st.rho.expr)
        (.expI (.div st.phase.expr (.real st.consts.hbar))) ∧
    st.velocity.expr =
      .scale (.div (.real 1) (.real st.consts.mu)) (.grad st.phase.expr)

/-- Eq. (A6): symbolic quantum potential `Q = -(ℏ²/2μ) (∇²√ρ)/√ρ`. -/
def quantumPotential (consts : PhysConsts) (rho : ScalarField) : ScalarExpr :=
  .neg
    (.mul
      (.div (.real ((consts.hbar^2 : ℝ))) (.real ((2 * consts.mu : ℝ))))
      (.div (.laplacian (.sqrt rho.expr)) (.sqrt rho.expr)))

/-- Eq. (A20): the dispersion coefficient `D = ℏ / (2μ)`. -/
def dispersion_coefficient (consts : PhysConsts) : ℝ :=
  consts.hbar / (2 * consts.mu)

end

end HeytingLean.PDE.Madelung
