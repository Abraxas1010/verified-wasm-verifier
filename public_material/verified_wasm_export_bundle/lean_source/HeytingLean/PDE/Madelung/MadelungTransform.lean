import HeytingLean.PDE.Madelung.SchrodingerSpec

namespace HeytingLean.PDE.Madelung

open HeytingLean.PDE.Symbolic

noncomputable section

/-- The polar amplitude `√ρ` from Eq. (A2). -/
def polar_amplitude (st : MadelungState) : ScalarExpr :=
  .sqrt st.rho.expr

/-- The phase factor `exp(i S / ℏ)` from Eq. (A2). -/
def polar_phase_factor (st : MadelungState) : ScalarExpr :=
  .expI (.div st.phase.expr (.real st.consts.hbar))

/-- Eq. (A4): the symbolic continuity equation `∂ₜρ + ∇·(ρv) = 0`. -/
def continuity_eq (st : MadelungState) : ScalarEquation :=
  { lhs := .add (.dt st.rho.expr) (.divergence (.scale st.rho.expr st.velocity.expr))
    rhs := .zero }

/-- Eq. (A4) with the divergence term expanded using `∇·(ρv)`. -/
def expanded_continuity_eq (st : MadelungState) : ScalarEquation :=
  { lhs :=
      .add (.dt st.rho.expr)
        (.add
          (.inner (.grad st.rho.expr) st.velocity.expr)
          (.mul st.rho.expr (.divergence st.velocity.expr)))
    rhs := .zero }

/-- Eq. (A5): the symbolic Euler-like momentum equation
`μ(∂ₜv + (v·∇)v) = -∇(V + Q)`. -/
def momentum_eq (eq : SchrodingerEq) (st : MadelungState) : VectorEquation :=
  { lhs :=
      .scale (.real st.consts.mu)
        (.add (.dt st.velocity.expr) (.convective st.velocity.expr st.velocity.expr))
    rhs :=
      .neg (.grad (.add eq.potential.expr (quantumPotential eq.consts st.rho))) }

/-- The symbolic Madelung reduction pairing continuity and momentum equations. -/
def madelung_reduction (eq : SchrodingerEq) (st : MadelungState) : MadelungReduction :=
  { continuity := continuity_eq st
    momentum := momentum_eq eq st }

/-- Step-1 witness: the polar decomposition transports the Schrödinger data into
its continuity/momentum reduction while carrying the product- and chain-rule
identities used in the substitution. -/
structure Step1Witness (eq : SchrodingerEq) (st : MadelungState) where
  red : MadelungReduction
  reduction_eq : red = madelung_reduction eq st
  psi_eq : eq.psi = st.psi
  polar_eq : st.psi.expr = .mul (polar_amplitude st) (polar_phase_factor st)
  velocity_eq :
    st.velocity.expr =
      .scale (.div (.real 1) (.real st.consts.mu)) (.grad st.phase.expr)
  product_rule_eq :
    ScalarExpr.dt (.mul (polar_amplitude st) (polar_phase_factor st)) =
      .add
        (.mul (.dt (polar_amplitude st)) (polar_phase_factor st))
        (.mul (polar_amplitude st) (.dt (polar_phase_factor st)))
  phase_rule_eq :
    ScalarExpr.dt (polar_phase_factor st) =
      .mul (polar_phase_factor st)
        (.dt (.div st.phase.expr (.real st.consts.hbar)))

/-- Step-2b witness: the Euler-like momentum equation is extracted from the same
reduction witness that produced the continuity equation. -/
structure MomentumReductionWitness (eq : SchrodingerEq) (st : MadelungState) where
  step1 : Step1Witness eq st
  continuity_eqn : step1.red.continuity = continuity_eq st
  momentum_eqn : step1.red.momentum = momentum_eq eq st

/-- Step 1: substituting the Madelung polar ansatz produces the continuity and
momentum system of Eq. (A4)–(A5), together with the required product- and
chain-rule identities used in the substitution. -/
theorem step1_madelung_decomposition
    (eq : SchrodingerEq) (st : MadelungState)
    (h_psi : eq.psi = st.psi)
    (h_decomp : madelungDecomposition st) :
    Nonempty (Step1Witness eq st) := by
  rcases h_decomp with ⟨h_psi_expr, h_velocity⟩
  have h_polar : st.psi.expr = .mul (polar_amplitude st) (polar_phase_factor st) := by
    simpa [polar_amplitude, polar_phase_factor] using h_psi_expr
  have h_prod :
      ScalarExpr.dt (.mul (polar_amplitude st) (polar_phase_factor st)) =
        .add
          (.mul (.dt (polar_amplitude st)) (polar_phase_factor st))
          (.mul (polar_amplitude st) (.dt (polar_phase_factor st))) := by
    simpa [polar_amplitude, polar_phase_factor] using
      product_rule_div (polar_amplitude st) (polar_phase_factor st)
  have h_phase :
      ScalarExpr.dt (polar_phase_factor st) =
        .mul (polar_phase_factor st)
          (.dt (.div st.phase.expr (.real st.consts.hbar))) := by
    simpa [polar_phase_factor] using
      chain_rule_exp (.div st.phase.expr (.real st.consts.hbar))
  exact ⟨{
    red := madelung_reduction eq st
    reduction_eq := rfl
    psi_eq := h_psi
    polar_eq := h_polar
    velocity_eq := h_velocity
    product_rule_eq := h_prod
    phase_rule_eq := h_phase
  }⟩

/-- Step 2a: Eq. (A4), written with the divergence term expanded after the
Madelung substitution. -/
theorem step2a_continuity_equation
    (st : MadelungState)
    (h_rho : st.rho.smooth = true) (h_v : st.velocity.smooth = true) :
    continuity_eq st = expanded_continuity_eq st := by
  have h_div := div_grad_identity st.rho st.velocity h_rho h_v
  simp [continuity_eq, expanded_continuity_eq, h_div]

/-- Step 2b: Eq. (A5), extracted from the reduction witness produced by step 1. -/
theorem step2b_momentum_equation
    (eq : SchrodingerEq) (st : MadelungState)
    (h_step1 : Step1Witness eq st) :
    Nonempty (MomentumReductionWitness eq st) := by
  have h_cont : h_step1.red.continuity = continuity_eq st := by
    simp [h_step1.reduction_eq, madelung_reduction]
  have h_mom : h_step1.red.momentum = momentum_eq eq st := by
    simp [h_step1.reduction_eq, madelung_reduction]
  exact ⟨{
    step1 := h_step1
    continuity_eqn := h_cont
    momentum_eqn := h_mom
  }⟩

end

end HeytingLean.PDE.Madelung
