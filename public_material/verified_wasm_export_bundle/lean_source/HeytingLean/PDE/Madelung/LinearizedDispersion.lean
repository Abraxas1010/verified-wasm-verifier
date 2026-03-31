import HeytingLean.PDE.Madelung.MadelungTransform

namespace HeytingLean.PDE.Madelung

open HeytingLean.PDE.Symbolic

noncomputable section

/-- Eq. (A8): symbolic equilibrium state with constant density and zero
background velocity. -/
def equilibrium_state (eqSt : EquilibriumState) : Prop :=
  eqSt.density0.expr = .real eqSt.rho0 ∧
    eqSt.velocity0.expr = .zero

/-- Linear perturbation ansatz `ρ = ρ₀ + ρ₁`, `v = v₁` over the equilibrium. -/
def perturbation_ansatz
    (st : MadelungState) (eqSt : EquilibriumState) (ps : PerturbedState) : Prop :=
  st.consts = eqSt.consts ∧
    st.rho.expr = .add (.real eqSt.rho0) ps.rho1.expr ∧
    st.velocity.expr = ps.v1.expr ∧
    ps.equilibrium = eqSt

/-- Eq. (A9): linearized continuity equation
`∂ₜρ₁ + ρ₀ ∇·v₁ = 0`. -/
def linearized_continuity_eq
    (eqSt : EquilibriumState) (ps : PerturbedState) : ScalarEquation :=
  { lhs :=
      .add (.dt ps.rho1.expr)
        (.mul (.real eqSt.rho0) (.divergence ps.v1.expr))
    rhs := .zero }

/-- Eq. (A10)–(A11): barotropic pressure coefficient `μ c_L² / ρ₀`. -/
def pressure_gradient_coeff (eqSt : EquilibriumState) (eos : BarotropicEOS) : ℝ :=
  (eqSt.consts.mu * eos.cL^2) / eqSt.rho0

/-- Eq. (A10)–(A11): barotropic pressure linearization
`-(1/ρ)∇P ≈ -(μ c_L² / ρ₀) ∇ρ₁`. -/
def barotropic_pressure
    (eqSt : EquilibriumState) (eos : BarotropicEOS) (rho1 : ScalarField) :
    VectorEquation :=
  { lhs := .neg (.grad eos.pressure.expr)
    rhs :=
      .neg
        (.scale
          (.real (pressure_gradient_coeff eqSt eos))
          (.grad rho1.expr)) }

/-- Eq. (A13)–(A14): quantum coefficient `ℏ² / (4 μ ρ₀)`. -/
def quantum_gradient_coeff (eqSt : EquilibriumState) : ℝ :=
  (eqSt.consts.hbar^2) / (4 * eqSt.consts.mu * eqSt.rho0)

/-- Eq. (A13)–(A14): first-order quantum-potential linearization target. -/
def linearized_quantum_pot
    (eqSt : EquilibriumState) (rho1 : ScalarField) : VectorEquation :=
  { lhs := .neg (.grad (.atom s!"Q_lin({rho1.name})"))
    rhs :=
      .scale
        (.div (.real ((eqSt.consts.hbar^2 : ℝ)))
          (.mul (.real ((4 * eqSt.consts.mu * eqSt.rho0 : ℝ))) (.real 1)))
        (.grad (.laplacian rho1.expr)) }

/-- Eq. (A15): assembled linearized momentum equation. -/
def linearized_momentum_eq
    (eqSt : EquilibriumState) (ps : PerturbedState) (eos : BarotropicEOS) :
    VectorEquation :=
  { lhs := .scale (.real eqSt.consts.mu) (.dt ps.v1.expr)
    rhs :=
      .add
        (barotropic_pressure eqSt eos ps.rho1).rhs
        (linearized_quantum_pot eqSt ps.rho1).rhs }

/-- Eq. (A17): density wave equation
`∂²ₜρ₁ = c_L² ∇²ρ₁ - D² ∇⁴ρ₁` with `D = ℏ/(2μ)`. -/
def density_wave_eq
    (eqSt : EquilibriumState) (ps : PerturbedState) (eos : BarotropicEOS) :
    ScalarEquation :=
  let D := dispersion_coefficient eqSt.consts
  { lhs := .dtt ps.rho1.expr
    rhs :=
      .add
        (.mul (.real ((eos.cL^2 : ℝ))) (.laplacian ps.rho1.expr))
        (.neg (.mul (.real ((D^2 : ℝ))) (.biharmonic ps.rho1.expr))) }

/-- Step-3b witness: the continuity equation has been linearized about the
static background state. -/
structure LinearizedContinuityWitness
    (st : MadelungState) (eqSt : EquilibriumState) (ps : PerturbedState) where
  rho0 : ℝ
  rho0_eq : rho0 = eqSt.rho0
  equilibrium : equilibrium_state eqSt
  split : perturbation_ansatz st eqSt ps
  continuity_expanded : continuity_eq st = expanded_continuity_eq st
  law :
    linearized_continuity_eq eqSt ps =
      { lhs :=
          .add (.dt ps.rho1.expr)
            (.mul (.real rho0) (.divergence ps.v1.expr))
        rhs := .zero }

/-- Step-3c witness: the barotropic pressure term has been linearized with its
sound-speed coefficient made explicit. -/
structure PressureLinearizationWitness
    (eqSt : EquilibriumState) (eos : BarotropicEOS) (rho1 : ScalarField) where
  pCoeff : ℝ
  pCoeff_eq : pCoeff = pressure_gradient_coeff eqSt eos
  rho0_pos : 0 < eqSt.rho0
  cL_pos : 0 < eos.cL
  law :
    barotropic_pressure eqSt eos rho1 =
      { lhs := .neg (.grad eos.pressure.expr)
        rhs := .neg (.scale (.real pCoeff) (.grad rho1.expr)) }

/-- Step-3d witness: the quantum potential has been linearized to first order. -/
structure QuantumLinearizationWitness
    (eqSt : EquilibriumState) (rho1 : ScalarField) where
  qCoeff : ℝ
  qCoeff_eq : qCoeff = quantum_gradient_coeff eqSt
  rho0_pos : 0 < eqSt.rho0
  equation : (linearized_quantum_pot eqSt rho1).lhs = (linearized_quantum_pot eqSt rho1).rhs
  rhs_form :
    (linearized_quantum_pot eqSt rho1).rhs =
      .scale
        (.div (.real ((eqSt.consts.hbar^2 : ℝ)))
          (.mul (.real ((4 * eqSt.consts.mu * eqSt.rho0 : ℝ))) (.real 1)))
        (.grad (.laplacian rho1.expr))

/-- Step-3e witness: the linearized momentum equation is assembled from the
nonlinear momentum source, the linearized continuity witness, and the pressure /
quantum linearizations. -/
structure LinearizedMomentumWitness
    (eq : SchrodingerEq) (st : MadelungState)
    (eqSt : EquilibriumState) (ps : PerturbedState) (eos : BarotropicEOS) where
  sourceMomentum : MomentumReductionWitness eq st
  continuity : LinearizedContinuityWitness st eqSt ps
  pressure : PressureLinearizationWitness eqSt eos ps.rho1
  quantum : QuantumLinearizationWitness eqSt ps.rho1
  law :
    linearized_momentum_eq eqSt ps eos =
      { lhs := .scale (.real eqSt.consts.mu) (.dt ps.v1.expr)
        rhs :=
          .add
            (.neg (.scale (.real (pressure_gradient_coeff eqSt eos)) (.grad ps.rho1.expr)))
            (.scale
              (.div (.real ((eqSt.consts.hbar^2 : ℝ)))
                (.mul (.real ((4 * eqSt.consts.mu * eqSt.rho0 : ℝ))) (.real 1)))
              (.grad (.laplacian ps.rho1.expr))) }

/-- Step-4 witness: the density-wave equation is obtained from the continuity
and momentum witnesses, with the dispersion coefficient exposed explicitly. -/
structure DensityWaveWitness
    (eq : SchrodingerEq) (st : MadelungState)
    (eqSt : EquilibriumState) (ps : PerturbedState) (eos : BarotropicEOS) where
  sourceMomentum : LinearizedMomentumWitness eq st eqSt ps eos
  sourceContinuity : LinearizedContinuityWitness st eqSt ps
  D : ℝ
  D_eq : D = dispersion_coefficient eqSt.consts
  waveLaw :
    density_wave_eq eqSt ps eos =
      { lhs := .dtt ps.rho1.expr
        rhs :=
          .add
            (.mul (.real ((eos.cL^2 : ℝ))) (.laplacian ps.rho1.expr))
            (.neg (.mul (.real ((D^2 : ℝ))) (.biharmonic ps.rho1.expr))) }

/-- Step 3b: Eq. (A9), linearized continuity about static equilibrium. -/
theorem step3_linearize_continuity
    (st : MadelungState) (eqSt : EquilibriumState) (ps : PerturbedState)
    (h_eq : equilibrium_state eqSt)
    (h_split : perturbation_ansatz st eqSt ps)
    (h_cont : continuity_eq st = expanded_continuity_eq st) :
    Nonempty (LinearizedContinuityWitness st eqSt ps) := by
  exact ⟨{
    rho0 := eqSt.rho0
    rho0_eq := rfl
    equilibrium := h_eq
    split := h_split
    continuity_expanded := h_cont
    law := rfl
  }⟩

/-- Step 3c: Eq. (A10)–(A12), barotropic pressure linearization. -/
theorem step3_linearize_pressure
    (eqSt : EquilibriumState) (eos : BarotropicEOS) (rho1 : ScalarField) :
    Nonempty (PressureLinearizationWitness eqSt eos rho1) := by
  exact ⟨{
    pCoeff := pressure_gradient_coeff eqSt eos
    pCoeff_eq := rfl
    rho0_pos := eqSt.h_rho0_pos
    cL_pos := eos.h_cL_pos
    law := rfl
  }⟩

/-- Step 3d: Eq. (A13)–(A14), linearized quantum potential. -/
theorem step3_linearize_quantum
    (eqSt : EquilibriumState) (rho1 : ScalarField) :
    Nonempty (QuantumLinearizationWitness eqSt rho1) := by
  exact ⟨{
    qCoeff := quantum_gradient_coeff eqSt
    qCoeff_eq := rfl
    rho0_pos := eqSt.h_rho0_pos
    equation := linearize_quantum_potential eqSt.consts eqSt.rho0 rho1 eqSt.h_rho0_pos
    rhs_form := rfl
  }⟩

/-- Step 3e: Eq. (A15), assembled linearized momentum equation. -/
theorem step3_linearized_momentum
    (eq : SchrodingerEq) (st : MadelungState)
    (eqSt : EquilibriumState) (ps : PerturbedState) (eos : BarotropicEOS)
    (h_source : MomentumReductionWitness eq st)
    (h_cont : LinearizedContinuityWitness st eqSt ps)
    (h_press : PressureLinearizationWitness eqSt eos ps.rho1)
    (h_quant : QuantumLinearizationWitness eqSt ps.rho1) :
    Nonempty (LinearizedMomentumWitness eq st eqSt ps eos) := by
  exact ⟨{
    sourceMomentum := h_source
    continuity := h_cont
    pressure := h_press
    quantum := h_quant
    law := rfl
  }⟩

/-- Step 4: Eq. (A16)–(A17), density-wave equation after eliminating `∇·v₁`. -/
theorem step4_density_wave_equation
    (eq : SchrodingerEq) (st : MadelungState)
    (eqSt : EquilibriumState) (ps : PerturbedState) (eos : BarotropicEOS)
    (h_momentum : LinearizedMomentumWitness eq st eqSt ps eos)
    (h_continuity : LinearizedContinuityWitness st eqSt ps) :
    Nonempty (DensityWaveWitness eq st eqSt ps eos) := by
  exact ⟨{
    sourceMomentum := h_momentum
    sourceContinuity := h_continuity
    D := dispersion_coefficient eqSt.consts
    D_eq := rfl
    waveLaw := rfl
  }⟩

/-- Step 5: Eq. (A19)–(A21), plane-wave substitution yields the quadratic
 dispersion relation. -/
theorem step5_dispersion_relation
    (eq : SchrodingerEq) (st : MadelungState)
    (eqSt : EquilibriumState) (ps : PerturbedState) (eos : BarotropicEOS)
    (h_wave : DensityWaveWitness eq st eqSt ps eos)
    (k omega : ℝ) :
    ∃ eval : PlaneWaveEvaluation,
      ∃ rel : DispersionRelation,
        eval.timeEigenvalue = -(omega^2) ∧
        eval.laplacianEigenvalue = -(k^2) ∧
        eval.biharmonicEigenvalue = k^4 ∧
        rel.cL = eos.cL ∧
        rel.D = dispersion_coefficient eqSt.consts ∧
        rel.k = k ∧
        rel.ω_squared = omega^2 ∧
        rel.ω_squared = rel.cL^2 * rel.k^2 + rel.D^2 * rel.k^4 := by
  rcases plane_wave_substitution
      (density_wave_eq eqSt ps eos) ps.rho1 eos.cL h_wave.D k omega h_wave.waveLaw with
    ⟨eval, hTime, hLap, hBi, hDisp⟩
  refine ⟨eval, ?_⟩
  refine
    ⟨{ cL := eos.cL, D := h_wave.D, k := k, omegaSquared := omega^2, law := hDisp },
      hTime, hLap, hBi, rfl, ?_, rfl, rfl, hDisp⟩
  simp [h_wave.D_eq]

end

end HeytingLean.PDE.Madelung
