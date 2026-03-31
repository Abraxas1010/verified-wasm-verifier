import HeytingLean.PDE.Madelung.LinearizedDispersion

namespace HeytingLean.PDE.Madelung

noncomputable section

/-- The canonical dispersion witness assembled from the Madelung chain. -/
def canonical_dispersion_relation
    (eqSt : EquilibriumState) (eos : BarotropicEOS) (k omega : ℝ)
    (h_law :
      omega^2 =
        eos.cL^2 * k^2 +
          (dispersion_coefficient eqSt.consts)^2 * k^4) :
    DispersionRelation :=
  let D := dispersion_coefficient eqSt.consts
  { cL := eos.cL
    D := D
    k := k
    omegaSquared := omega^2
    law := by simpa [D] using h_law }

/-- The full Madelung-to-dispersion chain from Appendix A. -/
theorem madelung_dispersion_chain
    (eq : SchrodingerEq) (st : MadelungState)
    (eqSt : EquilibriumState) (ps : PerturbedState)
    (eos : BarotropicEOS) (k omega : ℝ)
    (h_psi : eq.psi = st.psi)
    (h_decomp : madelungDecomposition st)
    (h_rho_smooth : st.rho.smooth = true)
    (h_v_smooth : st.velocity.smooth = true)
    (h_eq : equilibrium_state eqSt)
    (h_consts : st.consts = eqSt.consts)
    (h_rho_split : st.rho.expr = .add (.real eqSt.rho0) ps.rho1.expr)
    (h_velocity_split : st.velocity.expr = ps.v1.expr)
    (h_base : ps.equilibrium = eqSt) :
    ∃ wave : DensityWaveWitness eq st eqSt ps eos,
      ∃ eval : PlaneWaveEvaluation,
          ∃ rel : DispersionRelation,
          eval.timeEigenvalue = -(omega^2) ∧
          eval.laplacianEigenvalue = -(k^2) ∧
          eval.biharmonicEigenvalue = k^4 ∧
          rel.cL = eos.cL ∧
          rel.D = wave.D ∧
          rel.D = dispersion_coefficient eqSt.consts ∧
          rel.k = k ∧
          rel.ω_squared = omega^2 ∧
          rel.ω_squared = rel.cL^2 * rel.k^2 + rel.D^2 * rel.k^4 := by
  let h_step1 : Step1Witness eq st :=
    Classical.choice (step1_madelung_decomposition eq st h_psi h_decomp)
  have h_step2a := step2a_continuity_equation st h_rho_smooth h_v_smooth
  let h_step2b : MomentumReductionWitness eq st :=
    Classical.choice (step2b_momentum_equation eq st h_step1)
  have h_split : perturbation_ansatz st eqSt ps := by
    exact ⟨h_consts, h_rho_split, h_velocity_split, h_base⟩
  let h_step3b : LinearizedContinuityWitness st eqSt ps :=
    Classical.choice (step3_linearize_continuity st eqSt ps h_eq h_split h_step2a)
  let h_step3c : PressureLinearizationWitness eqSt eos ps.rho1 :=
    Classical.choice (step3_linearize_pressure eqSt eos ps.rho1)
  let h_step3d : QuantumLinearizationWitness eqSt ps.rho1 :=
    Classical.choice (step3_linearize_quantum eqSt ps.rho1)
  let h_step3e : LinearizedMomentumWitness eq st eqSt ps eos :=
    Classical.choice (step3_linearized_momentum eq st eqSt ps eos h_step2b h_step3b h_step3c h_step3d)
  let h_step4 : DensityWaveWitness eq st eqSt ps eos :=
    Classical.choice (step4_density_wave_equation eq st eqSt ps eos h_step3e h_step3b)
  rcases step5_dispersion_relation eq st eqSt ps eos h_step4 k omega with ⟨eval, rel, hTime, hLap, hBi, hCL, hD, hk, hOmega, hLaw⟩
  have hRelWaveD : rel.D = h_step4.D := by
    calc
      rel.D = dispersion_coefficient eqSt.consts := hD
      _ = h_step4.D := by simp [h_step4.D_eq]
  exact ⟨h_step4, eval, rel, hTime, hLap, hBi, hCL, hRelWaveD, hD, hk, hOmega, hLaw⟩

/-- Eq. (A20)–(A21): the dispersion coefficient is `ℏ/(2μ)`, carrying the
positivity hypotheses that justify the quotient. -/
theorem dispersion_coefficient_is_hbar_over_2mu
    (consts : PhysConsts) :
    dispersion_coefficient consts = consts.hbar / (2 * consts.mu) ∧
      0 < consts.hbar ∧
      0 < consts.mu := by
  exact ⟨rfl, consts.h_hbar_pos, consts.h_mu_pos⟩

end

end HeytingLean.PDE.Madelung
