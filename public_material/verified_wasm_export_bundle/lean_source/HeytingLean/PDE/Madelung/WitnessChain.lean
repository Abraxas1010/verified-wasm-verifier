import HeytingLean.Core.WitnessChain
import HeytingLean.PDE.Madelung.LinearizedDispersion

namespace HeytingLean.PDE.Madelung

open HeytingLean.Core

instance {eq : SchrodingerEq} {st : MadelungState} :
    IsChainRoot (Step1Witness eq st) where
  rootEvidence _ := True

instance {st : MadelungState} {eqSt : EquilibriumState} {ps : PerturbedState} :
    IsChainRoot (LinearizedContinuityWitness st eqSt ps) where
  rootEvidence _ := True

instance
    {eqSt : EquilibriumState} {eos : BarotropicEOS}
    {rho1 : HeytingLean.PDE.Symbolic.ScalarField} :
    IsChainRoot (PressureLinearizationWitness eqSt eos rho1) where
  rootEvidence _ := True

instance
    {eqSt : EquilibriumState}
    {rho1 : HeytingLean.PDE.Symbolic.ScalarField} :
    IsChainRoot (QuantumLinearizationWitness eqSt rho1) where
  rootEvidence _ := True

instance {eq : SchrodingerEq} {st : MadelungState} :
    IsWitnessStep (MomentumReductionWitness eq st) where
  Upstream := Step1Witness eq st
  upstream w := w.step1

instance
    {eq : SchrodingerEq} {st : MadelungState}
    {eqSt : EquilibriumState} {ps : PerturbedState} {eos : BarotropicEOS} :
    IsWitnessStep (LinearizedMomentumWitness eq st eqSt ps eos) where
  Upstream := MomentumReductionWitness eq st
  upstream w := w.sourceMomentum

instance
    {eq : SchrodingerEq} {st : MadelungState}
    {eqSt : EquilibriumState} {ps : PerturbedState} {eos : BarotropicEOS} :
    IsWitnessStep (DensityWaveWitness eq st eqSt ps eos) where
  Upstream := LinearizedMomentumWitness eq st eqSt ps eos
  upstream w := w.sourceMomentum

/--
The reusable witness-chain API follows the momentum thread through the
Madelung derivation, but the density-wave witness still carries an independent
continuity witness. The wrapper is a linear projection of a larger DAG.
-/
theorem density_wave_has_continuity_source
    {eq : SchrodingerEq} {st : MadelungState}
    {eqSt : EquilibriumState} {ps : PerturbedState} {eos : BarotropicEOS}
    (w : DensityWaveWitness eq st eqSt ps eos) :
    exists hCont : LinearizedContinuityWitness st eqSt ps, w.sourceContinuity = hCont :=
  Exists.intro w.sourceContinuity rfl

end HeytingLean.PDE.Madelung
