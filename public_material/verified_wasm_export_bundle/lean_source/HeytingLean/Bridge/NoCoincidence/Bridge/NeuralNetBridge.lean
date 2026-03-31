import HeytingLean.LoF.Combinators.Topos.SheafNeuralNet

namespace HeytingLean.Bridge.NoCoincidence.Bridge

open HeytingLean.LoF.Combinators.Topos

/-- A minimal neural-net object viewed through the sheaf-neural infrastructure. -/
structure NeuralNetAsCircuit (V E : Type*) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] where
  sheaf : CellularSheaf V E
  signal : Section sheaf

/-- Structural explanation for the neural net: one nontrivial diffusion step fixes the observed
signal. This is a genuine harmonicity condition, not the universal zero-time identity. -/
def NeuralNetAsCircuit.explainedByStructure
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (N : NeuralNetAsCircuit V E) : Prop :=
  sheafDiffusion N.sheaf N.signal 1 = N.signal

/-- A neural net is structurally explained whenever its signal is fixed by unit-time diffusion. -/
theorem explainedByStructure_of_unit_time_fixed
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (N : NeuralNetAsCircuit V E)
    (hFix : sheafDiffusion N.sheaf N.signal 1 = N.signal) :
    N.explainedByStructure := hFix

/-- The bridge records a conceptual parallel with sheaf-neural harmonicity. It is not a formal
consequence of the circuit Heyting-gap theorem without additional hypotheses on the network. -/
theorem explainedByStructure_iff_unit_time_fixed
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (N : NeuralNetAsCircuit V E) :
    N.explainedByStructure ↔ sheafDiffusion N.sheaf N.signal 1 = N.signal := by
  rfl

end HeytingLean.Bridge.NoCoincidence.Bridge
