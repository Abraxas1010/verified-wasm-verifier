import HeytingLean.Numbers.Surreal.Experimental.NoneistAttentionCore

namespace HeytingLean
namespace Numbers
namespace Surreal
namespace Experimental

open HeytingLean.Numbers.SurrealCore

noncomputable section

/-- Minimal neuron surface for the Noneist neural lane. -/
structure NoneistNeuron where
  gate : Nat
  bias : PreGame
  deriving Repr

private def biasToken (n : NoneistNeuron) : AttentionToken :=
  { core := n.bias, velocity := n.gate, anchor := none }

/-- Symbolic forward pass over strategy/game carriers. -/
def forwardSymbolic (n : NoneistNeuron) (t : AttentionToken) : AttentionToken :=
  if t.velocity ≤ n.gate then
    { core := PreGame.build [t.core, n.bias] []
      velocity := t.velocity.succ
      anchor := t.anchor }
  else
    { core := attendBoundary t (biasToken n)
      velocity := Nat.max t.velocity n.gate
      anchor := t.anchor }

/-- Numeric forward pass used for executable scoring/smoke checks. -/
def forwardNumeric (n : NoneistNeuron) (t : AttentionToken) : Nat :=
  if t.velocity ≤ n.gate then t.core.birth + n.bias.birth else t.core.birth

theorem forwardSymbolic_birth_monotone (n : NoneistNeuron) (t : AttentionToken) :
    t.core.birth ≤ (forwardSymbolic n t).core.birth := by
  by_cases h : t.velocity ≤ n.gate
  · simp [forwardSymbolic, h, PreGame.build, PreGame.maxBirth]
    have hBase : t.core.birth ≤ Nat.max t.core.birth n.bias.birth := Nat.le_max_left _ _
    exact Nat.le_trans hBase (Nat.le_succ _)
  · simp [forwardSymbolic, h, attendBoundary, biasToken, PreGame.build, PreGame.maxBirth]
    have hBase : t.core.birth ≤ Nat.max t.core.birth n.bias.birth := Nat.le_max_left _ _
    exact Nat.le_trans hBase (Nat.le_succ _)

theorem forwardNumeric_ge_birth (n : NoneistNeuron) (t : AttentionToken) :
    t.core.birth ≤ forwardNumeric n t := by
  by_cases h : t.velocity ≤ n.gate
  · simp [forwardNumeric, h]
  · simp [forwardNumeric, h]

/-- Layer-level symbolic map. -/
def forwardLayer (n : NoneistNeuron) (xs : List AttentionToken) : List AttentionToken :=
  xs.map (forwardSymbolic n)

@[simp] theorem forwardLayer_length (n : NoneistNeuron) (xs : List AttentionToken) :
    (forwardLayer n xs).length = xs.length := by
  simp [forwardLayer]

/-- Fold a symbolic network over one input token. -/
def networkForward (net : List NoneistNeuron) (x : AttentionToken) : AttentionToken :=
  net.foldl (fun acc n => forwardSymbolic n acc) x

theorem networkForward_birth_monotone (net : List NoneistNeuron) (x : AttentionToken) :
    x.core.birth ≤ (networkForward net x).core.birth := by
  induction net generalizing x with
  | nil =>
      simp [networkForward]
  | cons n ns ih =>
      have hStep : x.core.birth ≤ (forwardSymbolic n x).core.birth :=
        forwardSymbolic_birth_monotone n x
      have hTail :
          (forwardSymbolic n x).core.birth ≤ (networkForward ns (forwardSymbolic n x)).core.birth :=
        ih (forwardSymbolic n x)
      exact Nat.le_trans hStep hTail

end

end Experimental
end Surreal
end Numbers
end HeytingLean
