import HeytingLean.Bridge.NoCoincidence.Basic.RandomCircuit

namespace HeytingLean.Bridge.NoCoincidence.Basic

/-- Polynomially bounded verifier schema for reversible circuits. -/
structure PolyVerifier where
  V : (n : ℕ) → RevCircuit n → String → Bool
  polyBound : ℕ → ℕ

/-- A circuit is accepted when some advice string of bounded length causes the verifier to return
`true`. This is the formal acceptance relation used in the CNCC statement. -/
def AdviceAccepts (pv : PolyVerifier) (n : ℕ) (C : RevCircuit n) : Prop :=
  ∃ π : String, π.length ≤ pv.polyBound C.size ∧ pv.V n C π = true

/-- Soundness slack is represented as a finite exceptional family of circuits.
This captures Neyman's "< 100%" verifier target without forcing a probability model on the Lean
statement at phase 1. -/
def SoundnessSlack (pv : PolyVerifier) (n : ℕ) : Prop :=
  ∃ bad : Set (RevCircuit n), bad.Finite ∧
    ∀ C : RevCircuit n, AdviceAccepts pv n C ∧ ¬ PropertyP n C → C ∈ bad

/-- The computational no-coincidence conjecture: every genuinely non-coincidental circuit admits
short advice, while false positives are confined to a finite exceptional family. -/
def CNCC : Prop :=
  ∃ pv : PolyVerifier,
    (∀ (n : ℕ) (C : RevCircuit n), PropertyP n C → AdviceAccepts pv n C) ∧
    (∀ n : ℕ, SoundnessSlack pv n)

end HeytingLean.Bridge.NoCoincidence.Basic
