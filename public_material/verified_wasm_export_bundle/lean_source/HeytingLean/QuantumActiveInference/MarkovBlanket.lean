import HeytingLean.Embeddings.HolographicScreen

/-!
# QuantumActiveInference.MarkovBlanket

Interface-first scaffolding for (holographic) Markov blankets.

The unified-system spec uses “Markov blanket” language to describe the boundary that mediates
interaction between internal (“witness/belief”) and external (“world”) state. Here we record the
core data needed downstream (ATP + sheaf gluing), without committing to a probability or quantum
semantics yet.
-/

namespace HeytingLean
namespace QuantumActiveInference

/-- A minimal Markov blanket interface. -/
structure MarkovBlanket where
  Internal : Type
  External : Type
  Sensory : Type
  Active : Type
  perceive : External → Sensory
  /-- Internal dynamics that (should) factor through sensory state. -/
  internalUpdate : Internal → Sensory → Internal
  /-- Raw internal dynamics used for falsifiability checks. -/
  rawInternalUpdate : Internal → External → Internal
  /-- Action selection from internal state. -/
  emit : Internal → Active
  /-- External dynamics mediated by chosen action. -/
  externalEffect : Active → External → External
  /-- Raw external dynamics used for screening checks. -/
  rawExternalEffect : Internal → External → External

/-- A holographic Markov blanket: an internal state can be encoded on a screen, and decoded to an external state. -/
structure HolographicMarkovBlanket where
  Internal : Type
  External : Type
  Sensory : Type
  Active : Type
  Screen : Type
  encode : Internal → Screen
  decode : Screen → External
  perceive : External → Sensory
  internalUpdate : Internal → Sensory → Internal
  rawInternalUpdate : Internal → External → Internal
  emit : Internal → Active
  externalEffect : Active → External → External
  rawExternalEffect : Internal → External → External

namespace MarkovBlanket

/-- Functional Markov property: raw internal dynamics must factor through
the sensory channel. -/
def FunctionalMarkovProperty (B : MarkovBlanket) : Prop :=
  ∀ i : B.Internal, ∀ e : B.External,
    B.rawInternalUpdate i e = B.internalUpdate i (B.perceive e)

/-- Active screening: raw external impact must factor through active channel. -/
def ActiveScreening (B : MarkovBlanket) : Prop :=
  ∀ i : B.Internal, ∀ e : B.External,
    B.rawExternalEffect i e = B.externalEffect (B.emit i) e

/-- Conditional-independence proxy used by this lightweight interface. -/
def conditionalIndependence (B : MarkovBlanket) : Prop :=
  FunctionalMarkovProperty B ∧ ActiveScreening B

/-- Generic constructor lemma: if an interface factors as declared, the
functional Markov property holds. -/
theorem functionalMarkov_of_perceive_determines (B : MarkovBlanket)
    (h :
      ∀ i : B.Internal, ∀ e : B.External,
        B.rawInternalUpdate i e = B.internalUpdate i (B.perceive e)) :
    FunctionalMarkovProperty B := by
  exact h

/-- A concrete blanket with non-trivial update/effect rules. -/
def ExampleBlanket : MarkovBlanket :=
  { Internal := Nat
    , External := Bool
    , Sensory := Bool
    , Active := Bool
    , perceive := fun e => e
    , internalUpdate := fun i s => if s then i + 1 else i
    , rawInternalUpdate := fun i e => if e then i + 1 else i
    , emit := fun i => i % 2 = 0
    , externalEffect := fun a e => decide (a ≠ e)
    , rawExternalEffect := fun i e => decide ((i % 2 = 0) ≠ e) }

theorem exampleBlanket_functional :
    FunctionalMarkovProperty ExampleBlanket := by
  intro i e
  cases e <;> simp [ExampleBlanket]

theorem exampleBlanket_active :
    ActiveScreening ExampleBlanket := by
  intro i e
  cases e <;> simp [ExampleBlanket]

theorem exampleBlanket_conditionalIndependence :
    conditionalIndependence ExampleBlanket := by
  exact ⟨exampleBlanket_functional, exampleBlanket_active⟩

/-- A leaky blanket: `perceive` discards external information, but
`rawInternalUpdate` still reads external state directly. -/
def LeakyBlanket : MarkovBlanket :=
  { Internal := Bool
    , External := Bool
    , Sensory := Unit
    , Active := Unit
    , perceive := fun _ => ()
    , internalUpdate := fun i _ => i
    , rawInternalUpdate := fun _ e => e
    , emit := fun _ => ()
    , externalEffect := fun _ e => e
    , rawExternalEffect := fun _ e => e }

theorem leakyBlanket_not_functional :
    ¬ FunctionalMarkovProperty LeakyBlanket := by
  intro h
  have h0 := h false true
  simp [LeakyBlanket] at h0

theorem leakyBlanket_not_conditionalIndependence :
    ¬ conditionalIndependence LeakyBlanket := by
  intro h
  exact leakyBlanket_not_functional h.1

end MarkovBlanket

namespace HolographicMarkovBlanket

/-- Functional Markov property for holographic blankets. -/
def FunctionalMarkovProperty (B : HolographicMarkovBlanket) : Prop :=
  ∀ i : B.Internal, ∀ e : B.External,
    B.rawInternalUpdate i e = B.internalUpdate i (B.perceive e)

/-- Active screening for holographic blankets. -/
def ActiveScreening (B : HolographicMarkovBlanket) : Prop :=
  ∀ i : B.Internal, ∀ e : B.External,
    B.rawExternalEffect i e = B.externalEffect (B.emit i) e

/-- Conditional-independence contract (no probabilistic machinery required). -/
def conditionalIndependence (B : HolographicMarkovBlanket) : Prop :=
  FunctionalMarkovProperty B ∧ ActiveScreening B

theorem conditionalIndependence_trivial (B : HolographicMarkovBlanket) :
    (FunctionalMarkovProperty B) →
    (ActiveScreening B) →
    B.conditionalIndependence := by
  intro hF hA
  exact ⟨hF, hA⟩

end HolographicMarkovBlanket

end QuantumActiveInference
end HeytingLean
