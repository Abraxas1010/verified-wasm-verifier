import HeytingLean.PerspectivalPlenum.StrictRatchet

namespace HeytingLean
namespace Tests
namespace PerspectivalPlenum

open HeytingLean.PerspectivalPlenum
open HeytingLean.PerspectivalPlenum.StrictRatchet

universe u

variable {α : Type u} [Order.Frame α]
variable (J : Nucleus α) (S : RatchetStep α) (steps : List (RatchetStep α))

#check StrictLevel
#check StrictStage
#check StrictStage.base
#check StrictStage.plenum
#check StrictStage.strictlyPrecedes
#check separationWitness
#check ConservativeTranslation
#check ConsequenceConservativeTranslation
#check Contracts.soundnessCoverage
#check Contracts.conservativityCoverage
#check GateG1
#check GateG2
#check GateG3
#check strictnessLedger

example :
    StrictStage.strictlyPrecedes (StrictStage.base J) (StrictStage.plenum steps J) := by
  exact StrictStage.base_strictly_precedes_plenum (steps := steps) (J := J)

example :
    separationWitness StrictLevel.L2 ∧ ¬ separationWitness StrictLevel.L1 := by
  exact explicit_strict_separation

example : GateG1 := by
  exact GateG1_complete

example : GateG2 := by
  exact GateG2_complete

example : GateG3 := by
  exact GateG3_complete

example : AllGatesClosed := by
  exact allGatesClosed_complete

section DoubleNegationConservativity

variable (β : Type u) [HeytingAlgebra β]
variable (φ : ConservativeTranslation.DoubleNegationLane.Core β)

example :
    (ConservativeTranslation.DoubleNegationLane.translation β).ProvableSrc φ
      ↔
    (ConservativeTranslation.DoubleNegationLane.translation β).ProvableTgt
      ((ConservativeTranslation.DoubleNegationLane.translation β).translate φ) := by
  simpa using
    (ConservativeTranslation.DoubleNegationLane.conservativity_exact (α := β) φ)

end DoubleNegationConservativity

section DoubleNegationConsequenceConservativity

variable (β : Type u) [HeytingAlgebra β]
variable (Γ : List (ConservativeTranslation.DoubleNegationLane.Core β))
variable (φ : ConservativeTranslation.DoubleNegationLane.Core β)

example :
    (ConsequenceConservativeTranslation.DoubleNegationLane.translationCtx β).DerivesSrc Γ φ
      ↔
    (ConsequenceConservativeTranslation.DoubleNegationLane.translationCtx β).DerivesTgt
      (Γ.map (ConsequenceConservativeTranslation.DoubleNegationLane.translationCtx β).translate)
      ((ConsequenceConservativeTranslation.DoubleNegationLane.translationCtx β).translate φ) := by
  simpa using
    (ConsequenceConservativeTranslation.DoubleNegationLane.conservativityCtx_exact
      (α := β) Γ φ)

example :
    (ConservativeTranslation.DoubleNegationLane.translation β).ProvableSrc φ
      ↔
    (ConsequenceConservativeTranslation.DoubleNegationLane.translationCtx β).DerivesSrc [] φ := by
  simpa using
    (ConsequenceConservativeTranslation.DoubleNegationLane.formula_level_as_empty_context
      (α := β) φ)

end DoubleNegationConsequenceConservativity

end PerspectivalPlenum
end Tests
end HeytingLean
