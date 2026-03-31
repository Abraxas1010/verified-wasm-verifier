import HeytingLean.Noneism.Witness

/-!
# Noneism.Intentionality

Lightweight intentional-state scaffolding.

This file is a minimal bridge layer so that other parts of the repo can refer to “an intentional
state” (a claim about an object) without choosing a specific noneist semantics.
-/

namespace HeytingLean
namespace Noneism

/-- An intentional state: a witnessed formula plus an (optional) label. -/
structure IntentionalState (σ : Type) where
  claim : WitnessedFormula σ
  label : String := ""

/-- The object (term) the intentional state is “about”. -/
def IntentionalState.object {σ : Type} (st : IntentionalState σ) : Term :=
  st.claim.term

/-- The associated witness-necessity formula. -/
def IntentionalState.requiresExistence {σ : Type} (st : IntentionalState σ) : Formula σ :=
  witnessNecessity st.claim

end Noneism
end HeytingLean

