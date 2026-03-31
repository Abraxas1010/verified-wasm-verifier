import HeytingLean.ActiveInference.FreeEnergy
import HeytingLean.Noneism.Intentionality

/-!
# Noneism.GenerativeModel

Bridge scaffolding between noneist intentional states (“witness talk”) and the repo’s
active-inference objective.

This is interface-first: it packages the objects so downstream code can refer to a “generative
witness model” without committing to a particular noneist semantics.
-/

namespace HeytingLean
namespace Noneism

open HeytingLean.ActiveInference

/-- A generative model whose hidden states carry a (noneist) intentional witness description. -/
structure GenerativeWitnessModel (σ : Type) (O S : Type*) where
  gen : GenerativeModel O S
  recModel : RecognitionModel O S
  witness : S → IntentionalState σ

/-- Free energy for an observation (delegated to the base `ActiveInference` definition). -/
noncomputable def freeEnergyAt {σ : Type} {O S : Type*} [Fintype S]
    (M : GenerativeWitnessModel σ O S) (o : O) : ℝ :=
  HeytingLean.ActiveInference.freeEnergy M.gen M.recModel o

end Noneism
end HeytingLean
