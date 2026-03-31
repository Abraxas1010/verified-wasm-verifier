import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum

namespace HeytingLean
namespace Metrics
namespace Magnitude

/-- Finite-set magnitude model: cardinality. -/
def finiteMagnitude (α : Type*) [Fintype α] : Nat := Fintype.card α

theorem finiteMagnitude_punit :
    finiteMagnitude PUnit = 1 := by
  simp [finiteMagnitude]

theorem finiteMagnitude_empty :
    finiteMagnitude PEmpty = 0 := by
  simp [finiteMagnitude]

theorem finiteMagnitude_sum (α β : Type*) [Fintype α] [Fintype β] :
    finiteMagnitude (α ⊕ β) = finiteMagnitude α + finiteMagnitude β := by
  simp [finiteMagnitude]

theorem finiteMagnitude_le_of_embedding {α β : Type*} [Fintype α] [Fintype β]
    (f : α ↪ β) :
    finiteMagnitude α ≤ finiteMagnitude β := by
  simpa [finiteMagnitude] using Fintype.card_le_of_injective f f.injective

end Magnitude
end Metrics
end HeytingLean
