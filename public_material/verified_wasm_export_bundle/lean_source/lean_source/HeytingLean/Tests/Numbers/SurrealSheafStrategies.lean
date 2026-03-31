import HeytingLean.Numbers.Surreal.SheafStrategies

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Numbers.Surreal
open HeytingLean.Numbers.Surreal.SheafStrategies

private def bPlus : Branch := [Sign.plus]
private def bMinus : Branch := [Sign.minus]

private def U : Set Branch := cylinder bPlus
private def V : Set Branch := cylinder bMinus

example : IsOpen U := by
  simpa [U] using isOpen_cylinder bPlus

example : IsOpen V := by
  simpa [V] using isOpen_cylinder bMinus

private def sU : LocalSection U := fun _ _ => StrategyOrder.zero
private def sV : LocalSection V := fun _ _ => StrategyOrder.zero

private theorem sUv_compatible : Compatible sU sV := by
  intro p hpU hpV
  rfl

example :
    ∃ g : LocalSection (U ∪ V),
      (∀ p (hpU : p ∈ U), g p (Or.inl hpU) = sU p hpU) ∧
      (∀ p (hpV : p ∈ V), g p (Or.inr hpV) = sV p hpV) := by
  exact exists_glue sU sV sUv_compatible

example {p : Branch} (hp : p ∈ U ∪ V) :
    glue (sumSection sU sU) (sumSection sV sV)
      (compatible_sum sUv_compatible sUv_compatible) p hp =
    StrategyOrder.sum
      (glue sU sV sUv_compatible p hp)
      (glue sU sV sUv_compatible p hp) := by
  simpa using glue_sum sU sU sV sV sUv_compatible sUv_compatible (hp := hp)

end Numbers
end Tests
end HeytingLean
