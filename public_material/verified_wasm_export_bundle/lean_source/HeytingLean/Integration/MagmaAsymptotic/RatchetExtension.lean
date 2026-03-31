import HeytingLean.Renormalization.DimensionalRatchet
import HeytingLean.Magma.Hierarchy
import HeytingLean.AsymptoticSafety.ScaleSymmetry

namespace HeytingLean.Integration.MagmaAsymptotic

/-- Extended logic types with a magmatic level below LoF. -/
inductive LogicTypeExt
  | Magmatic
  | LoF
  | Heyting
  | OML
  | Boolean
  deriving Repr, DecidableEq

/-- Higher dimension means more expressive and less tractable. -/
def LogicTypeExt.dimension : LogicTypeExt → ℕ
  | .Magmatic => 4
  | .LoF => 3
  | .Heyting => 2
  | .OML => 1
  | .Boolean => 0

/-- One RG step coarsens the logic toward tractability. -/
def rgStepExt : LogicTypeExt → LogicTypeExt
  | .Magmatic => .LoF
  | .LoF => .Heyting
  | .Heyting => .OML
  | .OML => .Boolean
  | .Boolean => .Boolean

theorem rgExt_monotone (L : LogicTypeExt) :
    (rgStepExt L).dimension ≤ L.dimension := by
  cases L <;> simp [rgStepExt, LogicTypeExt.dimension]

theorem rgStepExt_boolean_fixed : rgStepExt .Boolean = .Boolean := rfl

theorem constructive_corresponds_heyting :
    HeytingLean.Renormalization.logicAtScale HeytingLean.AsymptoticSafety.uvScale = .constructive ∧
    LogicTypeExt.Heyting.dimension = 2 := by
  exact ⟨rfl, rfl⟩

end HeytingLean.Integration.MagmaAsymptotic
