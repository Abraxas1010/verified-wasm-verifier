import HeytingLean.EpistemicCalculus.ChangeOfCalculi.Conservative
import HeytingLean.EpistemicCalculus.ChangeOfCalculi.Liberal

namespace HeytingLean.EpistemicCalculus.ChangeOfCalculi

/-- Balanced change: strict monoidal and monotone. -/
structure BalancedChange (V W : Type*)
    [EpistemicCalculus V] [EpistemicCalculus W] where
  map : V → W
  monotone : ∀ {x y : V}, x ≤ y → map x ≤ map y
  strict_monoidal : ∀ x y : V, map (x fus y) = map x fus map y
  strict_unit : map EpistemicCalculus.unit = EpistemicCalculus.unit

def BalancedChange.toConservative {V W : Type*}
    [EpistemicCalculus V] [EpistemicCalculus W]
    (F : BalancedChange V W) : ConservativeChange V W where
  map := F.map
  monotone := F.monotone
  lax_monoidal := by
    intro x y
    simp [F.strict_monoidal x y]
  lax_unit := by
    simp [F.strict_unit]

def BalancedChange.toLiberal {V W : Type*}
    [EpistemicCalculus V] [EpistemicCalculus W]
    (F : BalancedChange V W) : LiberalChange V W where
  map := F.map
  monotone := F.monotone
  oplax_monoidal := by
    intro x y
    simp [F.strict_monoidal x y]
  oplax_unit := by
    simp [F.strict_unit]

end HeytingLean.EpistemicCalculus.ChangeOfCalculi
