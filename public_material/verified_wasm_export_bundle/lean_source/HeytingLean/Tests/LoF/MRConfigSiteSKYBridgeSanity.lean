import Mathlib.Tactic
import HeytingLean.LoF.MRSystems.ConfigSiteSKYBridge

/-!
Sanity checks for `LoF/MRSystems/ConfigSiteSKYBridge.lean`.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF.Comb
open HeytingLean.LoF.MRSystems

namespace MRConfigSiteSKYBridgeSanity

open BoolConfig

def R : Bool → Bool → Bool := fun _ a => a

def c₁ : BoolConfig.Config R := { state := false, word := [true, false] }

def c₂ : BoolConfig.Config R := { state := true, word := [false] }

theorem hReach : BoolConfig.Config.Reachable (R := R) c₁ c₂ := by
  refine ⟨[true], ?_, ?_⟩
  · simp [c₁, c₂]
  · simp [c₂, BoolConfig.run, R]

example : Steps (BoolConfig.toSKYTerm R c₁) (BoolConfig.toSKYTerm R c₂) := by
  exact BoolConfig.steps_toSKYTerm_of_reachable (R := R) (c₁ := c₁) (c₂ := c₂) hReach

end MRConfigSiteSKYBridgeSanity

end LoF
end Tests
end HeytingLean
