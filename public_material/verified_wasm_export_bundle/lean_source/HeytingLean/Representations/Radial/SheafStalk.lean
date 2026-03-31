import HeytingLean.Representations.Radial.Core
import Mathlib.Data.Finset.Basic

/-!
# Sheaf stalks as radial paths (scaffold)

This module provides a minimal “stalk” API over a radial graph:
- a stalk is represented by its current tip state;
- `grow` moves one ring outward when possible.

The eventual goal is to connect stalk growth/collapse to sheaf gluing and diffusion.
-/

namespace HeytingLean
namespace Representations
namespace Radial
namespace SheafStalk

open HeytingLean.Representations.Radial

noncomputable section

/-- A stalk is represented by its current tip state (scaffold). -/
structure Stalk (G : RadialGraph) where
  tip : G.StateIdx

namespace Stalk

def height {G : RadialGraph} (stalk : Stalk G) : Nat :=
  G.assemblyIndex stalk.tip

/-- Grow one ring outward, if a successor ring exists and contains a state. -/
def grow {G : RadialGraph} (stalk : Stalk G) : Option (Stalk G) :=
  match G.ringSucc? (G.ringOf stalk.tip) with
  | none => none
  | some r' =>
      match G.stateInRing? r' with
      | none => none
      | some s' => some ⟨s'.1⟩

theorem grow_height {G : RadialGraph} (stalk stalk' : Stalk G)
    (h : stalk.grow = some stalk') :
    stalk'.height = stalk.height + 1 := by
  classical
  unfold grow at h
  cases hSucc : G.ringSucc? (G.ringOf stalk.tip) <;> simp [hSucc] at h
  case some r' =>
    cases hPick : G.stateInRing? r' <;> simp [hPick] at h
    case some s' =>
      -- `stalk'` is the chosen successor tip.
      cases h
      have hs : G.ringOf s'.1 = r' := s'.2
      -- `r'` is the successor ring of the original tip.
      have hr' : r'.val = (G.ringOf stalk.tip).val + 1 := by
        unfold RadialGraph.ringSucc? at hSucc
        by_cases hlt : (G.ringOf stalk.tip).val + 1 < G.ringCount
        · have : (⟨(G.ringOf stalk.tip).val + 1, hlt⟩ : G.RingIdx) = r' :=
            Option.some.inj (by simpa [hlt] using hSucc)
          simpa using (congrArg Fin.val this).symm
        · have : False := by
            have hSucc' := hSucc
            simp [hlt] at hSucc'
          cases this
      -- rewrite heights in terms of ring numbers
      simp [Stalk.height, RadialGraph.assemblyIndex, hs, hr']

end Stalk

/-- A section assigning a value to each state (placeholder for later sheaf structure). -/
structure SheafSection (G : RadialGraph) (R : Type*) where
  value : G.StateIdx → R

def SheafSection.isHarmonic {G : RadialGraph} {R : Type*} [Zero R]
    (_sec : SheafSection G R) (_M : RadialMatrix G R) : Prop :=
  True

end

end SheafStalk
end Radial
end Representations
end HeytingLean
