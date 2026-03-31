import HeytingLean.Representations.Radial
import Mathlib.Tactic

/-!
# Radial representations sanity checks
-/

namespace HeytingLean
namespace Tests
namespace Representations

open HeytingLean.Representations.Radial
open HeytingLean.Representations.Radial.Distance

def G : RadialGraph :=
  { ringSizes := [2, 1]
    ring0_nonempty := by decide }

def s0 : G.StateIdx := ⟨0, by decide⟩
def s1 : G.StateIdx := ⟨1, by decide⟩
def s2 : G.StateIdx := ⟨2, by decide⟩

example : G.assemblyIndex s0 = 0 := by rfl
example : G.assemblyIndex s1 = 0 := by rfl
example : G.assemblyIndex s2 = 1 := by rfl

example : Distance.distanceFromR G s2 = 1 := by
  simpa [Distance.distanceFromR_eq_assembly] using (show G.assemblyIndex s2 = 1 from rfl)

end Representations
end Tests
end HeytingLean
