import HeytingLean.EpistemicCalculus.Examples.BipolarPossibility

namespace HeytingLean.EpistemicCalculus.Examples

/--
`IP`: interval probabilities with empty intersections allowed.
This corrected model is definitionally the same carrier/operations as `PTbi`.
-/
abbrev IP := PTbi

def ptbiIsoIp : OrderIso PTbi IP where
  toFun := id
  invFun := id
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  map_rel_iff' := by intro a b; rfl

end HeytingLean.EpistemicCalculus.Examples
