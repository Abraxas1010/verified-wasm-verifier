import HeytingLean.Bridge.YWitness.ClassicalConstructive

namespace HeytingLean.Tests.YWitness

open HeytingLean.Bridge.YWitness

example (a : Bool) :
    isDiscrete ((HeytingLean.LoF.Bauer.toClassicalCore Bool a :
      HeytingLean.LoF.Bauer.ClassicalCore Bool) : Bool) := by
  exact regularized_value_is_discrete (α := Bool) a

example (a : Bool) :
    isDiscrete (HeytingLean.LoF.Bauer.doubleNegNucleus Bool a) := by
  exact bounded_classical_constructive_bridge_on_dn_core (α := Bool) a

example (a : Bool) :
    Function.IsFixedPt (HeytingLean.LoF.Bauer.doubleNegNucleus Bool)
      (HeytingLean.LoF.Bauer.doubleNegNucleus Bool a) := by
  exact y_fixed_point_shape_on_dn_core (α := Bool) a

example (a : Bool) :
    HeytingLean.LoF.Bauer.doubleNegNucleus Bool
      ((defaultDNBridgeData Bool).regularize a : Bool) =
        ((defaultDNBridgeData Bool).regularize a : Bool) := by
  exact (defaultDNBridgeData Bool).fixed_on_image a

end HeytingLean.Tests.YWitness
