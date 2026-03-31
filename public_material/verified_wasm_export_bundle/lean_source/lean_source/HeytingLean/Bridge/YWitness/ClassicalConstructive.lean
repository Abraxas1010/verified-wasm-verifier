import HeytingLean.Bridge.YWitness.BooleanCore

namespace HeytingLean.Bridge.YWitness

open HeytingLean.LoF.Bauer

/-- Concrete data for the bounded bridge from a Heyting algebra into its double-negation core. -/
structure DNBridgeData (α : Type _) [HeytingAlgebra α] where
  regularize : α -> ClassicalCore α
  fixed_on_image :
    forall a, doubleNegNucleus α ((regularize a : ClassicalCore α) : α) =
      (regularize a : ClassicalCore α)

/-- The canonical bridge data uses the standard regularization map. -/
def defaultDNBridgeData (α : Type _) [HeytingAlgebra α] : DNBridgeData α where
  regularize := toClassicalCore α
  fixed_on_image := by
    intro a
    exact ((toClassicalCore α a).property :
      doubleNegNucleus α ((toClassicalCore α a : ClassicalCore α) : α) =
        ((toClassicalCore α a : ClassicalCore α) : α))

theorem bounded_classical_constructive_bridge_on_dn_core {α : Type _} [HeytingAlgebra α]
    (a : α) :
    isDiscrete (doubleNegNucleus α a) := by
  apply (discrete_iff_dn_fixed (α := α) (a := doubleNegNucleus α a)).2
  exact Nucleus.idempotent (n := doubleNegNucleus α) (x := a)

theorem y_fixed_point_shape_on_dn_core {α : Type _} [HeytingAlgebra α] (a : α) :
    Function.IsFixedPt (doubleNegNucleus α) (doubleNegNucleus α a) := by
  exact Nucleus.idempotent (n := doubleNegNucleus α) (x := a)

end HeytingLean.Bridge.YWitness
