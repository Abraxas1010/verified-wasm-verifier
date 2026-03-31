import HeytingLean.LoF.Bauer

namespace HeytingLean
namespace Tests
namespace LoF

open CategoryTheory
open HeytingLean.LoF.Bauer

namespace BauerPhase4

universe u

noncomputable def JProp : Nucleus Prop :=
  HeytingLean.LoF.Bauer.doubleNegNucleus Prop

noncomputable def JType : HeytingLean.Topos.LocalOperator (Type u) :=
  HeytingLean.LoF.Bauer.localOperatorOfPropNucleus JProp

example : HeytingLean.Topos.LocalOperator.MeetPreserving JType :=
  HeytingLean.LoF.Bauer.localOperatorOfPropNucleus_meetPreserving JProp

example {X : Type u} (S T : Subobject X) :
    JType.cl X (S ⊓ T) = JType.cl X S ⊓ JType.cl X T := by
  simpa using (HeytingLean.LoF.Bauer.localOperatorOfPropNucleus_meetPreserving JProp).map_inf S T

open HeytingLean.LoF.Bauer.SyntheticComputability

example : Nonempty (Toy.ΩJ ≃ Bool) :=
  ⟨Toy.equivBool⟩

example (p : Toy.ΩJ) : p = Toy.Ω0 ∨ p = Toy.Ωtop :=
  Toy.eq_Ω0_or_eq_Ωtop p

end BauerPhase4

end LoF
end Tests
end HeytingLean
