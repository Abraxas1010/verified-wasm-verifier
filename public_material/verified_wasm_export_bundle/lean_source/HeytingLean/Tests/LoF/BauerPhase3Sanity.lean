import HeytingLean.LoF.Bauer

namespace HeytingLean
namespace Tests
namespace LoF

open CategoryTheory
open HeytingLean.LoF.Bauer

namespace BauerPhase3

universe u

noncomputable def JProp : Nucleus Prop :=
  HeytingLean.LoF.Bauer.doubleNegNucleus Prop

noncomputable def JType : HeytingLean.Topos.LocalOperator (Type u) :=
  HeytingLean.LoF.Bauer.localOperatorOfPropNucleus JProp

example {X : Type u} (S : Subobject X) :
    ToposBridge.asSet (ToposBridge.closeSubobject (X := X) JProp S)
      = {x : X | JProp (x ∈ ToposBridge.asSet S)} := by
  simp [ToposBridge.closeSet]

example {X Y : Type u} (f : Y ⟶ X) (S : Subobject X) :
    (Subobject.pullback f).obj (JType.cl X S)
      = JType.cl Y ((Subobject.pullback f).obj S) := by
  simpa using (JType.pullback_stable f S)

end BauerPhase3

end LoF
end Tests
end HeytingLean
