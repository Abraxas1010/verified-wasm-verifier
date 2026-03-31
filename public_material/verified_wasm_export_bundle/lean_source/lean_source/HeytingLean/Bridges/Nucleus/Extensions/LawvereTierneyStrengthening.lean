import HeytingLean.LoF.Bauer.ToposBridge
import HeytingLean.Topos.LTfromNucleus
import HeytingLean.Topos.SheafBridges

namespace HeytingLean
namespace Bridges
namespace Nucleus
namespace Extensions

open CategoryTheory

universe u v

/-- Nucleus-on-truth-values to local-operator bridge (Type-level carrier). -/
noncomputable def localOperatorOfTruthNucleus (J : _root_.Nucleus Prop) :
    HeytingLean.Topos.LocalOperator (Type u) :=
  HeytingLean.LoF.Bauer.localOperatorOfPropNucleus J

/-- Meet-preservation of the bridge above. -/
theorem localOperatorOfTruthNucleus_meetPreserving (J : _root_.Nucleus Prop) :
    HeytingLean.Topos.LocalOperator.MeetPreserving
      (localOperatorOfTruthNucleus J) := by
  simpa [localOperatorOfTruthNucleus] using
    (HeytingLean.LoF.Bauer.localOperatorOfPropNucleus_meetPreserving J)

section KitBridge

variable (C : Type u) [Category.{v} C]
  [CategoryTheory.Limits.HasPullbacks C] [CategoryTheory.HasClassifier C]

/-- LT kits package directly into local operators. -/
noncomputable def localOperatorOfKit
    (kit : HeytingLean.Topos.LTfromNucleus.LawvereTierneyKit (C := C)) :
    HeytingLean.Topos.LocalOperator C :=
  HeytingLean.Topos.LTfromNucleus.ofLawvereTierneyKit (C := C) kit

/-- Closedness in the operator from a kit is exactly a fixed-point statement. -/
@[simp] theorem localOperatorOfKit_isClosed_iff
    (kit : HeytingLean.Topos.LTfromNucleus.LawvereTierneyKit (C := C))
    {X : C} (S : Subobject X) :
    HeytingLean.Topos.LocalOperator.IsClosed (C := C)
      (localOperatorOfKit (C := C) kit) S
      ↔ HeytingLean.Topos.LTfromNucleus.reclassify (C := C) kit.j S = S := by
  simpa [localOperatorOfKit] using
    (HeytingLean.Topos.LTfromNucleus.ofLawvereTierneyKit_isClosed_iff (C := C) kit S)

/-- The identity LT kit induces identity closure on every subobject. -/
@[simp] theorem idKit_closure_id (X : C) (S : Subobject X) :
    (HeytingLean.Topos.LTfromNucleus.idLocalOperator (C := C)).cl X S = S := by
  exact HeytingLean.Topos.LTfromNucleus.idLocalOperator_cl (C := C) X S

end KitBridge

end Extensions
end Nucleus
end Bridges
end HeytingLean
