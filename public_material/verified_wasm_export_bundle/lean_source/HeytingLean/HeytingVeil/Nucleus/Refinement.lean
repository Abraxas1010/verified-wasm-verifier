import HeytingLean.Topos.LTfromNucleus

namespace HeytingLean.HeytingVeil.Nucleus

open CategoryTheory
open HeytingLean.Topos
open HeytingLean.Topos.LTfromNucleus

universe u v

variable (C : Type u) [Category.{v} C]
variable [CategoryTheory.Limits.HasPullbacks C]
variable [CategoryTheory.HasClassifier C]

/--
Refinement preorder induced by `j`-reclassification:
`S` refines `T` when `j(S) ≤ j(T)` in the subobject lattice.
-/
def Refines (kit : LawvereTierneyKit (C := C)) {X : C}
    (S T : Subobject X) : Prop :=
  reclassify (C := C) kit.j S ≤ reclassify (C := C) kit.j T

theorem refines_refl (kit : LawvereTierneyKit (C := C)) {X : C}
    (S : Subobject X) :
    Refines (C := C) kit S S := by
  exact le_rfl

theorem refines_trans (kit : LawvereTierneyKit (C := C)) {X : C}
    {S T U : Subobject X}
    (hST : Refines (C := C) kit S T)
    (hTU : Refines (C := C) kit T U) :
    Refines (C := C) kit S U := by
  exact le_trans hST hTU

/-- Monotone map into the refinement preorder from ordinary subobject inclusion. -/
theorem refines_of_le (kit : LawvereTierneyKit (C := C)) {X : C}
    {S T : Subobject X} (hST : S ≤ T) :
    Refines (C := C) kit S T := by
  exact reclassify_le_of_le (C := C) kit hST

/-- Closed subobjects for `ofLawvereTierneyKit` are exactly `j`-fixed points. -/
theorem fixedPoint_iff_isClosed (kit : LawvereTierneyKit (C := C)) {X : C}
    (S : Subobject X) :
    reclassify (C := C) kit.j S = S
      ↔ Topos.LocalOperator.IsClosed
          (C := C) (ofLawvereTierneyKit (C := C) kit) S := by
  simpa [Iff.comm] using
    (ofLawvereTierneyKit_isClosed_iff (C := C) kit S)

/-- `j`-fixed points are stable under pullback along any map. -/
theorem fixedPoint_pullback (kit : LawvereTierneyKit (C := C))
    {X Y : C} (f : Y ⟶ X) (S : Subobject X)
    (hfix : reclassify (C := C) kit.j S = S) :
    reclassify (C := C) kit.j ((Subobject.pullback f).obj S)
      = (Subobject.pullback f).obj S := by
  have hclosed : Topos.LocalOperator.IsClosed
      (C := C) (ofLawvereTierneyKit (C := C) kit) S :=
    (fixedPoint_iff_isClosed (C := C) kit S).mp hfix
  have hclosedPb : Topos.LocalOperator.IsClosed
      (C := C) (ofLawvereTierneyKit (C := C) kit) ((Subobject.pullback f).obj S) :=
    Topos.LocalOperator.isClosed_pullback
      (J := ofLawvereTierneyKit (C := C) kit) (f := f) (S := S) hclosed
  exact (fixedPoint_iff_isClosed (C := C) kit ((Subobject.pullback f).obj S)).mpr hclosedPb

end HeytingLean.HeytingVeil.Nucleus
