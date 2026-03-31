import HeytingLean.VETT.Rel.Basic
import HeytingLean.VETT.Rel.Theorems
import HeytingLean.VETT.Rel.IteratedVirtualModel

/-!
# Tests.VETT.Sanity

Compile-time sanity checks for the Phase-10 VETT strict relation model.
-/

namespace HeytingLean.Tests.VETT.Sanity

open HeytingLean.VETT.Rel
open HeytingLean.VETT.Rel.RelOps

example {A B C : Type} (P : HeytingLean.VETT.Rel.HRel A B) (Q : HeytingLean.VETT.Rel.HRel B C) (f : A → A) (g : C → C) :
    RelOps.restrict (RelOps.tensor P Q) f g =
      RelOps.tensor (RelOps.restrict P f (fun x => x)) (RelOps.restrict Q (fun x => x) g) :=
  rfl

example {C : Type} (P : C → Prop) (x : C) :
    (∀ y, y = x → P y) ↔ P x :=
  yoneda_tautology P x

end HeytingLean.Tests.VETT.Sanity
