import HeytingLean.Embeddings.CrossLensTransport

/-!
# QuantumActiveInference.SheafGluing

Executable-friendly sheaf-gluing scaffolding over lens-indexed transports.

The intent is:
- each lens has its own “local section” type,
- transports project local data into a shared comparison space (“Plato”),
- gluing holds when the projected invariants agree (or are close).
-/

namespace HeytingLean
namespace QuantumActiveInference

open HeytingLean.Embeddings

/-- A gluing condition: two local sections agree after projection to the shared Platonic space. -/
def GluingCondition {Carrier : LensID → Type} {Plato : Type}
    (T : CrossLensTransport Carrier Plato)
    (l1 l2 : LensID) (x : Carrier l1) (y : Carrier l2) : Prop :=
  T.toPlato l1 x = T.toPlato l2 y

/-- Glue two local sections by choosing their common Platonic value (when gluable). -/
noncomputable def glue {Carrier : LensID → Type} {Plato : Type}
    (T : CrossLensTransport Carrier Plato)
    (l1 l2 : LensID) (x : Carrier l1) (y : Carrier l2)
    (_h : GluingCondition T l1 l2 x y) : Plato :=
  T.toPlato l1 x

theorem glue_spec {Carrier : LensID → Type} {Plato : Type}
    (T : CrossLensTransport Carrier Plato)
    (l1 l2 : LensID) (x : Carrier l1) (y : Carrier l2)
    (h : GluingCondition T l1 l2 x y) :
    glue T l1 l2 x y h = T.toPlato l2 y := by
  simpa [glue, GluingCondition] using h

end QuantumActiveInference
end HeytingLean
