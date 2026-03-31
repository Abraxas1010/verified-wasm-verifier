/-!
# QuantumActiveInference.TQFT

Tiny TQFT/control-flow hooks.

This is a placeholder interface sufficient for downstream modules to *mention* a TQFT-shaped
control flow without importing heavy category theory.
-/

namespace HeytingLean
namespace QuantumActiveInference

/-- A minimal TQFT-like record: objects, morphisms, and a (placeholder) composition law. -/
structure TQFT where
  Obj : Type
  Hom : Obj → Obj → Type
  id : (X : Obj) → Hom X X
  comp : {X Y Z : Obj} → Hom Y Z → Hom X Y → Hom X Z
  assoc : Prop := True

end QuantumActiveInference
end HeytingLean

