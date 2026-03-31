import HeytingLean.Layouts.Flat.Basic

/-!
# CuTe layouts: flat composition (semantic)

This file provides a minimal, executable notion of *semantic* composition of flat layouts by
composing their `applyIndex` functions.

Note: this is not an algorithm for producing a new tractable flat layout from two inputs; for the
categorical (and nested) composition machinery, see the `Tuple`/`Nested` layers.
-/

namespace HeytingLean
namespace Layouts
namespace Flat

open Flat

namespace FlatLayout

/-- Semantic composition of layout functions: `Φ_{B ∘ A} := Φ_B ∘ Φ_A` on linear indices. -/
def composeIndex (A B : FlatLayout) (i : ℕ) : ℕ :=
  B.applyIndex (A.applyIndex i)

end FlatLayout

end Flat
end Layouts
end HeytingLean
