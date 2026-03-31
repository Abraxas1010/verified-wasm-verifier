import HeytingLean.Layouts.Nested.NestCategory

/-!
# Nest operations: logical division and product

Thin wrapper module re-exporting the executable operations already implemented in
`HeytingLean.Layouts.Nested.NestCategory`.
-/

namespace HeytingLean
namespace Layouts
namespace Nested

namespace NestMorphism

/-- Alias for `NestMorphism.logicalDivide?` (paper notation: `f ⊘ g`). -/
abbrev divide? := logicalDivide?

/-- Alias for `NestMorphism.logicalProduct?` (paper notation: `f ⊗ g`). -/
abbrev product? := logicalProduct?

end NestMorphism

end Nested
end Layouts
end HeytingLean
