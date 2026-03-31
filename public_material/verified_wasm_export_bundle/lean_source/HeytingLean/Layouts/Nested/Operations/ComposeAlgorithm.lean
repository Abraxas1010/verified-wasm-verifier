import HeytingLean.Layouts.Nested.PullbackPushforward

/-!
# Nest operations: composition algorithm (weak composite)

Thin wrapper module re-exporting the executable “weak composite” construction (`weakComposite?`),
which follows the mutual refinement → pullback/pushforward pipeline from the companion reference.
-/

namespace HeytingLean
namespace Layouts
namespace Nested

namespace NestMorphism

/-- Alias for `NestMorphism.weakComposite?` (Algorithm 4.1.2 core pipeline). -/
abbrev composeAlgorithm? := weakComposite?

end NestMorphism

end Nested
end Layouts
end HeytingLean
