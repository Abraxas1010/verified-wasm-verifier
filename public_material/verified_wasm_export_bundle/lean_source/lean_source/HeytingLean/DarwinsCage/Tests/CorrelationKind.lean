import HeytingLean.DarwinsCage.Representation

/-!
# Correlation metric-kind helper lemmas (Phase 6 tests)

Smoke tests for the kind-tagged correlation layer.
-/

namespace HeytingLean
namespace DarwinsCage
namespace Tests

open DarwinsCage

theorem highCorrelationWith_of_highCorrelationWithKind {L : Type*} [CompleteLattice L]
    {rep : PhysicsRepresentation L} {h f : L} {kind : CorrelationKind}
    {bounds : CorrelationBounds} :
    highCorrelationWithKind rep h f kind bounds → highCorrelationWith rep h f bounds :=
  DarwinsCage.highCorrelationWith_of_highCorrelationWithKind

end Tests
end DarwinsCage
end HeytingLean

