import HeytingLean.Quantum.Contextuality

/-!
# Contextuality tests: witness layer (Phase 12)

Compile-time checks for the Phase 9 contextuality adapter layer.
-/

namespace HeytingLean.Tests.Contextuality.WitnessTests

open HeytingLean.Quantum.Contextuality

#check Triangle.witness
#check CryptoLink.triangle_no_constructor_globalSectionTask

end HeytingLean.Tests.Contextuality.WitnessTests

