import HeytingLean.Quantum.QState

namespace HeytingLean.Quantum

/-!
This module is reserved for a future bridge to the external `QuantumInfo` library.

At the moment, upstream `Timeroot/Lean-QuantumInfo` still contains incomplete proof placeholders
that trigger warnings and therefore fail our strict `lake build --wfail` QA loop on clean builds. Until that is resolved
(either upstream becomes warning-free, or we vendor the needed parts), we keep this file as a
non-broken placeholder that does not import `QuantumInfo`.
-/

end HeytingLean.Quantum
