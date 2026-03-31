import HeytingLean.Quantum.Contextuality.MerminPeresRealization
import HeytingLean.LoF.CryptoSheaf.Quantum.MerminPeres

/-!
# Mermin–Peres contextuality (packaging)

This file links:
- the purely combinatorial parity obstruction (`no_assignment`) from the LoF/CryptoSheaf layer, and
- the explicit two-qubit matrix realization from `HeytingLean.Quantum.Contextuality`.

It provides a stable `HeytingLean.Quantum.Contextuality.MerminPeres.*` access point.
-/

namespace HeytingLean
namespace Quantum
namespace Contextuality
namespace MerminPeres

abbrev no_assignment :=
  HeytingLean.LoF.CryptoSheaf.Quantum.MerminPeres.no_assignment

/-!
The explicit two-qubit matrix realization theorems already live in this namespace via
`HeytingLean.Quantum.Contextuality.MerminPeresRealization`, e.g.
`HeytingLean.Quantum.Contextuality.MerminPeres.row1_prod` and
`HeytingLean.Quantum.Contextuality.MerminPeres.col3_prod`.
-/

end MerminPeres
end Contextuality
end Quantum
end HeytingLean
