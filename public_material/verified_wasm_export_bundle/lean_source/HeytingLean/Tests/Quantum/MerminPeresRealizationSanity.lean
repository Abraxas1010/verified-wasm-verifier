import HeytingLean.LoF.CryptoSheaf.Quantum.MerminPeres
import HeytingLean.Quantum.Contextuality.MerminPeresRealization

namespace HeytingLean.Tests.Quantum

open scoped BigOperators

-- Combinatorial obstruction exists (parity proof).
example :=
  HeytingLean.LoF.CryptoSheaf.Quantum.MerminPeres.no_assignment

-- Quantum realization satisfies the operator product constraints.
example :=
  HeytingLean.Quantum.Contextuality.MerminPeres.row1_prod

example :=
  HeytingLean.Quantum.Contextuality.MerminPeres.col3_prod

end HeytingLean.Tests.Quantum
