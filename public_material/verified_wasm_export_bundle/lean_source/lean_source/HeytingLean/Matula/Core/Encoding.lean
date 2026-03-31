import HeytingLean.Matula.Core.Primes
import HeytingLean.Matula.Core.RootedTree

namespace HeytingLean
namespace Matula

/-- Encode a rooted tree into a Matula-style natural. -/
def matula : RTree → Nat
  | .leaf => 1
  | .node children =>
      children.foldl (fun acc t => acc * nthPrime (matula t)) 1

/-- Expand prime factors of `n` with multiplicity (via `Nat.primeFactorsList`). -/
def expandedPrimeFactors (n : Nat) : List Nat :=
  n.primeFactorsList

end Matula
end HeytingLean
