import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors

namespace HeytingLean
namespace Matula

/--
Internal search: return the `(remaining+1)`-th prime after `candidate`.
This is a temporary executable scaffold for Phase I; proof-facing lemmas are
tracked separately in PM artifacts.
-/
partial def nthPrimeAfter (remaining candidate : Nat) : Nat :=
  let c := candidate + 1
  if c.Prime then
    if remaining = 0 then c
    else nthPrimeAfter (remaining - 1) c
  else
    nthPrimeAfter remaining c

/--
1-indexed prime accessor: `nthPrime 1 = 2`, `nthPrime 2 = 3`, ...
Returns `2` for input `0` to keep totality while we keep the bijection domain as
positive naturals in higher layers.
-/
def nthPrime (n : Nat) : Nat :=
  if n = 0 then 2 else nthPrimeAfter (n - 1) 1

/-- Internal search for 1-indexed prime position. -/
partial def primeIndexAux (target candidate idx : Nat) : Nat :=
  let c := candidate + 1
  if c.Prime then
    let idx' := idx + 1
    if c = target then idx' else primeIndexAux target c idx'
  else
    primeIndexAux target c idx

/--
1-indexed prime position. Returns `0` for non-prime inputs.
Phase I will tighten this with theorem-facing lemmas over `Nat.Prime p`.
-/
def primeIndex (p : Nat) : Nat :=
  if p.Prime then primeIndexAux p 1 0 else 0

end Matula
end HeytingLean
