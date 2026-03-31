import HeytingLean.Crypto.Lattice.NTTIterative

/-!
# NTT iterative export hooks (FFI scaffolding)

This module provides **exported** Lean symbols for the iterative NTT routine.

It is intentionally minimal:
- it exports total functions (no panics) by checking the input length; and
- it does not attempt to provide a stable C ABI for `Array`/`ZMod` (that belongs in a dedicated
  extraction/FFI track).

The immediate goal is to make it easy to experiment with Lean's `@[export]` mechanism and keep a
stable symbol name for future wiring.
-/

namespace HeytingLean
namespace Crypto
namespace Lattice
namespace NTTIterativeExport

open HeytingLean.Crypto.Lattice.NTTIterative

abbrev F : Type := ZMod NTT.q

@[export heyting_ntt_forward]
def nttForward (coeffs : Array F) : Array F :=
  if h : coeffs.size = 256 then
    nttIterative coeffs h
  else
    coeffs

@[export heyting_ntt_inverse]
def nttInverse (coeffs : Array F) : Array F :=
  if h : coeffs.size = 256 then
    inttIterative coeffs h
  else
    coeffs

end NTTIterativeExport
end Lattice
end Crypto
end HeytingLean
