import HeytingLean.Crypto.Lattice.NTTBridge
import HeytingLean.Crypto.Lattice.NTTIterative
import Mathlib.Tactic

/-!
# NTT iterative vs quadratic spec: basis-vector agreement (computed)

This file records a strong, fully checkable sanity fact:

`NTTIterative.nttIterative` agrees with the quadratic-factor specification `NTTBridge.quadraticSpec`
on all 256 standard basis vectors.

This is *not* the final Gap 1 refinement theorem (which quantifies over all inputs), but it is a
useful certified milestone:
- it pins down ordering/twiddle conventions at the matrix-entry level;
- it supports future proofs by reducing the remaining work to establishing linearity/compositionality
  of the iterative algorithm.
-/

namespace HeytingLean
namespace Crypto
namespace Lattice
namespace NTTIterativeBasisAgreement

open HeytingLean.Crypto.Lattice.NTTIterative
open HeytingLean.Crypto.Lattice.NTTBridge

abbrev q : Nat := HeytingLean.Crypto.Lattice.NTT.q
abbrev F : Type := ZMod q

def basisArray (i : Fin 256) : Array F :=
  Array.ofFn (fun j : Fin 256 => if j = i then (1 : F) else 0)

theorem nttIterative_eq_quadraticSpec_on_basis :
    ∀ i : Fin 256,
      nttIterative (basisArray i) (by simp [basisArray]) = quadraticSpec (basisArray i) := by
  native_decide

end NTTIterativeBasisAgreement
end Lattice
end Crypto
end HeytingLean

