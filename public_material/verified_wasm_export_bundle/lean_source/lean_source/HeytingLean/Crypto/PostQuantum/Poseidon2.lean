import Mathlib.Data.ZMod.Basic

/-!
# Crypto.PostQuantum.Poseidon2

Specification façade for the Poseidon2 permutation.

This module keeps Poseidon2 *abstract*:
- parameters and round constants are bundled as structures; and
- the permutation itself is a single `permute` function.

This is intended for reuse by the `leanEthereum/leanSig` family of constructions, which use
Poseidon2 for tweakable hashes and message hashing.

References:
- Poseidon2 (design/parameters): https://eprint.iacr.org/2023/323
- Upstream usage (Rust): `external/leanSig/src/symmetric/tweak_hash/poseidon.rs`
-/

namespace HeytingLean
namespace Crypto
namespace PostQuantum
namespace Poseidon2

/-- Poseidon2 parameter bundle.

`p` is the modulus used by `ZMod p` to model the underlying field.
`t` is the permutation width (state size). -/
structure Params where
  p       : Nat
  t       : Nat
  roundsF : Nat
  roundsP : Nat
  alpha   : Nat

/-- Underlying field type used by this spec layer. -/
abbrev F (P : Params) := ZMod P.p

/-- Poseidon2 state: a width-`t` vector of field elements. -/
abbrev State (P : Params) := Fin P.t → F P

/-- Round constants and linear layer parameters.

This keeps the constant tables explicit (externalized), so concrete parameter sets can be
introduced later without changing interfaces. -/
structure Constants (P : Params) where
  rcF  : Fin P.roundsF → Fin P.t → F P
  rcP  : Fin P.roundsP → F P
  mds  : Fin P.t → Fin P.t → F P
  diag : Fin P.t → F P

/-- Poseidon2 S-box (power map). -/
def sbox (P : Params) (x : F P) : F P :=
  x ^ P.alpha

/-- Abstract Poseidon2 permutation over a fixed parameter set and constants. -/
structure Permutation (P : Params) (C : Constants P) where
  permute : State P → State P

namespace State

variable {P : Params}

def add (x y : State P) : State P := fun i => x i + y i

def zero : State P := fun _ => 0

end State

namespace Permutation

variable {P : Params} {C : Constants P}

/-- Feed-forward compression (as used in `leanSig`):
`compress(x) = permute(x) + x` (pointwise). -/
def compress (perm : Permutation P C) (x : State P) : State P :=
  State.add (perm.permute x) x

/-- Zero-padding embed: map an `n`-vector into the width-`t` state by filling the remaining
coordinates with zero. -/
def pad {n : Nat} (_hn : n ≤ P.t) (x : Fin n → F P) : State P :=
  fun i =>
    if h : i.val < n then
      x ⟨i.val, h⟩
    else
      0

/-- Truncate a state to its first `k` coordinates. -/
def truncate (k : Nat) (hk : k ≤ P.t) (x : State P) : Fin k → F P :=
  fun i => x ⟨i.val, lt_of_lt_of_le i.isLt hk⟩

/-- Convenience: pad, permute, feed-forward, then truncate.

This matches the common Poseidon2 compression/sponge interface shape in upstream implementations.
Any padding-collision mitigation (length encoding, domain separation) is handled at higher layers. -/
def compressPadded
    {n outLen : Nat}
    (hn : n ≤ P.t)
    (hout : outLen ≤ P.t)
    (perm : Permutation P C)
    (x : Fin n → F P) :
    Fin outLen → F P :=
  truncate outLen hout (compress perm (pad (P := P) hn x))

end Permutation

end Poseidon2
end PostQuantum
end Crypto
end HeytingLean
