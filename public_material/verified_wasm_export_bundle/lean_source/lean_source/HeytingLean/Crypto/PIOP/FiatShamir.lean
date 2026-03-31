import HeytingLean.Crypto.PIOP.Sumcheck

/-!
# Crypto.PIOP.FiatShamir

Specification façade for the Fiat–Shamir transform.

This module provides:
- an abstract oracle interface (`Oracle`) with `absorb`/`squeeze`; and
- a small non-interactive constructor for Sumcheck transcripts, deriving challenges
  from an oracle run.

The oracle is intentionally abstract: concrete instantiations can be modelled as
hash-to-field constructions, sponge challengers, random oracles, or executable
implementations with test vectors.
-/

namespace HeytingLean
namespace Crypto
namespace PIOP
namespace FiatShamir

/-- Abstract Fiat–Shamir oracle (a.k.a. challenger / transcript hash).

`Absorb` is the type of items fed into the transcript.
`Challenge` is the type of derived challenges (e.g. field elements). -/
class Oracle (Absorb Challenge : Type) where
  State : Type
  init : String → State
  absorb : State → Absorb → State
  squeeze : State → Challenge

namespace Oracle

variable {Absorb Challenge : Type} [Oracle Absorb Challenge]

/-- Apply `absorb` to a list of items. -/
def absorbMany (st : Oracle.State (Absorb := Absorb) (Challenge := Challenge)) (xs : List Absorb) :
    Oracle.State (Absorb := Absorb) (Challenge := Challenge) :=
  xs.foldl Oracle.absorb st

end Oracle

/-- Bundled transcript state for an oracle. -/
structure Transcript (Absorb Challenge : Type) [Oracle Absorb Challenge] where
  label : String
  st    : Oracle.State (Absorb := Absorb) (Challenge := Challenge)

namespace Transcript

variable {Absorb Challenge : Type} [Oracle Absorb Challenge]

def init (label : String) : Transcript Absorb Challenge :=
  { label := label, st := Oracle.init label }

def absorb (t : Transcript Absorb Challenge) (x : Absorb) : Transcript Absorb Challenge :=
  { t with st := Oracle.absorb t.st x }

def absorbMany (t : Transcript Absorb Challenge) (xs : List Absorb) : Transcript Absorb Challenge :=
  { t with st := Oracle.absorbMany (Absorb := Absorb) (Challenge := Challenge) t.st xs }

def squeeze (t : Transcript Absorb Challenge) : Challenge :=
  Oracle.squeeze t.st

end Transcript

/-! ## Non-interactive Sumcheck transcript construction

We derive Sumcheck challenges by hashing:
1. the claimed sum; then
2. each round polynomial; then
3. the newly-squeezed challenge (so later challenges depend on earlier ones).

All encoding details are explicit parameters (`encodeClaim`, `encodePoly`, `encodeChal`), so this
layer stays independent of any concrete serialization.
-/

namespace Sumcheck

open HeytingLean.Crypto.PIOP.Sumcheck

variable {F : Type} [Field F]

/-- Oracle-driven challenge derivation for Sumcheck. -/
def deriveChallenges
    {Absorb : Type}
    [Oracle Absorb F]
    (encodeClaim : F → Absorb)
    (encodePoly  : RoundPoly (F := F) → Absorb)
    (encodeChal  : F → Absorb)
    (label : String)
    (claimedSum : F)
    (polys : Nat → RoundPoly (F := F)) :
    Nat → F :=
  fun i =>
    let t0 : Transcript Absorb F :=
      (Transcript.init (Absorb := Absorb) (Challenge := F) label).absorb (encodeClaim claimedSum)
    let round (j : Nat) (t : Transcript Absorb F) : Transcript Absorb F × F :=
      let t1 := t.absorb (encodePoly (polys j))
      let r := t1.squeeze
      let t2 := t1.absorb (encodeChal r)
      (t2, r)
    let rec go : Nat → Transcript Absorb F → Transcript Absorb F × F
      | 0, t => round 0 t
      | k + 1, t =>
          let (t', _) := go k t
          round (k + 1) t'
    (go i t0).2

/-- Build a non-interactive Sumcheck transcript by deriving challenges from the oracle.

The resulting transcript is intended to be checked by `Sumcheck.verify`. -/
def mkTranscript
    {n : Nat}
    {Absorb : Type}
    [Oracle Absorb F]
    (encodeClaim : F → Absorb)
    (encodePoly  : RoundPoly (F := F) → Absorb)
    (encodeChal  : F → Absorb)
    (label : String)
    (claimedSum : F)
    (polys : Nat → RoundPoly (F := F)) :
    HeytingLean.Crypto.PIOP.Sumcheck.Transcript (F := F) n :=
  { claimedSum := claimedSum
  , polys := polys
  , challenges := deriveChallenges
      (F := F)
      (Absorb := Absorb)
      encodeClaim encodePoly encodeChal label claimedSum polys }

end Sumcheck

end FiatShamir
end PIOP
end Crypto
end HeytingLean
