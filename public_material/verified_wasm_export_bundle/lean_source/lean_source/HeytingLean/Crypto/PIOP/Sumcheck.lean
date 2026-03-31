import HeytingLean.Crypto.PIOP.Multilinear

/-!
# Crypto.PIOP.Sumcheck

Specification façade for the Sumcheck protocol verification equations.

This module intentionally starts at the “equations only” layer:
- the prover is not modelled operationally yet;
- completeness/soundness are exposed as `Prop` statements for later work.

The goal is to provide a stable interface that downstream developments (Fiat–Shamir,
payment-channel proofs, zkVM/AIR encodings) can depend on without committing to a
particular prover implementation.
-/

namespace HeytingLean
namespace Crypto
namespace PIOP
namespace Sumcheck

variable {F : Type} [Field F]

/-- A univariate polynomial presented by evaluation, plus an abstract degree bound predicate. -/
structure RoundPoly where
  eval : F → F
  degreeBound : Prop

/-- A Sumcheck transcript for an `n`-variate multilinear polynomial.

We represent round objects as `Nat → ...` to avoid committing to a concrete container
or dependent indexing; only indices `< n` are relevant for verification. -/
structure Transcript (n : Nat) where
  claimedSum : F
  polys      : Nat → RoundPoly (F := F)
  challenges : Nat → F

/-- Claim value entering round `i`.

`claimAt 0` is the initial claimed sum. For `i+1`, the claim is the previous round
polynomial evaluated at the previous challenge. -/
def claimAt {n : Nat} (tr : Transcript (F := F) n) : Nat → F
  | 0     => tr.claimedSum
  | i + 1 => (tr.polys i).eval (tr.challenges i)

/-- Round check equation: `g_i(0) + g_i(1) = claimAt i`. -/
def roundCheck {n : Nat} (tr : Transcript (F := F) n) (i : Nat) : Prop :=
  let g := tr.polys i
  g.eval 0 + g.eval 1 = claimAt tr i

/-- Final check: after `n` rounds, the remaining claim matches evaluation of `p` at the
challenge point. -/
def finalCheck {n : Nat} (p : MultilinearPoly (F := F) n) (tr : Transcript (F := F) n) : Prop :=
  p.eval (fun i => tr.challenges i.val) = claimAt tr n

/-- Verification predicate for a Sumcheck transcript. -/
def verify {n : Nat} (p : MultilinearPoly (F := F) n) (tr : Transcript (F := F) n) : Prop :=
  (∀ i, i < n → roundCheck tr i) ∧ finalCheck p tr

/-- Abstract completeness statement: the protocol can produce verifiable transcripts for
the true hypercube sum. -/
def CompletenessStatement {n : Nat} (p : MultilinearPoly (F := F) n) : Prop :=
  ∃ tr : Transcript (F := F) n,
    verify p tr ∧ tr.claimedSum = MultilinearPoly.hypercubeSum p

/-- Abstract soundness statement: any verifiable transcript implies the claimed sum is the
true hypercube sum. -/
def SoundnessStatement {n : Nat} (p : MultilinearPoly (F := F) n) : Prop :=
  ∀ tr : Transcript (F := F) n,
    verify p tr → tr.claimedSum = MultilinearPoly.hypercubeSum p

end Sumcheck
end PIOP
end Crypto
end HeytingLean
