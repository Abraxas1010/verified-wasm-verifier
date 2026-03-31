import HeytingLean.Chem.Reactions.Reaction
import Mathlib.Data.Fintype.Basic

/-!
# Reaction balancing (bounded search, soundness proved)

This module provides a small, deterministic reaction balancer.

Current solver is intentionally simple:
- bounded search over coefficient vectors in `[1..maxCoeff]`;
- returns the first certificate it finds.

Soundness is proved: any returned coefficients satisfy `Balanced`.

This is a pragmatic v1 implementation. If/when we need a faster / unbounded solver,
we can switch the search backend (e.g. Gaussian elimination over `ℚ`) while keeping
the same certificate interface and soundness theorem.
-/

namespace HeytingLean.Chem.Reactions

open HeytingLean.Chem

def mkTerms (coeffs : List Nat) (forms : List Formula) : List StoichTerm :=
  (List.zip coeffs forms).map (fun cf => { coeff := cf.1, formula := cf.2 })

def BalancedPointwise (reactants products : List StoichTerm) : Prop :=
  ∀ e : HeytingLean.Chem.PeriodicTable.Element, (total reactants) e = (total products) e

theorem balanced_iff_pointwise (reactants products : List StoichTerm) :
    Balanced reactants products ↔ BalancedPointwise reactants products := by
  constructor
  · intro h e
    -- `h : total reactants = total products`
    simpa [Balanced] using congrArg (fun f => f e) h
  · intro h
    -- ext on the (finite) element type
    apply funext
    intro e
    exact h e

def coeffsUpTo (maxCoeff : Nat) : List Nat :=
  (List.range maxCoeff).map (fun k => k + 1)

def coeffVectors : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | n+1, maxCoeff =>
      (coeffsUpTo maxCoeff).flatMap (fun c =>
        (coeffVectors n maxCoeff).map (fun cs => c :: cs))

def findFirstCert? {α : Type} (p : α → Prop) [DecidablePred p] :
    List α → Option { a : α // p a }
  | [] => none
  | a :: as =>
      if h : p a then
        some ⟨a, h⟩
      else
        findFirstCert? p as

/--
Try to balance a reaction by bounded search.

Returns coefficients *together with a proof* that they balance the reaction.
-/
def balanceCert? (reactants products : List Formula) (maxCoeff : Nat := 6) :
    Option { coeffs : List Nat × List Nat //
      Balanced (mkTerms coeffs.1 reactants) (mkTerms coeffs.2 products) } := by
  let rCands := coeffVectors reactants.length maxCoeff
  let pCands := coeffVectors products.length maxCoeff
  let cands : List (List Nat × List Nat) :=
    rCands.flatMap (fun rc => pCands.map (fun pc => (rc, pc)))
  let p : (List Nat × List Nat) → Prop := fun cp =>
    BalancedPointwise (mkTerms cp.1 reactants) (mkTerms cp.2 products)
  -- Find a pointwise-balanced candidate, then convert pointwise equality to `Balanced`.
  let inst : DecidablePred p := fun cp => by
    -- `BalancedPointwise` is decidable because `Element` is finite (`Fin 118`).
    dsimp [p, BalancedPointwise]
    infer_instance
  refine (@findFirstCert? (List Nat × List Nat) p inst cands).map ?_
  intro cert
  exact ⟨cert.1, (balanced_iff_pointwise _ _).2 cert.2⟩

def balance? (reactants products : List Formula) (maxCoeff : Nat := 6) :
    Option (List Nat × List Nat) :=
  (balanceCert? reactants products maxCoeff).map (fun c => c.1)

theorem balance?_sound {reactants products : List Formula} {maxCoeff : Nat}
    {coeffs : List Nat × List Nat} :
    balance? reactants products maxCoeff = some coeffs →
      Balanced (mkTerms coeffs.1 reactants) (mkTerms coeffs.2 products) := by
  intro h
  unfold balance? at h
  -- Use the shape of `Option.map`; do *not* unfold the search implementation.
  cases hcert : balanceCert? reactants products maxCoeff with
  | none =>
      simp [hcert] at h
  | some cert =>
      simp [hcert] at h
      cases h
      simpa using cert.2

end HeytingLean.Chem.Reactions
