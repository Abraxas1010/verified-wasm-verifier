import Mathlib.Data.List.Infix
import HeytingLean.Blockchain.Consensus.Core

/-
# Consensus.LongestChain

Minimal longest-chain-style safety lemmas on top of the core consensus
model. We assume that there exists, for each time `t`, a canonical
chain `canonical t` such that every honest node's chain at time `t`
is a prefix of `canonical t`. Under this assumption we prove:

* `NoFork` for the execution; and
* `CommonPrefix k` for every `k`.

These theorems are intended as a first structural realisation of
`Consensus.Spec.PropertyId.noForkTheorem` and
`Consensus.Spec.PropertyId.commonPrefixProperty` under a simple
longest-chain assumption, without yet modelling adversary fractions,
probabilities, or protocol-specific dynamics.
-/

namespace HeytingLean
namespace Blockchain
namespace Consensus
namespace LongestChain

open Core

abbrev Chain := Core.Chain

/-- Bridge between the custom `isPrefix` relation used in
    `Consensus.Core` and the standard `List.IsPrefix` relation from
    Mathlib. -/
lemma isPrefix_iff_listIsPrefix (c₁ c₂ : Chain) :
    Core.isPrefix c₁ c₂ ↔ List.IsPrefix c₁ c₂ := by
  constructor
  · intro h
    rcases h with ⟨s, hs⟩
    refine ⟨s, ?_⟩
    exact hs.symm
  · intro h
    rcases h with ⟨s, hs⟩
    refine ⟨s, ?_⟩
    exact hs.symm

/-- Any two prefixes of the same chain are comparable by the prefix
    relation. This is the list-theoretic heart of the longest-chain
    argument: if honest chains are prefixes of a canonical chain, they
    are mutually prefix-comparable. -/
lemma isPrefix_comparable_of_prefix_same
    (c₁ c₂ c : Chain)
    (h₁ : Core.isPrefix c₁ c)
    (h₂ : Core.isPrefix c₂ c) :
    Core.isPrefix c₁ c₂ ∨ Core.isPrefix c₂ c₁ := by
  classical
  -- Translate to `List.IsPrefix` and express each prefix as a `take`
  -- of the canonical chain, indexed by its own length.
  have h₁' : List.IsPrefix c₁ c :=
    (isPrefix_iff_listIsPrefix _ _).1 h₁
  have h₂' : List.IsPrefix c₂ c :=
    (isPrefix_iff_listIsPrefix _ _).1 h₂
  have hEq₁ : c₁ = c.take c₁.length :=
    (List.prefix_iff_eq_take).1 h₁'
  have hEq₂ : c₂ = c.take c₂.length :=
    (List.prefix_iff_eq_take).1 h₂'
  -- Compare the lengths of the two prefixes.
  have hlen :
      c₁.length ≤ c₂.length ∨ c₂.length ≤ c₁.length :=
    Nat.le_total c₁.length c₂.length
  cases hlen with
  | inl hle =>
      -- `c.take c₁.length` is a prefix of `c.take c₂.length`.
      have hPref_take :
          List.IsPrefix (c.take c₁.length) (c.take c₂.length) := by
        have hdisj :
            c₁.length ≤ c₂.length ∨ c.length ≤ c₂.length :=
          Or.inl hle
        have hLemma :=
          (List.take_isPrefix_take (l := c)
            (m := c₁.length) (n := c₂.length))
        exact hLemma.mpr hdisj
      -- Unfold the prefix relation and transfer it back to `c₁`, `c₂`.
      rcases hPref_take with ⟨s, hs⟩
      -- `hs` has type `c.take c₁.length ++ s = c.take c₂.length`.
      -- Rewrite both sides using the characterisations of `c₁` and `c₂`.
      have hs₂ : c₁ ++ s = c₂ := by
        simpa [hEq₁.symm, hEq₂.symm] using hs
      have hPref : List.IsPrefix c₁ c₂ := by
        exact ⟨s, hs₂⟩
      left
      exact (isPrefix_iff_listIsPrefix _ _).2 hPref
  | inr hle =>
      -- Symmetric case: `c.take c₂.length` is a prefix of `c.take c₁.length`.
      have hPref_take :
          List.IsPrefix (c.take c₂.length) (c.take c₁.length) := by
        have hdisj :
            c₂.length ≤ c₁.length ∨ c.length ≤ c₁.length :=
          Or.inl hle
        have hLemma :=
          (List.take_isPrefix_take (l := c)
            (m := c₂.length) (n := c₁.length))
        exact hLemma.mpr hdisj
      rcases hPref_take with ⟨s, hs⟩
      -- `hs` has type `c.take c₂.length ++ s = c.take c₁.length`.
      -- Rewrite both sides using the characterisations of `c₂` and `c₁`.
      have hs₂ : c₂ ++ s = c₁ := by
        simpa [hEq₂.symm, hEq₁.symm] using hs
      have hPref : List.IsPrefix c₂ c₁ := by
        exact ⟨s, hs₂⟩
      right
      exact (isPrefix_iff_listIsPrefix _ _).2 hPref

/-- Longest-chain-style no-fork theorem: if there exists a canonical
    chain `canonical t` for each time such that every honest node's
    chain is a prefix of `canonical t`, then `NoFork` holds. -/
theorem noFork_longestChain
    (exec : Execution) (canonical : Time → Chain)
    (hPrefix :
      ∀ (t : Time) (n : NodeId),
        exec.honest n → Core.isPrefix (exec.chainAt t n) (canonical t)) :
    NoFork exec := by
  intro t n₁ n₂ h₁ h₂
  -- Both honest chains are prefixes of the same canonical chain.
  have h₁' : Core.isPrefix (exec.chainAt t n₁) (canonical t) :=
    hPrefix t n₁ h₁
  have h₂' : Core.isPrefix (exec.chainAt t n₂) (canonical t) :=
    hPrefix t n₂ h₂
  -- Use comparability of prefixes of `canonical t`.
  exact
    isPrefix_comparable_of_prefix_same
      (c₁ := exec.chainAt t n₁)
      (c₂ := exec.chainAt t n₂)
      (c := canonical t) h₁' h₂'

/-- Longest-chain-style common-prefix theorem: under the same prefix
    assumption as `noFork_longestChain`, honest nodes share a common
    prefix at every time (for any `k`, which is currently a blueprint
    index and does not constrain the prefix length). -/
theorem commonPrefix_longestChain
    (k : Nat) (exec : Execution) (canonical : Time → Chain)
    (hPrefix :
      ∀ (t : Time) (n : NodeId),
        exec.honest n → Core.isPrefix (exec.chainAt t n) (canonical t)) :
    CommonPrefix k exec := by
  intro t n₁ n₂ h₁ h₂
  have h₁' : Core.isPrefix (exec.chainAt t n₁) (canonical t) :=
    hPrefix t n₁ h₁
  have h₂' : Core.isPrefix (exec.chainAt t n₂) (canonical t) :=
    hPrefix t n₂ h₂
  have hComp :=
    isPrefix_comparable_of_prefix_same
      (c₁ := exec.chainAt t n₁)
      (c₂ := exec.chainAt t n₂)
      (c := canonical t) h₁' h₂'
  -- Take as common prefix whichever chain is shorter in the prefix order.
  cases hComp with
  | inl hPref =>
      refine ⟨exec.chainAt t n₁, ?_⟩
      exact And.intro (Core.isPrefix_refl _) hPref
  | inr hPref =>
      refine ⟨exec.chainAt t n₂, ?_⟩
      exact And.intro hPref (Core.isPrefix_refl _)

/-- Registry-level no-fork instance under the longest-chain assumption:
    whenever all honest chains are prefixes of a canonical chain, the
    registry predicate `Spec.PropertyId.noForkTheorem` holds. -/
theorem propertyHolds_noFork_longestChain
    (exec : Execution) (canonical : Time → Chain)
    (hPrefix :
      ∀ (t : Time) (n : NodeId),
        exec.honest n → Core.isPrefix (exec.chainAt t n) (canonical t)) :
    Core.propertyHolds exec Spec.PropertyId.noForkTheorem := by
  have h : NoFork exec :=
    noFork_longestChain exec canonical hPrefix
  simpa [Core.propertyHolds] using h

/-- Registry-level common-prefix instance under the longest-chain
    assumption: for any fixed `k`, the predicate
    `Spec.PropertyId.commonPrefixProperty` holds for the given
    execution. -/
theorem propertyHolds_commonPrefix_longestChain
    (k : Nat) (exec : Execution) (canonical : Time → Chain)
    (hPrefix :
      ∀ (t : Time) (n : NodeId),
        exec.honest n → Core.isPrefix (exec.chainAt t n) (canonical t)) :
    Core.propertyHolds exec Spec.PropertyId.commonPrefixProperty := by
  have h : CommonPrefix k exec :=
    commonPrefix_longestChain k exec canonical hPrefix
  have hExists : ∃ k', CommonPrefix k' exec := ⟨k, h⟩
  simpa [Core.propertyHolds] using hExists

end LongestChain
end Consensus
end Blockchain
end HeytingLean
