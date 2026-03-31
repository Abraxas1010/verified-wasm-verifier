import Mathlib.Logic.Relation
import HeytingLean.WPP.Wolfram.RewriteFresh

namespace HeytingLean
namespace WPP
namespace Wolfram

/-!
# Causal invariance (Wolfram Physics notion) for single-LHS rules

The Wolfram Physics Project characterizes **causal invariance** via **branch-pair
resolution**: when two distinct updates are possible from the same state, the resulting
branches must eventually **reconverge** (possibly after several further updates).

This file sets up the *relation-theoretic* definitions we use for that notion in the
fresh-vertex semantics (`SystemFresh`), with the intention of proving the Wolfram Physics
claim:

> If a rule has a single relation on its left-hand side, then the system is causally invariant.

We treat reconvergence **up to vertex renaming** (`HGraph.Iso`), since fresh vertices are
names with no intrinsic meaning.
-/

universe u v

namespace SystemFresh

variable {V : Type u} {P : Type v} (sys : SystemFresh V P)
variable [DecidableEq V]

open SystemFresh

/-! ## One-step and multi-step relations (with explicit fresh choices) -/

/-- One-step rewrite relation for `SystemFresh`, with an **explicit** fresh assignment. -/
def StepWith (s t : HGraph V) : Prop :=
  ∃ e : sys.Event,
    ∃ τ : Fin (e.rule.nFresh) → V,
      e.Applicable s ∧ e.FreshAssign τ s ∧ e.applyWith τ s = t

/-- Reflexive–transitive closure of `StepWith`. -/
abbrev StepStarWith : HGraph V → HGraph V → Prop :=
  Relation.ReflTransGen (StepWith (sys := sys))

/-! ## Branch resolution up to vertex renaming -/

/-- Two states are *joinable* if they can be evolved to isomorphic states. -/
def JoinableIso (b c : HGraph V) : Prop :=
  ∃ d₁ d₂,
    StepStarWith (sys := sys) b d₁ ∧
    StepStarWith (sys := sys) c d₂ ∧
    HGraph.Iso d₁ d₂

/-- A one-step branch-pair from `a` resolves if its endpoints are joinable up to isomorphism. -/
def BranchResolves (a b c : HGraph V) : Prop :=
  StepWith (sys := sys) a b →
  StepWith (sys := sys) a c →
  JoinableIso (sys := sys) b c

/-- **Causal invariance** (Wolfram Physics / "branch-pair resolution"): every one-step fork resolves. -/
def CausalInvariant : Prop :=
  ∀ a b c, StepWith (sys := sys) a b → StepWith (sys := sys) a c → JoinableIso (sys := sys) b c

end SystemFresh

end Wolfram
end WPP
end HeytingLean
