import Mathlib.Data.List.Basic
import HeytingLean.Meta.AIT.Prefix

/-
# Democratic model voting over prefix-coded programs

This module builds a small layer on top of the AIT prefix core:

* A finite family of models with:
  * a program `code : M → Program`,
  * a prediction function `predict : M → D → O`,
  * a Boolean consistency predicate `consistent : M → D → Bool`;
* simple democratic voting by counting consistent models supporting
  a given outcome;
* a length-bounded variant that only counts models whose codes are
  at most a given length;
* an `occamPreference` predicate expressing that, for a fixed
  length budget, one outcome receives at least as many votes from
  simple models as another.

This does not yet state or prove a general Occam theorem; rather,
it provides the combinatorial quantities that such a theorem will
relate. The design is intentionally modest and free of axioms or
dummy semantics so it can be safely extended in later phases.
-/

namespace HeytingLean.Meta.AIT

open Program

variable {M D O : Type}

/-- A finite family of models with prefix codes, predictions, and a
Boolean consistency predicate. -/
structure ModelFamily (M D O : Type) where
  /-- Finite list of models under consideration. -/
  models     : List M
  /-- Code assignment: how each model is represented as a bitstring. -/
  code       : M → Program
  /-- Prediction function: given past data, each model produces an outcome. -/
  predict    : M → D → O
  /-- Boolean consistency predicate with respect to past data. -/
  consistent : M → D → Bool

namespace ModelFamily

variable (F : ModelFamily M D O)

/-! ### Code-level structure: prefix-freeness and injectivity -/

/-- The set of codes used by a model family, restricted to its
finite list of models. -/
def codeSet : Set Program :=
  { p | ∃ m ∈ F.models, F.code m = p }

/-- Codes are prefix-free if the images of the models (as programs)
form a prefix-free family. -/
def codesPrefixFree : Prop :=
  PrefixFree F.codeSet

/-- Codes are injective if distinct models in the family never share
the same program. -/
def codesInjective : Prop :=
  Function.Injective F.code

/-! Basic consequence: under prefix-freeness and injectivity, the
codes of any two distinct models are never in the prefix relation
in either direction. -/

lemma no_prefix_of_distinct
    (hPF : F.codesPrefixFree) (hInj : F.codesInjective)
    {m₁ m₂ : M} (h₁ : m₁ ∈ F.models) (h₂ : m₂ ∈ F.models)
    (hne : m₁ ≠ m₂) :
    ¬ IsPrefix (F.code m₁) (F.code m₂) ∧
      ¬ IsPrefix (F.code m₂) (F.code m₁) := by
  -- Lift the model-level statements to the code set and apply the
  -- generic `PrefixFree.pair` lemma.
  unfold codesPrefixFree codeSet at hPF
  have hp : F.code m₁ ∈ F.codeSet := ⟨m₁, h₁, rfl⟩
  have hq : F.code m₂ ∈ F.codeSet := ⟨m₂, h₂, rfl⟩
  have hcode_ne : F.code m₁ ≠ F.code m₂ := by
    intro hc
    apply hne
    exact hInj hc
  exact PrefixFree.pair (C := F.codeSet) hPF hp hq hcode_ne

section Voting

variable [DecidableEq O]

/-- Models in `F` that are consistent with `past` and predict `out`.

We stay in `Bool` for consistency and prediction tests so that this
remains executable and easy to connect to external numerics. -/
def votesFor (past : D) (out : O) : List M :=
  F.models.filter fun m =>
    F.consistent m past &&
      decide (F.predict m past = out)

/-- Democratic vote count for an outcome `out` given past data:
the number of models in `F` that are consistent with `past` and
predict `out`. -/
def voteCount (past : D) (out : O) : Nat :=
  (F.votesFor past out).length

lemma voteCount_nonneg (past : D) (out : O) :
    0 ≤ F.voteCount past out := by
  unfold voteCount
  exact Nat.zero_le _

/-- Models in `F` that are consistent with `past`, predict `out`,
and whose code length is at most the given bound `L`. -/
def votesForBounded (past : D) (out : O) (L : Nat) : List M :=
  (F.votesFor past out).filter fun m =>
    decide (codeLength (F.code m) ≤ L)

/-- Democratic vote count restricted to models with code length at
most `L`. -/
def voteCountBounded (past : D) (out : O) (L : Nat) : Nat :=
  (F.votesForBounded past out L).length

lemma voteCountBounded_nonneg (past : D) (out : O) (L : Nat) :
    0 ≤ F.voteCountBounded past out L := by
  unfold voteCountBounded
  exact Nat.zero_le _

/-- Simple Occam-style inequality: the number of length-bounded votes
is always at most the total number of votes, since the bounded voters
are a subset of the full voters. -/
lemma voteCountBounded_le_voteCount (past : D) (out : O) (L : Nat) :
    F.voteCountBounded past out L ≤ F.voteCount past out := by
  unfold voteCountBounded voteCount votesForBounded
  -- Work with a shorthand for the predicate used in the bounded filter.
  let p : M → Bool := fun m => decide (codeLength (F.code m) ≤ L)
  -- Use the standard length/filter identity: `l.length = (l.filter p).length + (l.filter (!p ·)).length`.
  have hb :
      ((F.votesFor past out).filter p).length ≤
        ((F.votesFor past out).filter p).length +
          ((F.votesFor past out).filter (!p ·)).length :=
    Nat.le_add_right _ _
  -- Rewrite the right-hand side using the identity, then simplify.
  have hlen :
      (F.votesFor past out).length =
        ((F.votesFor past out).filter p).length +
          ((F.votesFor past out).filter (!p ·)).length :=
    List.length_eq_length_filter_add (l := F.votesFor past out) (f := p)
  have : ((F.votesFor past out).filter p).length ≤
      (F.votesFor past out).length := by
    simpa [hlen] using hb
  exact this

/-- An Occam-style preference: among models with code length at most
`L`, outcome `outSimple` receives at least as many votes as outcome
`outComplex` under the same past data. -/
def occamPreference (past : D) (outSimple outComplex : O) (L : Nat) : Prop :=
  F.voteCountBounded past outSimple L ≥ F.voteCountBounded past outComplex L

end Voting

end ModelFamily

end HeytingLean.Meta.AIT
