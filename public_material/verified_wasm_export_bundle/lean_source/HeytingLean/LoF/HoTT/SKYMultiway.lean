import Mathlib.Data.Finset.Basic
import HeytingLean.LoF.HoTT.SKYBridge
import HeytingLean.WPP.Multiway

/-
SKY / comparison nucleus bridge to WPP-style multiway semantics.

We instantiate the generic `WppRule` interface on small fixed-point
cores `ΩR` arising from comparison nuclei, starting with the Boolean
example `boolCompSpec`. This yields an explicit two-branch multiway
graph whose edges correspond exactly to the RT-1 branches, and which
is combinatorially joined via the SKY identity bridge.
-/

namespace HeytingLean
namespace LoF
namespace HoTT

open Comparison Comb WPP

open scoped Classical

/-- For convenience we equip the Boolean fixed-point core with a
decidable equality instance, so that we can use `Finset`-based
multiway rules. -/
noncomputable instance :
    DecidableEq (Comparison.ΩR Comparison.boolCompSpec) :=
  Classical.decEq _

/-- Multiway rule mirroring the two RT-1 branches on `ΩR` for the
Boolean comparison nucleus. From any state `a`, we may step either to
`a` itself (the identity branch) or to `dec (enc a)` (the encoded
round-trip branch). -/
noncomputable def boolComparisonRule :
    WppRule (Comparison.ΩR Comparison.boolCompSpec) :=
{ step := fun a =>
    let b :=
      Comparison.dec Comparison.boolCompSpec
        (Comparison.enc Comparison.boolCompSpec a)
    {a, b} }

/-- The successors of `boolComparisonRule` at a state `a` are exactly
the two RT-1 branches `a` and `dec (enc a)`. -/
lemma boolComparisonRule_targets_eq (a : Comparison.ΩR Comparison.boolCompSpec) :
    ∀ b, b ∈ boolComparisonRule.step a ↔
      (b = a ∨
       b = Comparison.dec Comparison.boolCompSpec
              (Comparison.enc Comparison.boolCompSpec a)) := by
  classical
  intro b
  -- Expand the definition of the successor finset `{a, dec (enc a)}`.
  simp [boolComparisonRule]

/-- Equivalence between the WPP-style multiway successors of
`boolComparisonRule` and the abstract two-branch relation
`stepComparison` for `boolCompSpec`. -/
lemma boolComparisonRule_stepComparison_targets
    (a : Comparison.ΩR Comparison.boolCompSpec) :
    ∀ b, b ∈ boolComparisonRule.step a ↔
      stepComparison (S := Comparison.boolCompSpec) a b := by
  classical
  intro b
  constructor
  · -- From multiway membership to the abstract two-branch step.
    intro hb
    have hb' :=
      (boolComparisonRule_targets_eq a b).1 hb
    rcases hb' with h | h
    · -- Identity branch: `b = a`.
      subst h
      -- This is the `step_g` branch of `StepFG`.
      unfold stepComparison
      exact StepFG.step_g _
    · -- Round-trip branch: `b = dec (enc a)`.
      subst h
      unfold stepComparison
      exact StepFG.step_f _
  · -- From the abstract two-branch step back to multiway membership.
    intro hb
    unfold stepComparison at hb
    -- `hb` is either the round-trip or identity branch.
    have hb' :
        b = a ∨
        b = Comparison.dec Comparison.boolCompSpec
                (Comparison.enc Comparison.boolCompSpec a) := by
      cases hb with
      | step_f =>
          right
          rfl
      | step_g =>
          left
          rfl
    exact (boolComparisonRule_targets_eq a b).2 hb'

/-- Decidable equality on the four-state ΩR core for `fin2CompSpec`. -/
noncomputable instance :
    DecidableEq (Comparison.ΩR Comparison.fin2CompSpec) :=
  Classical.decEq _

/-- Multiway rule mirroring the two RT-1 branches on `ΩR` for the
`Set (Fin 2)` comparison nucleus. -/
noncomputable def fin2ComparisonRule :
    WppRule (Comparison.ΩR Comparison.fin2CompSpec) :=
{ step := fun a =>
    let b :=
      Comparison.dec Comparison.fin2CompSpec
        (Comparison.enc Comparison.fin2CompSpec a)
    {a, b} }

/-- Membership-level description of the successors of
`fin2ComparisonRule`. -/
lemma fin2ComparisonRule_targets_eq
    (a : Comparison.ΩR Comparison.fin2CompSpec) :
    ∀ b, b ∈ fin2ComparisonRule.step a ↔
      (b = a ∨
       b = Comparison.dec Comparison.fin2CompSpec
              (Comparison.enc Comparison.fin2CompSpec a)) := by
  classical
  intro b
  simp [fin2ComparisonRule]

/-- Equivalence between the WPP-style multiway successors of
`fin2ComparisonRule` and the abstract two-branch relation
`stepComparison` for `fin2CompSpec`. -/
lemma fin2ComparisonRule_stepComparison_targets
    (a : Comparison.ΩR Comparison.fin2CompSpec) :
    ∀ b, b ∈ fin2ComparisonRule.step a ↔
      stepComparison (S := Comparison.fin2CompSpec) a b := by
  classical
  intro b
  constructor
  · -- From multiway membership to the abstract two-branch step.
    intro hb
    have hb' :=
      (fin2ComparisonRule_targets_eq a b).1 hb
    rcases hb' with h | h
    · -- Identity branch: `b = a`.
      subst h
      unfold stepComparison
      exact StepFG.step_g _
    · -- Round-trip branch: `b = dec (enc a)`.
      subst h
      unfold stepComparison
      exact StepFG.step_f _
  · -- From the abstract two-branch step back to multiway membership.
    intro hb
    unfold stepComparison at hb
    -- `hb` is either the round-trip or identity branch.
    have hb' :
        b = a ∨
        b = Comparison.dec Comparison.fin2CompSpec
                (Comparison.enc Comparison.fin2CompSpec a) := by
      cases hb with
      | step_f =>
          right
          rfl
      | step_g =>
          left
          rfl
    exact (fin2ComparisonRule_targets_eq a b).2 hb'

end HoTT
end LoF
end HeytingLean
