import HeytingLean.LeanCP.Core.HProp
import HeytingLean.LeanCP.Core.SepLog
import HeytingLean.LeanCP.VCG.Entailment

/-!
# LeanCP XSimp Tactic

Simplification tactic for separation logic entailments.
Given a goal `P1 ∗ P2 ∗ ... ⊢ₛ Q1 ∗ Q2 ∗ ...`, cancels matching
predicates on both sides.

Adapted from SPlean/Theories/XSimp.lean (ported from Lean 4.11 to 4.24).
This is a simplified version that handles the common cases for LeanCP.
-/

namespace HeytingLean.LeanCP

open Lean Elab Tactic Meta in
/-- `leancp_xsimp` — simplify separation logic entailments by:
    1. Unfolding `entails`, `HProp.sep`, `HProp.emp`
    2. Applying `simp` with separation logic lemmas
    3. Trying to close goals with `SepLog` structural rules -/
elab "leancp_xsimp" : tactic => do
  -- Strategy: unfold definitions and apply simp with our lemma set
  evalTactic (← `(tactic|
    (try simp only [entails, HProp.sep, HProp.emp, HProp.pure,
                    HProp.hexists, HProp.hand, HProp.pointsTo,
                    store, Heap.empty, Heap.write, Heap.union,
                    Finmap.Disjoint])
    <;> (first
          | exact heap_entails_refl _
          | exact heap_entails_emp_left _
          | exact heap_entails_emp_right _
          | exact state_entails_refl _
          | exact state_entails_emp_left _
          | exact state_entails_emp_right _
          | skip)
    <;> (try constructor)
    <;> (try intro)
    <;> (try assumption)
    <;> (try exact ⟨_, _, by assumption, rfl, by assumption, by assumption⟩)))

end HeytingLean.LeanCP
