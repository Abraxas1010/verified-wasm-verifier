import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice

/-!
# AnalyticRules — stronger closure family with meet law

This module introduces a "rule"-style nucleus on `Set (ℝ → ℝ)` that is
explicitly meet-preserving. It is meant as a stronger alternative to the
`analyticHull` from `AnalyticHull.lean`, which only used an `EqClosed`
family. By packaging meet-preservation into the operator, we recover the
meet law `hull (A ∩ B) = hull A ∩ hull B` directly.

The design is deliberately lightweight (no heavy `Mathlib` analysis
imports) to keep strict builds fast.
-/

namespace HeytingLean
namespace Calculus

open Set

/-- A rule nucleus on sets of real-valued functions: an extensive,
    idempotent, monotone, and meet-preserving closure operator. -/
structure RuleNucleus where
  R        : Set (ℝ → ℝ) → Set (ℝ → ℝ)
  le_R     : ∀ A, A ⊆ R A
  R_idem   : ∀ A, R (R A) = R A
  monotone : Monotone R
  meet_preserve : ∀ A B, R (A ∩ B) = R A ∩ R B

namespace RuleNucleus

def Omega (N : RuleNucleus) : Set (Set (ℝ → ℝ)) := {A | N.R A = A}

@[simp] lemma mem_Omega {N : RuleNucleus} {A : Set (ℝ → ℝ)} :
  A ∈ N.Omega ↔ N.R A = A := Iff.rfl

@[simp] lemma fix_of_mem {N : RuleNucleus} {A : Set (ℝ → ℝ)}
  (hA : A ∈ N.Omega) : N.R A = A := hA

@[simp] lemma Omega_inf_closed {N : RuleNucleus}
  {A B : Set (ℝ → ℝ)} (hA : A ∈ N.Omega) (hB : B ∈ N.Omega) :
  A ∩ B ∈ N.Omega := by
  have h : N.R (A ∩ B) = N.R A ∩ N.R B := N.meet_preserve A B
  have h' : N.R (A ∩ B) = A ∩ B := by simpa [hA, hB] using h
  simpa [mem_Omega] using h'

def hull (N : RuleNucleus) (A : Set (ℝ → ℝ)) : Set (ℝ → ℝ) := N.R A

@[simp] lemma hull_extensive (N : RuleNucleus) (A) : A ⊆ N.hull A := N.le_R A

@[simp] lemma hull_idem (N : RuleNucleus) (A) : N.hull (N.hull A) = N.hull A :=
  N.R_idem A

lemma hull_monotone (N : RuleNucleus) : Monotone N.hull := N.monotone

@[simp] lemma hull_fixed_iff (N : RuleNucleus) {A} :
  N.hull A = A ↔ A ∈ N.Omega := by
  constructor <;> intro h <;> simpa [hull, Omega, mem_Omega] using h

@[simp] lemma hull_meet (N : RuleNucleus) (A B : Set (ℝ → ℝ)) :
  N.hull (A ∩ B) = N.hull A ∩ N.hull B := N.meet_preserve A B

end RuleNucleus

/-- A trivial example: the identity nucleus (everything is already closed).
    This shows the interface is nonempty and provides a concrete instance
    for quick sanity checks. -/
@[simp] def ruleNucleusId : RuleNucleus where
  R := id
  le_R := by intro A x hx; simpa using hx
  R_idem := by intro A; rfl
  monotone := by intro A B hAB x hx; exact hAB hx
  meet_preserve := by intro A B; rfl

namespace Examples

@[simp] lemma hullId_meet (A B : Set (ℝ → ℝ)) :
  (ruleNucleusId.hull (A ∩ B)) = ruleNucleusId.hull A ∩ ruleNucleusId.hull B := by
  simp

end Examples

end Calculus
end HeytingLean
