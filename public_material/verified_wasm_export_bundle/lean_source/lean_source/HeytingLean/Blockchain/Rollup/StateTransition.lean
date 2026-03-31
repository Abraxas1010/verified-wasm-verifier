import HeytingLean.LoF.Nucleus
import HeytingLean.Epistemic.Occam
import HeytingLean.Crypto.Form
import HeytingLean.Crypto.Compile
import HeytingLean.Crypto.CoreSemantics

/-!
# Rollup State Transition — Core Spec (Ω_R)

Abstract, lens-agnostic specification of a rollup state transition as a
core `Form` with an environment in `Ω_R`.
-/

namespace HeytingLean
namespace Blockchain
namespace Rollup

open HeytingLean.LoF
open HeytingLean.Crypto

universe u v w

variable {α : Type u} [PrimaryAlgebra α]

/-- Rollup transition specification parametric over the core and arity. -/
structure Spec (R : Reentry α) (n : ℕ) where
  State : Type v
  transitionForm : State → State → Crypto.Form n
  env : (s₁ s₂ : State) → Crypto.EnvΩ (R := R) n

namespace Spec

variable {R : Reentry α} {n : ℕ}

/-- Core validity: the transition evaluates to top in Ω_R under the provided env. -/
def validTransition (S : Spec (R := R) n) (s₁ s₂ : S.State) : Prop :=
  Crypto.Form.evalΩ (R := R) (S.transitionForm s₁ s₂) (S.env s₁ s₂) = ⊤

/-- Compiled program corresponding to the transition. -/
def program (S : Spec (R := R) n) (s₁ s₂ : S.State) : Crypto.Program n :=
  Crypto.Form.compile (S.transitionForm s₁ s₂)

/-- Occam-reduced core evaluation (equal to the original since evalΩ yields a fixed point). -/
noncomputable def occamEval (S : Spec (R := R) n) (s₁ s₂ : S.State) : α :=
  HeytingLean.Epistemic.occam (R := R)
    (((Crypto.Form.evalΩ (R := R) (S.transitionForm s₁ s₂) (S.env s₁ s₂)) : R.Omega) : α)

lemma occamEval_eq_eval (S : Spec (R := R) n) (s₁ s₂ : S.State) :
    S.occamEval s₁ s₂
      = ((Crypto.Form.evalΩ (R := R) (S.transitionForm s₁ s₂) (S.env s₁ s₂)) : R.Omega) := by
  unfold Spec.occamEval
  set a : α :=
    (((Crypto.Form.evalΩ (R := R) (S.transitionForm s₁ s₂) (S.env s₁ s₂)) : R.Omega) : α)
  have hfix : R a = a := by
    simp [a]
  have hle : HeytingLean.Epistemic.occam (R := R) a ≤ a :=
    le_trans (HeytingLean.Epistemic.occam_le_reentry (R := R) a) (le_of_eq hfix)
  have hge : a ≤ HeytingLean.Epistemic.occam (R := R) a :=
    HeytingLean.Epistemic.occam_contains_candidate (R := R) (a := a) (u := a) le_rfl hfix
  exact le_antisymm hle hge

end Spec

/-! ## Examples

A tiny always-true transition spec to exercise the pipeline. -/

namespace Examples

variable {R : Reentry α}

/-- Trivial spec: transition formula is `⊤`, environment is constant `⊤`. -/
def demoSpec (R : Reentry α) : Spec (R := R) 1 :=
  { State := Nat
    transitionForm := fun _ _ => Crypto.Form.top
    env := fun _ _ => fun _ => (⊤ : R.Omega) }

@[simp] lemma demoSpec_valid (s₁ s₂ : Nat) :
    (demoSpec (R := R)).validTransition s₁ s₂ := by
  simp [demoSpec, Spec.validTransition, Crypto.Form.evalΩ_top]

end Examples

/-! ### Counter example (non-trivial) -/

structure Counter where
  val : Nat
  limit : Nat

/-- Counter transition: increment under guard and preserve limit. -/
def counter (R : Reentry α) : Spec (R := R) 2 :=
  { State := Counter
    transitionForm := fun _ _ =>
      -- var 0: guard; var 1: postcondition
      Crypto.Form.and (Crypto.Form.var ⟨0, by decide⟩)
                     (Crypto.Form.var ⟨1, by decide⟩)
    env := fun s₁ s₂ =>
      fun i =>
        if h0 : i = ⟨0, by decide⟩ then
          -- guard: s₁.val + 1 ≤ s₁.limit
          if s₁.val + 1 ≤ s₁.limit then (⊤ : R.Omega) else (⊥ : R.Omega)
        else if h1 : i = ⟨1, by decide⟩ then
          -- post: s₂ reflects the step and preserves the limit
          if s₂.val = s₁.val + 1 ∧ s₂.limit = s₁.limit then (⊤ : R.Omega) else (⊥ : R.Omega)
        else (⊥ : R.Omega) }

@[simp] lemma counter_accept (R : Reentry α)
    (s : Counter) (hguard : s.val + 1 ≤ s.limit) :
    (counter (R := R)).validTransition s { val := s.val + 1, limit := s.limit } := by
  -- unfold and reduce the environment branches to ⊤
  simp [counter, Spec.validTransition, Crypto.Form.evalΩ_and,
        Crypto.Form.evalΩ_var, hguard]

@[simp] lemma counter_eval_guard_false (R : Reentry α)
    (s : Counter) (s' : Counter) (hguard : ¬ s.val + 1 ≤ s.limit) :
    Crypto.Form.evalΩ (R := R)
      ((counter (R := R)).transitionForm s s')
      ((counter (R := R)).env s s') = (⊥ : R.Omega) := by
  -- guard branch returns ⊥, so the conjunction evaluates to ⊥
  simp [counter, Crypto.Form.evalΩ_and, Crypto.Form.evalΩ_var, hguard]

@[simp] lemma counter_eval_step_false (R : Reentry α)
    (s : Counter) (s' : Counter)
    (hstep : s'.val ≠ s.val + 1 ∨ s'.limit ≠ s.limit) :
    Crypto.Form.evalΩ (R := R)
      ((counter (R := R)).transitionForm s s')
      ((counter (R := R)).env s s') = (⊥ : R.Omega) := by
  -- postcondition branch returns ⊥
  rcases hstep with hne | hne
  · have : ¬ (s'.val = s.val + 1 ∧ s'.limit = s.limit) := by
      intro h; exact hne h.1
    simp [counter, Crypto.Form.evalΩ_and, Crypto.Form.evalΩ_var, this]
  · have : ¬ (s'.val = s.val + 1 ∧ s'.limit = s.limit) := by
      intro h; exact hne h.2
    simp [counter, Crypto.Form.evalΩ_and, Crypto.Form.evalΩ_var, this]

end Rollup
end Blockchain
end HeytingLean
