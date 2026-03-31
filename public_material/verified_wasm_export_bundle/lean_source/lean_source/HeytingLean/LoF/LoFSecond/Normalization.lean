import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Filter
import HeytingLean.LoF.LoFSecond.Rewrite

/-!
# LoFSecond.Normalization — 3-valued semantics for re-entry + rewrite soundness

The primary-algebra development `LoFPrimary.Normalization` uses classical two-valued semantics
(`Bool`) and therefore **cannot** model re-entry as a fixed point of negation.

Here we supply a minimal, QA-friendly semantics by extending the truth values to a Kleene-style
three-valued type:

* `f`  : false
* `u`  : unknown / indeterminate
* `t`  : true

with negation fixing `u`.  We interpret:

* `void`    ↦ `f`
* `mark`    ↦ negation
* `juxt`    ↦ Kleene disjunction (max under `f < u < t`)
* `reentry` ↦ `u`

This makes the re-entry reduction `mark reentry ↦ reentry` semantically sound.

As in the primary development, we also provide a finite truth-table canonicalization via
`valueSet`, since `Fin n → Tri` is finite.
-/

namespace HeytingLean
namespace LoF
namespace LoFSecond

open Expr

/-! ## Truth values (Kleene-style) -/

inductive Tri where
  | f
  | u
  | t
  deriving DecidableEq, Repr

namespace Tri

instance : Fintype Tri where
  elems := {Tri.f, Tri.u, Tri.t}
  complete := by
    intro x
    cases x <;> simp

/-- Kleene negation with a fixed point `u`. -/
def not : Tri → Tri
  | .f => .t
  | .u => .u
  | .t => .f

/-- Kleene disjunction (max under `f < u < t`). -/
def or : Tri → Tri → Tri
  | .f, b => b
  | .u, .f => .u
  | .u, .u => .u
  | .u, .t => .t
  | .t, _ => .t

@[simp] theorem not_f : not .f = .t := rfl
@[simp] theorem not_u : not .u = .u := rfl
@[simp] theorem not_t : not .t = .f := rfl

@[simp] theorem not_not : ∀ a : Tri, not (not a) = a := by
  intro a
  cases a <;> rfl

@[simp] theorem or_f_left (a : Tri) : or .f a = a := rfl
@[simp] theorem or_t_left (a : Tri) : or .t a = .t := by cases a <;> rfl

@[simp] theorem or_self : ∀ a : Tri, or a a = a := by
  intro a
  cases a <;> rfl

end Tri

/-! ## Semantics -/

variable {n : Nat}

def eval : Expr n → (Fin n → Tri) → Tri
  | .void, _ => .f
  | .var i, ρ => ρ i
  | .mark A, ρ => Tri.not (eval A ρ)
  | .juxt A B, ρ => Tri.or (eval A ρ) (eval B ρ)
  | .reentry, _ => .u

/-! ## Canonicalization by value-sets -/

def valueSet (A : Expr n) (v : Tri) : Finset (Fin n → Tri) :=
  Finset.filter (fun ρ => eval A ρ = v) Finset.univ

@[simp] theorem mem_valueSet {A : Expr n} {ρ : Fin n → Tri} {v : Tri} :
    ρ ∈ valueSet (n := n) A v ↔ eval A ρ = v := by
  simp [valueSet]

/-! ## Semantic equivalence -/

def Eqv (A B : Expr n) : Prop :=
  ∀ ρ : Fin n → Tri, eval A ρ = eval B ρ

theorem eqv_iff_valueSet_eq {A B : Expr n} :
    Eqv (n := n) A B ↔ ∀ v : Tri, valueSet (n := n) A v = valueSet (n := n) B v := by
  constructor
  · intro h v
    ext ρ
    simp [valueSet, h ρ]
  · intro h ρ
    -- Pick the value `v := eval A ρ` and use equality of the corresponding value-sets.
    have hv : valueSet (n := n) A (eval (n := n) A ρ) =
        valueSet (n := n) B (eval (n := n) A ρ) := h (eval (n := n) A ρ)
    have hmem : ρ ∈ valueSet (n := n) B (eval (n := n) A ρ) := by
      have : ρ ∈ valueSet (n := n) A (eval (n := n) A ρ) := by
        simp
      simpa [hv] using this
    exact
      ((mem_valueSet (n := n) (A := B) (ρ := ρ) (v := eval (n := n) A ρ)).1 hmem).symm

/-! ## Soundness of the rewrite rules -/

theorem step_sound {A B : Expr n} : Step A B → Eqv (n := n) A B := by
  intro h ρ
  induction h with
  | calling A =>
      simp [eval, Tri.or_self]
  | crossing A =>
      simp [eval, Tri.not_not]
  | void_left A =>
      simp [eval]
  | void_right A =>
      -- Use the `or` truth table: `or a f = a` holds by cases.
      cases hA : eval (n := n) A ρ <;> simp [eval, Tri.or, hA]
  | reentry =>
      simp [eval]
  | juxt_left _ ih =>
      simp [eval, ih]
  | juxt_right _ ih =>
      simp [eval, ih]
  | mark_congr _ ih =>
      simp [eval, ih]

theorem steps_sound {A B : Expr n} : Steps A B → Eqv (n := n) A B := by
  intro h
  induction h with
  | refl A =>
      intro ρ
      rfl
  | trans hstep hsteps ih =>
      intro ρ
      exact (step_sound (n := n) hstep ρ).trans (ih ρ)

end LoFSecond
end LoF
end HeytingLean
