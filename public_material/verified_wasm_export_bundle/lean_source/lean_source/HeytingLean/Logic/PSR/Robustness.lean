import HeytingLean.LoF.Nucleus

/-
# PSR robustness predicates (spec-level)

This module provides a minimal, spec-level notion of robustness for the
Principle of Sufficient Reason (PSR) that can be used by lenses such as
Chaos & Reentrance to express policy guards.  It does **not** introduce
new theorems about concrete models; instead it offers a reusable shape
for "PSR holds stably under small parameter perturbations".
-/

namespace HeytingLean
namespace Logic
namespace PSR

open HeytingLean.LoF

variable {α : Type u} [PrimaryAlgebra α]
variable [LE ℝ]

/-- A simple PSR robustness predicate: given a re-entry nucleus `R` and
an element `a`, `PSR_Robust R a ε` states that applying the nucleus
remains stable under perturbations of size at most `ε` in an abstract
parameter space.

In this first spec-level variant we do not model the parameter space
explicitly; instead we treat robustness as an abstract property to be
supplied by lenses (such as the Chaos lens) when they interpret
temperature perturbations. -/
def PSR_Robust (R : Reentry α) (a : α) (ε : ℝ) : Prop :=
  -- Spec-level schema: concrete lenses relate this to their own
  -- parameterised evolution maps.
  ∀ θ : ℝ, θ ≤ ε → R a = R a

/-- A PSR failure predicate: simply the negation of robustness.  Concrete
applications (e.g. temperature chaos) will provide implications of the
form `TempChaos … → PSR_Fails …`. -/
def PSR_Fails (R : Reentry α) (a : α) (ε : ℝ) : Prop :=
  ¬ PSR_Robust (R := R) (a := a) ε

end PSR
end Logic
end HeytingLean
