import Mathlib.Order.Nucleus
import HeytingLean.Core.Nucleus
import HeytingLean.Core.Heyting.Basic
import HeytingLean.Calculus.AnalyticRules
import HeytingLean.Calculus.CalculusLens

namespace HeytingLean
namespace Bridges
namespace Nucleus

open Set

private theorem coreNucleus_ext {L : Type*} [SemilatticeInf L] [OrderBot L]
    {N₁ N₂ : HeytingLean.Core.Nucleus L} (hR : N₁.R = N₂.R) : N₁ = N₂ := by
  cases N₁
  cases N₂
  cases hR
  simp

private theorem heytingNucleus_ext {α : Type*} [HeytingAlgebra α]
    {N₁ N₂ : HeytingLean.Core.Heyting.Nucleus α} (hop : N₁.op = N₂.op) : N₁ = N₂ := by
  cases N₁
  cases N₂
  cases hop
  simp

private theorem calculusNucleus_ext {α : Type*} [CompleteLattice α]
    {N₁ N₂ : HeytingLean.Calculus.CalculusNucleus α} (hR : N₁.R = N₂.R) : N₁ = N₂ := by
  cases N₁
  cases N₂
  cases hR
  simp

/-- Convert `Core.Nucleus` to Mathlib `Nucleus`. -/
def coreToMathlib {L : Type*} [SemilatticeInf L] [OrderBot L]
    (N : HeytingLean.Core.Nucleus L) : _root_.Nucleus L where
  toFun := N.R
  map_inf' := N.meet_preserving
  idempotent' := by
    intro x
    rw [N.idempotent x]
  le_apply' := N.extensive

/-- Convert Mathlib `Nucleus` to `Core.Nucleus`. -/
def mathlibToCore {L : Type*} [SemilatticeInf L] [OrderBot L]
    (N : _root_.Nucleus L) : HeytingLean.Core.Nucleus L where
  R := N
  extensive := fun a => _root_.Nucleus.le_apply (n := N) (x := a)
  idempotent := fun x => _root_.Nucleus.idempotent (n := N) (x := x)
  meet_preserving := fun a b => _root_.Nucleus.map_inf (n := N) (x := a) (y := b)

/-- Mathlib -> Core -> Mathlib is identity. -/
theorem coreToMathlib_mathlibToCore {L : Type*} [SemilatticeInf L] [OrderBot L]
    (N : _root_.Nucleus L) :
    coreToMathlib (mathlibToCore N) = N := by
  ext x
  simp [coreToMathlib, mathlibToCore]

/-- Core -> Mathlib -> Core is identity. -/
theorem mathlibToCore_coreToMathlib {L : Type*} [SemilatticeInf L] [OrderBot L]
    (N : HeytingLean.Core.Nucleus L) :
    mathlibToCore (coreToMathlib N) = N := by
  exact coreNucleus_ext (N₁ := mathlibToCore (coreToMathlib N)) (N₂ := N) rfl

/-- Convert `Core.Heyting.Nucleus` to Mathlib `Nucleus`. -/
def heytingToMathlib {α : Type*} [HeytingAlgebra α]
    (N : HeytingLean.Core.Heyting.Nucleus α) : _root_.Nucleus α where
  toFun := N.op
  map_inf' := N.preserves_meet
  idempotent' := by
    intro x
    rw [N.idempotent x]
  le_apply' := N.extensive

/-- Convert Mathlib `Nucleus` to `Core.Heyting.Nucleus`. -/
def mathlibToHeyting {α : Type*} [HeytingAlgebra α]
    (N : _root_.Nucleus α) : HeytingLean.Core.Heyting.Nucleus α where
  op := N
  extensive := fun x => _root_.Nucleus.le_apply (n := N) (x := x)
  idempotent := fun x => _root_.Nucleus.idempotent (n := N) (x := x)
  preserves_meet := fun x y => _root_.Nucleus.map_inf (n := N) (x := x) (y := y)

/-- Mathlib -> Heyting -> Mathlib is identity. -/
theorem heytingToMathlib_mathlibToHeyting {α : Type*} [HeytingAlgebra α]
    (N : _root_.Nucleus α) :
    heytingToMathlib (mathlibToHeyting N) = N := by
  ext x
  simp [heytingToMathlib, mathlibToHeyting]

/-- Heyting -> Mathlib -> Heyting is identity. -/
theorem mathlibToHeyting_heytingToMathlib {α : Type*} [HeytingAlgebra α]
    (N : HeytingLean.Core.Heyting.Nucleus α) :
    mathlibToHeyting (heytingToMathlib N) = N := by
  exact heytingNucleus_ext (N₁ := mathlibToHeyting (heytingToMathlib N)) (N₂ := N) rfl

private theorem mathlib_nucleus_monotone {α : Type*} [SemilatticeInf α]
    (N : _root_.Nucleus α) : Monotone N :=
  _root_.Nucleus.monotone (n := N)

/-- Convert `RuleNucleus` to Mathlib `Nucleus` on function sets. -/
def ruleToMathlib (N : HeytingLean.Calculus.RuleNucleus) :
    _root_.Nucleus (Set (ℝ → ℝ)) where
  toFun := N.R
  map_inf' := by
    intro A B
    simpa [inf_eq_inter] using N.meet_preserve A B
  idempotent' := by
    intro A
    rw [N.R_idem A]
  le_apply' := N.le_R

/-- Convert Mathlib `Nucleus` on function sets to `RuleNucleus`. -/
def mathlibToRule (N : _root_.Nucleus (Set (ℝ → ℝ))) :
    HeytingLean.Calculus.RuleNucleus where
  R := N
  le_R := fun A => _root_.Nucleus.le_apply (n := N) (x := A)
  R_idem := fun A => _root_.Nucleus.idempotent (n := N) (x := A)
  monotone := mathlib_nucleus_monotone N
  meet_preserve := by
    intro A B
    simpa [inf_eq_inter] using (_root_.Nucleus.map_inf (n := N) (x := A) (y := B))

/-- Mathlib -> Rule -> Mathlib is identity. -/
theorem ruleToMathlib_mathlibToRule
    (N : _root_.Nucleus (Set (ℝ → ℝ))) :
    ruleToMathlib (mathlibToRule N) = N := by
  ext A x
  rfl

/-- Rule -> Mathlib -> Rule is identity. -/
theorem mathlibToRule_ruleToMathlib
    (N : HeytingLean.Calculus.RuleNucleus) :
    mathlibToRule (ruleToMathlib N) = N := by
  cases N
  simp [ruleToMathlib, mathlibToRule]

/-- Convert `CalculusNucleus` to Mathlib `Nucleus`. -/
def calculusToMathlib {α : Type*} [CompleteLattice α]
    (N : HeytingLean.Calculus.CalculusNucleus α) : _root_.Nucleus α where
  toFun := N.R
  map_inf' := N.map_inf
  idempotent' := by
    intro x
    rw [N.idempotent x]
  le_apply' := N.extensive

/-- Convert Mathlib `Nucleus` to `CalculusNucleus`. -/
def mathlibToCalculus {α : Type*} [CompleteLattice α]
    (N : _root_.Nucleus α) : HeytingLean.Calculus.CalculusNucleus α where
  R := N
  extensive := fun a => _root_.Nucleus.le_apply (n := N) (x := a)
  idempotent := fun x => _root_.Nucleus.idempotent (n := N) (x := x)
  map_inf := fun a b => _root_.Nucleus.map_inf (n := N) (x := a) (y := b)

/-- Mathlib -> Calculus -> Mathlib is identity. -/
theorem calculusToMathlib_mathlibToCalculus {α : Type*} [CompleteLattice α]
    (N : _root_.Nucleus α) :
    calculusToMathlib (mathlibToCalculus N) = N := by
  ext x
  simp [calculusToMathlib, mathlibToCalculus]

/-- Calculus -> Mathlib -> Calculus is identity. -/
theorem mathlibToCalculus_calculusToMathlib {α : Type*} [CompleteLattice α]
    (N : HeytingLean.Calculus.CalculusNucleus α) :
    mathlibToCalculus (calculusToMathlib N) = N := by
  exact calculusNucleus_ext
    (N₁ := mathlibToCalculus (calculusToMathlib N)) (N₂ := N) rfl

end Nucleus
end Bridges
end HeytingLean
