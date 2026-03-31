import HeytingLean.LeanClef.DTS.AbelianGroup

/-!
# LeanClef.DTS.HMUnification

Formalize the structure of HM unification extended with dimensional
constraints, and prove principality for the ground (variable-free)
base case.

Reference: Haynes arXiv:2603.16437, Section 2.2; Kennedy (2009)

Mathematical content:
Standard HM generates type constraints.
DTS adds dimensional constraints: each arithmetic operation generates
a linear equation over Z^n.
The combined system is solved by:
  1. Standard HM unification for type structure
  2. Gaussian elimination over Z^n for dimensional constraints
Both are decidable and principal.

This module formalizes: DimExpr (dimension expressions with variables),
Unifier, satisfiesConstraint/satisfiesAll, isPrincipalUnifier, and
proves the ground_principal theorem (variable-free constraints have
a trivially principal unifier). Full variable unification via
Gaussian elimination over Z is future work (see comment at end).
-/

namespace LeanClef.DTS

/-- Dimension expression with unification variables. -/
inductive DimExpr (n : Nat) where
  | var : Nat → DimExpr n
  | const : Dimension n → DimExpr n
  | add : DimExpr n → DimExpr n → DimExpr n
  | sub : DimExpr n → DimExpr n → DimExpr n
  deriving DecidableEq

/-- A unifier maps variable indices to concrete dimensions. -/
def Unifier (n : Nat) := Nat → Option (Dimension n)

/-- Evaluate a DimExpr under a unifier. -/
def DimExpr.eval (σ : Unifier n) : DimExpr n → Option (Dimension n)
  | .var i => σ i
  | .const d => some d
  | .add e1 e2 => do
    let d1 ← e1.eval σ
    let d2 ← e2.eval σ
    pure (mulDimension d1 d2)
  | .sub e1 e2 => do
    let d1 ← e1.eval σ
    let d2 ← e2.eval σ
    pure (divDimension d1 d2)

/-- Collect the set of variable indices in a DimExpr. -/
def DimExpr.vars : DimExpr n → List Nat
  | .var i => [i]
  | .const _ => []
  | .add e1 e2 => e1.vars ++ e2.vars
  | .sub e1 e2 => e1.vars ++ e2.vars

/-- A unifier satisfies a constraint when both sides evaluate to the same dimension. -/
def satisfiesConstraint (σ : Unifier n) (c : DimExpr n × DimExpr n) : Prop :=
  c.1.eval σ = c.2.eval σ

/-- A unifier satisfies all constraints. -/
def satisfiesAll (σ : Unifier n) (cs : Array (DimExpr n × DimExpr n)) : Prop :=
  ∀ c ∈ cs.toList, satisfiesConstraint σ c

/-- A unifier σ₁ is more general than σ₂ if σ₂ extends σ₁:
    every variable mapped by σ₁ is mapped the same way by σ₂. -/
def moreGeneral (σ₁ σ₂ : Unifier n) : Prop :=
  ∀ i d, σ₁ i = some d → σ₂ i = some d

/-- A principal unifier satisfies all constraints and is more general
    than any other satisfying unifier. -/
def isPrincipalUnifier (σ : Unifier n) (cs : Array (DimExpr n × DimExpr n)) : Prop :=
  satisfiesAll σ cs ∧ ∀ σ', satisfiesAll σ' cs → moreGeneral σ σ'

/-- For ground constraints (no variables), the identity unifier works. -/
def groundUnifier : Unifier n := fun _ => none

def ground_constraint_decidable (d1 d2 : Dimension n) :
    Decidable (DimExpr.eval groundUnifier (.const d1) =
               DimExpr.eval groundUnifier (.const d2)) := by
  simp [DimExpr.eval]
  exact instDecidableEqDimension d1 d2

/-- Principality for ground constraints: the identity unifier is trivially principal
    when all constraints are between constants. This is the honest base case.
    Full variable unification requires row reduction over Z (future work). -/
theorem ground_principal
    (cs : Array (DimExpr n × DimExpr n))
    (_h_ground : ∀ c ∈ cs.toList, ∃ d1 d2 : Dimension n, c = (.const d1, .const d2))
    (h_sat : satisfiesAll groundUnifier cs) :
    isPrincipalUnifier groundUnifier cs :=
  ⟨h_sat, fun _ _ i _ h_contra => by simp [groundUnifier] at h_contra⟩

-- Full variable unification is implemented in GaussianElim.lean via
-- row reduction over Z with back-substitution (RREF). The ground case
-- above remains the proved base; the executable solver in GaussianElim
-- handles the general case including multi-variable interacting systems.
-- Key correctness lemmas proved: constPart_eq_scalarEval_zero (constant
-- extraction), additive_combination_preserves (row operation invariant),
-- rref_unique_solution (RREF forces unique variable values).
-- Multi-variable correctness verified via native_decide on 2- and
-- 3-variable systems with solution value extraction.

end LeanClef.DTS
