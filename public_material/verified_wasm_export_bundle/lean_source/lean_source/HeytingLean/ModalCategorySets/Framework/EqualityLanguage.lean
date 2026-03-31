import Mathlib.Data.List.Range

namespace HeytingLean.ModalCategorySets.Framework.Equality

universe u

abbrev Var := Nat
abbrev Valuation (α : Type u) := Var → α
abbrev Accessibility := {α β : Type u} → (α → β) → Prop

/-- Extend a valuation with a fresh de Bruijn variable at index `0`. -/
def extend {α : Type u} (ρ : Valuation α) (a : α) : Valuation α :=
  fun
  | 0 => a
  | n + 1 => ρ n

@[simp] theorem extend_zero {α : Type u} (ρ : Valuation α) (a : α) :
    extend ρ a 0 = a := rfl

@[simp] theorem extend_succ {α : Type u} (ρ : Valuation α) (a : α) (n : Nat) :
    extend ρ a (n + 1) = ρ n := rfl

/-- Equality-only first-order modal assertions over de Bruijn variables. -/
inductive EqAssertion : Type
| falsum : EqAssertion
| atomEq : Var → Var → EqAssertion
| impl : EqAssertion → EqAssertion → EqAssertion
| conj : EqAssertion → EqAssertion → EqAssertion
| disj : EqAssertion → EqAssertion → EqAssertion
| forallQ : EqAssertion → EqAssertion
| existsQ : EqAssertion → EqAssertion
| boxQ : EqAssertion → EqAssertion
| diaQ : EqAssertion → EqAssertion

namespace EqAssertion

def top : EqAssertion := .impl .falsum .falsum
def neg (φ : EqAssertion) : EqAssertion := .impl φ .falsum

end EqAssertion

/-- Satisfaction for equality assertions over an explicit admissibility predicate. -/
def Holds (admits : Accessibility) {α : Type u} (ρ : Valuation α) : EqAssertion → Prop
  | .falsum => False
  | .atomEq x y => ρ x = ρ y
  | .impl φ ψ => Holds admits ρ φ → Holds admits ρ ψ
  | .conj φ ψ => Holds admits ρ φ ∧ Holds admits ρ ψ
  | .disj φ ψ => Holds admits ρ φ ∨ Holds admits ρ ψ
  | .forallQ φ => ∀ a : α, Holds admits (extend ρ a) φ
  | .existsQ φ => ∃ a : α, Holds admits (extend ρ a) φ
  | .boxQ φ => ∀ β : Type u, ∀ f : α → β, admits f → Holds admits (fun x => f (ρ x)) φ
  | .diaQ φ => ∃ β : Type u, ∃ f : α → β, admits f ∧ Holds admits (fun x => f (ρ x)) φ

@[simp] theorem holds_neg_atomEq_iff {admits : Accessibility} {α : Type u} (ρ : Valuation α)
    (x y : Var) :
    Holds admits ρ (EqAssertion.neg (.atomEq x y)) ↔ ρ x ≠ ρ y := by
  simp [EqAssertion.neg, Holds]

def conjList : List EqAssertion → EqAssertion
  | [] => EqAssertion.top
  | φ :: φs => .conj φ (conjList φs)

def disjList : List EqAssertion → EqAssertion
  | [] => .falsum
  | φ :: φs => .disj φ (disjList φs)

/-- All unordered pairs from a list, used for pairwise equality/disequality constraints. -/
def allPairs : List Var → List (Var × Var)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ allPairs xs

def eqPairsFormula (pairs : List (Var × Var)) : EqAssertion :=
  conjList (pairs.map (fun p => .atomEq p.1 p.2))

def neqPairsFormula (pairs : List (Var × Var)) : EqAssertion :=
  conjList (pairs.map (fun p => EqAssertion.neg (.atomEq p.1 p.2)))

def pairwiseDistinct (vars : List Var) : EqAssertion :=
  neqPairsFormula (allPairs vars)

def partitionFormula (equalPairs unequalPairs : List (Var × Var)) : EqAssertion :=
  .conj (eqPairsFormula equalPairs) (neqPairsFormula unequalPairs)

def existsN : Nat → EqAssertion → EqAssertion
  | 0, φ => φ
  | n + 1, φ => .existsQ (existsN n φ)

def forallN : Nat → EqAssertion → EqAssertion
  | 0, φ => φ
  | n + 1, φ => .forallQ (forallN n φ)

/-- There are at least `n` distinct elements in the current world. -/
def atLeastCardinality (n : Nat) : EqAssertion :=
  existsN n (pairwiseDistinct (List.range n))

/-- There are at most `n` elements in the current world. -/
def atMostCardinality (n : Nat) : EqAssertion :=
  forallN (n + 1) (disjList ((allPairs (List.range (n + 1))).map (fun p => .atomEq p.1 p.2)))

/-- Exact finite-cardinality sentence in the equality language. -/
def exactCardinality (n : Nat) : EqAssertion :=
  .conj (atLeastCardinality n) (atMostCardinality n)

end HeytingLean.ModalCategorySets.Framework.Equality
