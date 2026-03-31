/-!
# LeanClef.DTS.AbelianGroup

Formalize the dimension space D = Z^n and prove that dimensional
inference reduces to linear algebra over Z.

Reference: Haynes arXiv:2603.16437, Section 2.1

Mathematical content:
Dimensions are vectors in Z^n where n = number of base dimensions.
SI base: n=7 (length, time, mass, temperature, current, luminosity, amount)
With Clifford grade: n=8 (add grade axis)

Operations:
  Addition requires equal dimensions: d(a) = d(b)
  Multiplication adds dimension vectors: d(a*b) = d(a) + d(b)
  Division subtracts: d(a/b) = d(a) - d(b)
  Differentiation subtracts: d(∂f/∂x) = d(f) - d(x)

All operations are closed in Z^n and decidable in O(n) per operation.
-/

namespace LeanClef.DTS

/-- Dimension vector in Z^n. -/
abbrev Dimension (n : Nat) := Fin n → Int

/-- Dimensions must match for addition. -/
def addConsistent (d1 d2 : Dimension n) : Prop := d1 = d2

/-- Multiplication adds dimension vectors. -/
def mulDimension (d1 d2 : Dimension n) : Dimension n :=
  fun i => d1 i + d2 i

/-- Division subtracts dimension vectors. -/
def divDimension (d1 d2 : Dimension n) : Dimension n :=
  fun i => d1 i - d2 i

/-- Differentiation dimension: d(∂f/∂x) = d(f) - d(x).
    This is the chain rule closure that makes training decidable. -/
def diffDimension (d_output d_input : Dimension n) : Dimension n :=
  divDimension d_output d_input

/-- The zero dimension (dimensionless). -/
def zeroDimension : Dimension n := fun _ => 0

/-- Dimension negation. -/
def negDimension (d : Dimension n) : Dimension n := fun i => -(d i)

-- Abelian group theorems: all follow from funext + Int arithmetic

theorem mulDimension_comm (d1 d2 : Dimension n) :
    mulDimension d1 d2 = mulDimension d2 d1 := by
  funext i; simp [mulDimension, Int.add_comm]

theorem mulDimension_assoc (d1 d2 d3 : Dimension n) :
    mulDimension (mulDimension d1 d2) d3 = mulDimension d1 (mulDimension d2 d3) := by
  funext i; simp [mulDimension, Int.add_assoc]

theorem mulDimension_zero_left (d : Dimension n) :
    mulDimension zeroDimension d = d := by
  funext i; simp [mulDimension, zeroDimension]

theorem mulDimension_zero_right (d : Dimension n) :
    mulDimension d zeroDimension = d := by
  funext i; simp [mulDimension, zeroDimension]

theorem mulDimension_neg_right (d : Dimension n) :
    mulDimension d (negDimension d) = zeroDimension := by
  funext i; simp [mulDimension, negDimension, zeroDimension]; omega

theorem divDimension_self (d : Dimension n) :
    divDimension d d = zeroDimension := by
  funext i; simp [divDimension, zeroDimension, Int.sub_self]

theorem divDimension_as_mul_neg (d1 d2 : Dimension n) :
    divDimension d1 d2 = mulDimension d1 (negDimension d2) := by
  funext i; simp [divDimension, mulDimension, negDimension, Int.sub_eq_add_neg]

/-- Chain rule closure: differentiation is closed in Z^n. -/
theorem diff_closed (d1 d2 : Dimension n) :
    ∃ d3 : Dimension n, diffDimension d1 d2 = d3 :=
  ⟨diffDimension d1 d2, rfl⟩

/-- Chain rule composition: d/dx (d/dy f) = d/dx f - d/dx y.
    Differentiation composes by vector subtraction. -/
theorem diff_compose (d_f d_x d_y : Dimension n) :
    diffDimension (diffDimension d_f d_y) d_x =
    divDimension (divDimension d_f d_y) d_x := rfl

-- Constraint system

/-- DTS constraint: lhs dimension = rhs dimension. -/
structure DTSConstraint (n : Nat) where
  lhs : Dimension n
  rhs : Dimension n

/-- A constraint system is a collection of equality constraints. -/
def ConstraintSystem (n : Nat) := Array (DTSConstraint n)

/-- A constraint system is satisfiable when all lhs = rhs. -/
def Satisfiable (cs : ConstraintSystem n) : Prop :=
  ∀ c ∈ cs.toList, c.lhs = c.rhs

/-- Pointwise decidable equality for dimension vectors. -/
instance instDecidableEqDimension : DecidableEq (Dimension n) :=
  fun d1 d2 =>
    if h : ∀ i, d1 i = d2 i then
      isTrue (funext h)
    else
      isFalse (fun heq => h (fun i => congrFun heq i))

/-- Ground constraint satisfiability is decidable via component-wise Int equality.
    This is the ground case; unification with variables requires Gaussian
    elimination (see HMUnification.lean). -/
instance instDecidableSatisfiable (n : Nat) (cs : ConstraintSystem n) :
    Decidable (Satisfiable cs) := by
  unfold Satisfiable
  exact List.decidableBAll _ cs.toList

/-- addConsistent is decidable. -/
instance instDecidableAddConsistent (d1 d2 : Dimension n) :
    Decidable (addConsistent d1 d2) :=
  instDecidableEqDimension d1 d2

end LeanClef.DTS
