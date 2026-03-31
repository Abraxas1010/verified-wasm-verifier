import Mathlib.Data.Real.Basic

namespace HeytingLean.PDE.Symbolic

/-! # Symbolic PDE Expressions

Domain-agnostic symbolic expression types for PDE specifications and export.
-/

/-- A symbolic real literal with an optional textual rendering for export surfaces. -/
structure RealLiteral where
  value : ℝ
  rendered : String := "real"

/-- Coercion for Lean-internal symbolic construction.
This path is not JSON round-trip safe unless `rendered` is set explicitly. -/
instance : Coe ℝ RealLiteral := ⟨fun value => { value := value }⟩
instance : Coe RealLiteral ℝ := ⟨fun lit => lit.value⟩

instance instOfNatRealLiteral (n : Nat) : OfNat RealLiteral n where
  ofNat := { value := (n : ℝ), rendered := toString n }

instance : Neg RealLiteral where
  neg lit := { value := -lit.value, rendered := "-" ++ lit.rendered }

instance : HPow RealLiteral Nat RealLiteral where
  hPow lit n := { value := lit.value ^ n, rendered := lit.rendered ++ "^" ++ toString n }

mutual

/-- Symbolic scalar expressions with differential operators. -/
inductive ScalarExpr where
  | atom (name : String)
  | real (value : RealLiteral)
  | add (lhs rhs : ScalarExpr)
  | mul (lhs rhs : ScalarExpr)
  | div (lhs rhs : ScalarExpr)
  | neg (expr : ScalarExpr)
  | sqrt (expr : ScalarExpr)
  | expI (phase : ScalarExpr)
  | dt (expr : ScalarExpr)
  | dtt (expr : ScalarExpr)
  | laplacian (expr : ScalarExpr)
  | biharmonic (expr : ScalarExpr)
  | divergence (expr : VectorExpr)
  | inner (lhs rhs : VectorExpr)

/-- Symbolic vector expressions with differential operators. -/
inductive VectorExpr where
  | atom (name : String)
  | zero
  | add (lhs rhs : VectorExpr)
  | scale (coeff : ScalarExpr) (expr : VectorExpr)
  | grad (expr : ScalarExpr)
  | dt (expr : VectorExpr)
  | convective (velocity transport : VectorExpr)
  | neg (expr : VectorExpr)

end

instance : Inhabited ScalarExpr := ⟨.atom "0"⟩
instance : Inhabited VectorExpr := ⟨.zero⟩

/-- Scalar symbolic equations. -/
structure ScalarEquation where
  lhs : ScalarExpr
  rhs : ScalarExpr

instance : Inhabited ScalarEquation := ⟨{ lhs := .atom "0", rhs := .atom "0" }⟩

/-- Vector symbolic equations. -/
structure VectorEquation where
  lhs : VectorExpr
  rhs : VectorExpr

instance : Inhabited VectorEquation := ⟨{ lhs := .zero, rhs := .zero }⟩

/-- A symbolic real-valued field. -/
structure ScalarField where
  name : String
  smooth : Bool := true
  deriving Repr, DecidableEq, Inhabited

/-- A symbolic vector field. -/
structure VectorField where
  name : String
  smooth : Bool := true
  deriving Repr, DecidableEq, Inhabited

namespace ScalarField

def expr (f : ScalarField) : ScalarExpr :=
  .atom f.name

end ScalarField

namespace VectorField

def expr (f : VectorField) : VectorExpr :=
  .atom f.name

end VectorField

namespace ScalarExpr

def zero : ScalarExpr :=
  .real 0

def sub (lhs rhs : ScalarExpr) : ScalarExpr :=
  .add lhs (.neg rhs)

end ScalarExpr

namespace VectorExpr

def sub (lhs rhs : VectorExpr) : VectorExpr :=
  .add lhs (.neg rhs)

end VectorExpr

/-- A coupled symbolic PDE system. -/
structure CoupledSystem where
  scalarEquations : List ScalarEquation := []
  vectorEquations : List VectorEquation := []
  parameters : List String := []
  assumptions : List String := []
  deriving Inhabited

end HeytingLean.PDE.Symbolic
