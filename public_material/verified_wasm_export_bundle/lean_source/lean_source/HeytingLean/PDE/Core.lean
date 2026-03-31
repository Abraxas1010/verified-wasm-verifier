import HeytingLean.Symbolic.Core
import HeytingLean.PDE.Symbolic.Expr

namespace HeytingLean.PDE

open HeytingLean.Symbolic

inductive PDEClass where
  | elliptic
  | parabolic
  | hyperbolic
  | variational
  deriving Repr, DecidableEq, Inhabited

inductive Domain where
  | interval (xMin xMax : Int)
  | hyperrectangle (dim : Nat) (bounds : List (Int × Int))
  | grid (dim : Nat) (shape : List Nat)
  deriving Repr, DecidableEq, Inhabited

namespace Domain

def dimension : Domain → Nat
  | .interval _ _ => 1
  | .hyperrectangle dim _ => dim
  | .grid dim _ => dim

end Domain

structure UnknownField where
  name : String
  codomain : SymSort := .real
  deriving Repr, DecidableEq, Inhabited

structure PDESpec where
  id : String
  pdeClass : PDEClass
  dimension : Nat
  domain : Domain
  unknown : UnknownField
  parameters : List SymbolDecl := []
  constraints : List Constraint := []
  scalarEquations : List HeytingLean.PDE.Symbolic.ScalarEquation := []
  vectorEquations : List HeytingLean.PDE.Symbolic.VectorEquation := []
  assumptions : List String := []
  tags : List String := []
  deriving Inhabited

namespace PDESpec

def wellFormed (spec : PDESpec) : Prop :=
  spec.dimension > 0 ∧ spec.domain.dimension = spec.dimension

def addConstraint (spec : PDESpec) (c : Constraint) : PDESpec :=
  { spec with constraints := spec.constraints.concat c }

def symbolicSystem (spec : PDESpec) : HeytingLean.PDE.Symbolic.CoupledSystem :=
  { scalarEquations := spec.scalarEquations
    vectorEquations := spec.vectorEquations
    parameters := spec.parameters.map (·.name)
    assumptions := spec.assumptions }

def hasSymbolicEquations (spec : PDESpec) : Bool :=
  !spec.scalarEquations.isEmpty || !spec.vectorEquations.isEmpty

end PDESpec

end HeytingLean.PDE
