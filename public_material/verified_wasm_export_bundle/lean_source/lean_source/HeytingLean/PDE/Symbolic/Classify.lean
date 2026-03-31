import HeytingLean.PDE.Core
import HeytingLean.PDE.Symbolic.Simp

namespace HeytingLean.PDE.Symbolic

open HeytingLean.PDE

/-- Heuristic classification of a scalar PDE from its symbolic operator profile. -/
def classifyScalarEquation (eq : ScalarEquation) : PDEClass :=
  let lhsTime := eq.lhs.timeOrder
  let rhsTime := eq.rhs.timeOrder
  let lhsSpace := eq.lhs.spatialOrder
  let rhsSpace := eq.rhs.spatialOrder
  if max lhsTime rhsTime ≥ 2 ∧ max lhsSpace rhsSpace ≥ 1 then
    .hyperbolic
  else if max lhsTime rhsTime = 1 ∧ max lhsSpace rhsSpace ≥ 2 then
    .parabolic
  else if max lhsTime rhsTime = 0 ∧ max lhsSpace rhsSpace ≥ 1 then
    .elliptic
  else
    .variational

/-- Heuristic classification of a vector PDE by reducing to the dominant orders. -/
def classifyVectorEquation (eq : VectorEquation) : PDEClass :=
  let lhsTime := eq.lhs.timeOrder
  let rhsTime := eq.rhs.timeOrder
  let lhsSpace := eq.lhs.spatialOrder
  let rhsSpace := eq.rhs.spatialOrder
  if max lhsTime rhsTime ≥ 2 ∧ max lhsSpace rhsSpace ≥ 1 then
    .hyperbolic
  else if max lhsTime rhsTime = 1 ∧ max lhsSpace rhsSpace ≥ 2 then
    .parabolic
  else if max lhsTime rhsTime = 0 ∧ max lhsSpace rhsSpace ≥ 1 then
    .elliptic
  else
    .variational

/-- Infer a PDE class from the symbolic equations attached to a spec, if any. -/
def classifySpec? (spec : PDESpec) : Option PDEClass :=
  match spec.scalarEquations, spec.vectorEquations with
  | eq :: _, _ => some (classifyScalarEquation eq)
  | [], eq :: _ => some (classifyVectorEquation eq)
  | [], [] => none

end HeytingLean.PDE.Symbolic
