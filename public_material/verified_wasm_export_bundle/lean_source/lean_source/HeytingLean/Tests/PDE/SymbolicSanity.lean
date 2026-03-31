import HeytingLean.PDE
import HeytingLean.ProgramCalculus.PDEDSL

namespace HeytingLean.Tests.PDE

open HeytingLean.PDE.Examples
open HeytingLean.PDE.Symbolic

private def containsSub (needle haystack : String) : Bool :=
  (haystack.splitOn needle).length > 1

private def nestedScalarDt : ScalarExpr :=
  .dt (.dt (.atom "u"))

private def nestedVectorDt : VectorExpr :=
  .dt (.dt (.atom "v"))

private def firstOrderVectorEquation : VectorEquation :=
  { lhs := .dt (.atom "v")
    rhs := .grad (.atom "p") }

example : heat1DSpec.dimension = 1 := rfl

example : (HeytingLean.ProgramCalculus.compileToy heat1DSpec).isSome := by
  simp [HeytingLean.ProgramCalculus.compileToy, heat1DSpec]

example : heat1DSMTQuery.length > 0 := by
  decide

example : classifyScalarEquation heatSymbolicEquation = .parabolic := by
  native_decide

example : nestedScalarDt.timeOrder = 2 := rfl

example : nestedScalarDt.diffOrder = 2 := rfl

example : nestedVectorDt.timeOrder = 2 := rfl

example : nestedVectorDt.diffOrder = 2 := rfl

example : classifyVectorEquation firstOrderVectorEquation = .variational := by
  native_decide

example : heat1DSymbolicSMTQuery.length > 0 := by
  decide

example : containsSub "\\nabla^2" heat1DSymbolicLaTeX = true := by
  native_decide

end HeytingLean.Tests.PDE
