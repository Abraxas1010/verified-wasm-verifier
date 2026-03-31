import HeytingLean.PDE.Examples.Heat1D

namespace HeytingLean.Tests.PDE

open HeytingLean.PDE.Examples

private def containsSub (needle haystack : String) : Bool :=
  (haystack.splitOn needle).length > 1

def heatProblemInferred : HeytingLean.Symbolic.Problem :=
  (HeytingLean.PDE.Bridge.toSymbolicProblem heat1DSpec).withInferredDecls

example : heatProblemInferred.declarations.length = 3 := by native_decide

example : containsSub "(set-logic ALL)" heat1DSMTQuery = true := by native_decide

example : containsSub "(declare-const u_prev Real)" heat1DSMTQuery = true := by native_decide

example : containsSub "(declare-const u_next Real)" heat1DSMTQuery = true := by native_decide

example : containsSub "(declare-const r Real)" heat1DSMTQuery = true := by native_decide

example : containsSub "(declare-fun laplace1d (Real) Real)" heat1DSMTQuery = true := by native_decide

example : heat1DArtifact.toTPTPFOF.length = heat1DSpec.constraints.length := by rfl

end HeytingLean.Tests.PDE
