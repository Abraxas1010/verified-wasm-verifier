import HeytingLean.PDE
import HeytingLean.PDE.Examples.Heat1D
import Lean.Data.Json

namespace HeytingLean.Tests.PDE

open HeytingLean.PDE.Symbolic
open HeytingLean.PDE.Examples

private def sampleScalarExpr : ScalarExpr :=
  .add (.atom "u") (.laplacian (.atom "u"))

private def sampleRealExpr : ScalarExpr :=
  .real { value := (2 : ℝ), rendered := "2" }

private def sampleZeroRealExpr : ScalarExpr :=
  ScalarExpr.real (0 : RealLiteral)

private def sampleMulExpr : ScalarExpr :=
  .mul (.atom "u") (.atom "v")

private def sampleNegExpr : ScalarExpr :=
  .neg (.atom "u")

private def sampleDivExpr : ScalarExpr :=
  .div (.atom "u") (.atom "v")

private def sampleDtExpr : ScalarExpr :=
  .dt (.atom "u")

private def sampleDttExpr : ScalarExpr :=
  .dtt (.atom "u")

private def sampleBiharmonicExpr : ScalarExpr :=
  .biharmonic (.atom "u")

private def sampleInnerExpr : ScalarExpr :=
  .inner (.atom "v") (.grad (.atom "u"))

private def sampleDivergenceExpr : ScalarExpr :=
  .divergence (.scale (.atom "kappa") (.atom "v"))

private def sampleSqrtExpr : ScalarExpr :=
  .sqrt (.atom "rho")

private def sampleExpIExpr : ScalarExpr :=
  .expI (.atom "phase")

private def sampleVectorExpr : VectorExpr :=
  .scale (.atom "kappa") (.grad (.atom "u"))

private def sampleVectorAddExpr : VectorExpr :=
  .add (.atom "v") (.grad (.atom "u"))

private def sampleVectorGradExpr : VectorExpr :=
  .grad (.atom "u")

private def sampleVectorZeroExpr : VectorExpr :=
  .zero

private def sampleVectorDtExpr : VectorExpr :=
  .dt (.atom "v")

private def sampleVectorConvectiveExpr : VectorExpr :=
  .convective (.atom "v") (.grad (.atom "u"))

private def sampleVectorNegExpr : VectorExpr :=
  .neg (.atom "v")

private def containsSub (needle haystack : String) : Bool :=
  (haystack.splitOn needle).length > 1

example : ScalarExpr.fromJson? sampleScalarExpr.toJson = some sampleScalarExpr := rfl

example : ScalarExpr.fromJson? sampleMulExpr.toJson = some sampleMulExpr := rfl

example : ScalarExpr.fromJson? sampleNegExpr.toJson = some sampleNegExpr := rfl

example : ScalarExpr.fromJson? sampleDivExpr.toJson = some sampleDivExpr := rfl

example : ScalarExpr.fromJson? sampleDtExpr.toJson = some sampleDtExpr := rfl

example : ScalarExpr.fromJson? sampleDttExpr.toJson = some sampleDttExpr := rfl

example : ScalarExpr.fromJson? sampleBiharmonicExpr.toJson = some sampleBiharmonicExpr := rfl

example : ScalarExpr.fromJson? sampleInnerExpr.toJson = some sampleInnerExpr := rfl

example : ScalarExpr.fromJson? sampleDivergenceExpr.toJson = some sampleDivergenceExpr := rfl

example : ScalarExpr.fromJson? sampleSqrtExpr.toJson = some sampleSqrtExpr := rfl

example : ScalarExpr.fromJson? sampleExpIExpr.toJson = some sampleExpIExpr := rfl

example :
    sampleZeroRealExpr.toJson =
      Lean.Json.mkObj [("tag", Lean.Json.str "real"), ("value", Lean.Json.str "0")] := rfl

example : sampleZeroRealExpr.toSMTLIB = "0" := rfl

example : sampleZeroRealExpr.toLaTeX = "0" := rfl

example :
    sampleRealExpr.toJson =
      Lean.Json.mkObj [("tag", Lean.Json.str "real"), ("value", Lean.Json.str "2")] := rfl

example : VectorExpr.fromJson? sampleVectorExpr.toJson = some sampleVectorExpr := rfl

example : VectorExpr.fromJson? sampleVectorAddExpr.toJson = some sampleVectorAddExpr := rfl

example : VectorExpr.fromJson? sampleVectorGradExpr.toJson = some sampleVectorGradExpr := rfl

example : VectorExpr.fromJson? sampleVectorZeroExpr.toJson = some sampleVectorZeroExpr := rfl

example : VectorExpr.fromJson? sampleVectorDtExpr.toJson = some sampleVectorDtExpr := rfl

example :
    VectorExpr.fromJson? sampleVectorConvectiveExpr.toJson = some sampleVectorConvectiveExpr := rfl

example : VectorExpr.fromJson? sampleVectorNegExpr.toJson = some sampleVectorNegExpr := rfl

example : sampleScalarExpr.toSMTLIB = "(+ u (laplacian u))" := rfl

example : sampleRealExpr.toSMTLIB = "2" := rfl

example : sampleScalarExpr.toLaTeX = "u + \\nabla^2 u" := rfl

example : sampleRealExpr.toLaTeX = "2" := rfl

example : sampleVectorExpr.toSMTLIB = "(scale kappa (grad u))" := rfl

example : containsSub "\"symbolic\"" (toString heat1DSymbolicJson) = true := by
  native_decide

example : containsSub "(assert (= (dt u) (* kappa (laplacian u))))" heat1DSymbolicSMTQuery = true := by
  native_decide

example : containsSub "\\partial_t u = kappa \\cdot \\nabla^2 u" heat1DSymbolicLaTeX = true := by
  native_decide

end HeytingLean.Tests.PDE
