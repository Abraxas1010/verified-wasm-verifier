import HeytingLean.PDE.Bridge.Symbolic
import HeytingLean.PDE.Certificates.SchauderGate

namespace HeytingLean.PDE.Examples

open HeytingLean.Symbolic
open HeytingLean.Bridge.Framework
open HeytingLean.PDE.Symbolic

private def uPrev : SymbolDecl := { name := "u_prev", sort := .real }
private def uNext : SymbolDecl := { name := "u_next", sort := .real }
private def lapTerm : Expr := Expr.app "laplace1d" [Expr.var uPrev] .real
private def rhsTerm : Expr := Expr.app "+" [Expr.var uPrev, Expr.app "*" [Expr.realLit "r", lapTerm] .real] .real

private def heatConstraint : Constraint :=
  { lhs := Expr.var uNext, rhs := rhsTerm, rel := .eq }

def heatSymbolicUnknown : ScalarField := { name := "u" }

def heatSymbolicEquation : ScalarEquation :=
  { lhs := .dt heatSymbolicUnknown.expr
    rhs := .mul (.atom "kappa") (.laplacian heatSymbolicUnknown.expr) }

def heat1DSpec : HeytingLean.PDE.PDESpec :=
  { id := "pde.heat1d.step"
    pdeClass := .parabolic
    dimension := 1
    domain := .interval 0 1
    unknown := { name := "u", codomain := .real }
    parameters := [uPrev, uNext, { name := "r", sort := .real }]
    constraints := [heatConstraint]
    scalarEquations := [heatSymbolicEquation]
    assumptions := ["0 < r", "r <= 1/2", "Dirichlet boundary"]
    tags := ["heat1d", "finite-difference"] }

def sampleProvenance : Provenance :=
  { sourceSystem := "HeytingLean"
    sourceRef := "PDE.Examples.Heat1D"
    trustLevel := .verified
    translator := "native"
    timestamp := "2026-02-06" }

def heat1DArtifact : SymbolicArtifact :=
  HeytingLean.PDE.Bridge.toSymbolicArtifact heat1DSpec sampleProvenance

def heat1DSMTQuery : String := heat1DArtifact.toSMTLIB2

def heat1DSymbolicSMTQuery : String :=
  HeytingLean.PDE.Bridge.toSMTLIB2 heat1DSpec

def heat1DSymbolicLaTeX : String :=
  HeytingLean.PDE.Bridge.toLaTeX heat1DSpec

def heat1DSymbolicJson : Lean.Json :=
  HeytingLean.PDE.Bridge.toJson heat1DSpec

example : heat1DSpec.dimension = 1 := rfl

example : heat1DSpec.wellFormed := by
  constructor
  · decide
  · rfl

end HeytingLean.PDE.Examples
