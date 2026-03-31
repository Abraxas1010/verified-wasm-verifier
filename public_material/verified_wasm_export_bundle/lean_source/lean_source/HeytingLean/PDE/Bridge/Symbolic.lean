import HeytingLean.PDE.Core
import HeytingLean.PDE.Symbolic.Export
import HeytingLean.Symbolic.Bridge
import HeytingLean.Symbolic.SMT

namespace HeytingLean.PDE.Bridge

open HeytingLean.Symbolic
open HeytingLean.Bridge.Framework

private def classTag : HeytingLean.PDE.PDEClass → String
  | .elliptic => "elliptic"
  | .parabolic => "parabolic"
  | .hyperbolic => "hyperbolic"
  | .variational => "variational"

def toSymbolicProblem (spec : HeytingLean.PDE.PDESpec) : Problem :=
  { logic := "ALL"
    declarations := spec.parameters
    constraints := spec.constraints
    tags := ["pde", classTag spec.pdeClass, s!"dim:{spec.dimension}"] ++ spec.tags }

def toSymbolicArtifact (spec : HeytingLean.PDE.PDESpec) (prov : Provenance) : SymbolicArtifact :=
  { id := spec.id
    problem := toSymbolicProblem spec
    provenance := prov
    tags := ["pde", classTag spec.pdeClass] ++ spec.tags }

def toSymbolicSystem? (spec : HeytingLean.PDE.PDESpec) :
    Option HeytingLean.PDE.Symbolic.CoupledSystem :=
  if spec.hasSymbolicEquations then
    some spec.symbolicSystem
  else
    none

def toSMTLIB2 (spec : HeytingLean.PDE.PDESpec) : String :=
  match toSymbolicSystem? spec with
  | some sys => HeytingLean.PDE.Symbolic.CoupledSystem.toSMTLIB sys
  | none => HeytingLean.Symbolic.SMT.problemToSMTLIB2 (toSymbolicProblem spec)

def toLaTeX (spec : HeytingLean.PDE.PDESpec) : String :=
  match toSymbolicSystem? spec with
  | some sys => HeytingLean.PDE.Symbolic.CoupledSystem.toLaTeX sys
  | none =>
      "\\begin{align*}\n" ++
        "\\text{" ++ spec.id ++ "} & : \\text{" ++ classTag spec.pdeClass ++ "}\n" ++
        "\\end{align*}"

def toJson (spec : HeytingLean.PDE.PDESpec) : Lean.Json :=
  let symbolicJson :=
    match toSymbolicSystem? spec with
    | some sys => HeytingLean.PDE.Symbolic.CoupledSystem.toJson sys
    | none => Lean.Json.null
  Lean.Json.mkObj
    [ ("id", Lean.Json.str spec.id)
    , ("class", Lean.Json.str (classTag spec.pdeClass))
    , ("dimension", Lean.Json.num spec.dimension)
    , ("tags", Lean.Json.arr (spec.tags.map Lean.Json.str |>.toArray))
    , ("symbolic", symbolicJson)
    ]

end HeytingLean.PDE.Bridge
