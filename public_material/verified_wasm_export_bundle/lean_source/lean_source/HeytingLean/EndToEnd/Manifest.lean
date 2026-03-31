import HeytingLean.LambdaIR.Syntax
import HeytingLean.EndToEnd.NatFunSpec

namespace HeytingLean
namespace EndToEnd

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.EndToEnd.NatFunSpec

/-- A proven proposition bundled with a human-readable tag. -/
structure ProvenProp where
  theoremName : String
  description : String
  prop : Prop
  proof : prop

/-- Bundled metadata for a verified nat → nat example in the LambdaIR → MiniC pipeline. -/
structure Nat1Example where
  funName : String
  paramName : String
  cFunName : String
  leanName : String
  irName : String
  endToEndName : String
  leanF : Nat → Nat
  term : LambdaIR.Term [] (Ty.arrow Ty.nat Ty.nat)
  endToEndProof :
    _root_.HeytingLean.EndToEnd.EndToEndNatSpec funName paramName leanF term
  lofProps : List ProvenProp

/-- Bundled metadata for a verified nat → nat → nat example. -/
structure Nat2Example where
  funName : String
  param1 : String
  param2 : String
  cFunName : String
  leanName : String
  irName : String
  endToEndName : String
  leanF : Nat → Nat → Nat
  term :
    LambdaIR.Term [] (Ty.arrow Ty.nat (Ty.arrow Ty.nat Ty.nat))
  endToEndProof :
    _root_.HeytingLean.EndToEnd.EndToEndNat2Spec funName param1 param2 leanF
      term
  lofProps : List ProvenProp

/-- Canonical summary used by metadata emitters. -/
structure ExampleSummary where
  category : String
  name : String
  arity : Nat
  paramNames : List String
  cFunName : String
  leanName : String
  irName : String
  endToEndName : String
  provenProps : List ProvenProp

/-- Stable manifest version for downstream tooling. -/
def manifestVersion : String := "1"

/-- Stable manifest format tag for downstream tooling. -/
def manifestFormat : String := "heytinglean.examples_manifest.v1"

/-- Expected relative path (from repo root) for the examples manifest. -/
def manifestPath : String := "artifacts/examples_manifest.json"

namespace ExampleSummary

/-- Promote a unary example into a metadata summary. -/
def ofNat1 (ex : Nat1Example) : ExampleSummary :=
  { category := "nat1"
    name := ex.funName
    arity := 1
    paramNames := [ex.paramName]
    cFunName := ex.cFunName
    leanName := ex.leanName
    irName := ex.irName
    endToEndName := ex.endToEndName
    provenProps := ex.lofProps }

/-- Promote a binary example into a metadata summary. -/
def ofNat2 (ex : Nat2Example) : ExampleSummary :=
  { category := "nat2"
    name := ex.funName
    arity := 2
    paramNames := [ex.param1, ex.param2]
    cFunName := ex.cFunName
    leanName := ex.leanName
    irName := ex.irName
    endToEndName := ex.endToEndName
    provenProps := ex.lofProps }

end ExampleSummary

end EndToEnd
end HeytingLean
