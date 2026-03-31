import HeytingLean.EndToEnd.Manifest
import HeytingLean.LambdaIR.NatExamplesRegistry
import HeytingLean.LambdaIR.Nat2ExamplesRegistry

namespace HeytingLean
namespace EndToEnd
namespace Manifest

open HeytingLean.LambdaIR
open HeytingLean.EndToEnd

/-- Unary example summaries derived from the canonical registry. -/
def nat1Summaries : List ExampleSummary :=
  HeytingLean.LambdaIR.NatExamplesRegistry.examples.map
    ExampleSummary.ofNat1

/-- Binary example summaries derived from the canonical registry. -/
def nat2Summaries : List ExampleSummary :=
  HeytingLean.LambdaIR.Nat2ExamplesRegistry.examples.map
    ExampleSummary.ofNat2

/-- All example summaries in a single list, tagged by category. -/
def allExamples : List ExampleSummary :=
  nat1Summaries ++ nat2Summaries

end Manifest
end EndToEnd
end HeytingLean
