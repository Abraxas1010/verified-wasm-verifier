import HeytingLean.Meta.LeanTT0.Rules
import HeytingLean.Meta.LeanTT0.Core

namespace HeytingLean.Meta.LeanTT0

structure TraceStep where
  rule : KernelRule
  before : ByteArray
  after  : ByteArray
  pathToRule : List ByteArray := []
-- no deriving instances needed for this lightweight trace

structure Transcript where
  steps : List TraceStep
  initialDigest : ByteArray
  finalDigest   : ByteArray
-- no deriving instances needed for this lightweight trace

def runWithTrace (fuel : Nat) (t : Tm) : Transcript :=
  let init := digestTerm t
  let rec loop (n : Nat) (cur : Tm) (acc : List TraceStep) : (Tm × List TraceStep) :=
    match n with
    | 0 => (cur, acc)
    | n+1 =>
      match applyRule KernelRule.BetaLamApp cur with
      | some t' =>
          let before := digestTerm cur; let after := digestTerm t'
          let step : TraceStep := { rule := .BetaLamApp, before, after, pathToRule := [] }
          loop n t' (acc.concat step)
      | none =>
        match applyRule KernelRule.DeltaPrimNatAdd cur with
        | some t' =>
            let before := digestTerm cur; let after := digestTerm t'
            let step : TraceStep := { rule := .DeltaPrimNatAdd, before, after, pathToRule := [] }
            loop n t' (acc.concat step)
        | none => (cur, acc)
  let (t', steps) := loop fuel t []
  { steps, initialDigest := init, finalDigest := digestTerm t' }

end HeytingLean.Meta.LeanTT0
