import HeytingLean.ATP.DifferentiableATP.CoreOps
import HeytingLean.ATP.DifferentiableATP.GoalEncoder
import HeytingLean.ATP.DifferentiableATP.RetractedGD
import HeytingLean.ATP.DifferentiableATP.TypeLoss
import HeytingLean.ATP.LaneChanging

/-!
# ATP.DifferentiableATP.GradientProbe

Short gradient probes for lens selection in differentiable ATP.
-/

namespace HeytingLean
namespace ATP
namespace DifferentiableATP

open HeytingLean.Embeddings
open HeytingLean.LoF
open HeytingLean.LoF.Combinators.Differential
open HeytingLean.LoF.Combinators.Differential.Compute

inductive ProbeGDMode where
  | projected
  | retracted
  deriving Repr, DecidableEq

structure ProbeConfig where
  probeSteps : Nat := 5
  probeBudget : Nat := 3
  probeThreshold : Rat := 0
  psrWeight : Rat := 1
  ioWeight : Rat := 1
  deriving Repr

structure ProbeResult where
  lens : LensID
  initialPSR : Rat
  finalPSR : Rat
  psrDescentRate : Rat
  initialIOLoss : Rat
  finalIOLoss : Rat
  ioDescentRate : Rat
  score : Rat
  finalWeights : FSum
  deriving Repr

def probeScore (cfg : ProbeConfig) (p : ProbeResult) : Rat :=
  cfg.psrWeight * p.psrDescentRate + cfg.ioWeight * p.ioDescentRate

def candidateLenses (current : LensID) (budget : Nat) : List LensID :=
  let rec go : Nat → LensID → List LensID
    | 0, _ => []
    | Nat.succ k, lens =>
        let nxt := nextLens lens
        nxt :: go k nxt
  (current :: go (min budget 6) current).eraseDups

private def probeGDConfig (regularization : Rat) (steps : Nat) (basis : List Comb) : GDConfig :=
  {
    learningRate := (1 : Rat) / 5
    iterations := steps
    regularization := regularization
    params := if basis.isEmpty then [.K, .S, .Y] else basis
  }

private def probeStepFn
    (mode : ProbeGDMode)
    (gdCfg : GDConfig)
    (examples : List IOExample) : FSum → FSum :=
  match mode with
  | .projected => gradientStepProjected gdCfg examples
  | .retracted => retractedGradientStep gdCfg examples

def runProbe
    (goal : String)
    (lens : LensID)
    (carry : Option FSum)
    (cfg : ProbeConfig)
    (regularization : Rat := 0)
    (mode : ProbeGDMode := .retracted)
    (contextHints : List String := []) : ProbeResult :=
  let encoded := encodeGoal goal lens contextHints
  let initial :=
    match carry with
    | some w => add encoded.initial w
    | none => encoded.initial
  let w0 := projectToFixedWeights nucleusR initial
  let io0 := Compute.totalLoss regularization w0 encoded.examples
  let psr0 := psrLoss nucleusR w0
  let steps := cfg.probeSteps
  let gdCfg := probeGDConfig regularization steps encoded.basis
  let stepFn := probeStepFn mode gdCfg encoded.examples
  let wN := Nat.iterate stepFn steps w0
  let ioN := Compute.totalLoss regularization wN encoded.examples
  let psrN := psrLoss nucleusR wN
  let stepsRat : Rat := (Int.ofNat steps : Rat)
  let psrRate := if steps = 0 then 0 else (psr0 - psrN) / stepsRat
  let ioRate := if steps = 0 then 0 else (io0 - ioN) / stepsRat
  let p : ProbeResult :=
    {
      lens := lens
      initialPSR := psr0
      finalPSR := psrN
      psrDescentRate := psrRate
      initialIOLoss := io0
      finalIOLoss := ioN
      ioDescentRate := ioRate
      score := 0
      finalWeights := wN
    }
  { p with score := probeScore cfg p }

private def bestProbe? : List ProbeResult → Option ProbeResult
  | [] => none
  | p :: rest =>
      some <| rest.foldl (fun best cur => if cur.score > best.score then cur else best) p

def selectLaneByGradient
    (goal : String)
    (current : LensID)
    (carry : Option FSum)
    (cfg : ProbeConfig)
    (regularization : Rat := 0)
    (mode : ProbeGDMode := .retracted)
    (contextHints : List String := []) : LaneDecision × List ProbeResult :=
  let probes :=
    (candidateLenses current cfg.probeBudget).map
      (fun lens => runProbe goal lens carry cfg regularization mode contextHints)
  match bestProbe? probes with
  | none => (.stay, [])
  | some best =>
      if best.lens = current then
        (.stay, probes)
      else if best.psrDescentRate > cfg.probeThreshold then
        (.switch best.lens, probes)
      else
        (.stay, probes)

end DifferentiableATP
end ATP
end HeytingLean
