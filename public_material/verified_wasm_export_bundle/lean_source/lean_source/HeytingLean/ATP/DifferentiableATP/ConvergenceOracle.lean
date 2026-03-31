import HeytingLean.LoF.Combinators.Differential.GradientDescent
import HeytingLean.ATP.DifferentiableATP.Util

/-!
# ATP.DifferentiableATP.ConvergenceOracle

Loss-history based convergence and stuckness checks for the differentiable ATP lane.
-/

namespace HeytingLean
namespace ATP
namespace DifferentiableATP

open HeytingLean.LoF.Combinators.Differential
open HeytingLean.LoF.Combinators.Differential.Compute

namespace ConvergenceOracle

structure Config where
  lossThreshold : Rat := (1 : Rat) / 100
  plateauWindow : Nat := 4
  plateauEpsilon : Rat := (1 : Rat) / 1000
  psrThreshold : Rat := (1 : Rat) / 1000
  maxIterations : Nat := 24
  annealStart : Rat := 1
  annealEnd : Rat := (1 : Rat) / 5
  deriving Repr

structure Verdict where
  converged : Bool
  stuck : Bool
  reason : String
  temperature : Rat
  monotoneNonIncreasing : Bool
  monotonicityScore : Rat
  plateauSpan : Rat
  psrLoss : Rat
  psrConverged : Bool
  dialecticLoss : Rat
  deriving Repr

private def lastN (xs : List Rat) (n : Nat) : List Rat :=
  (xs.reverse.take n).reverse

private def minMax (xs : List Rat) : Option (Rat × Rat) :=
  match xs with
  | [] => none
  | x :: rest =>
      some <| rest.foldl
        (fun (acc : Rat × Rat) v =>
          let mn := if v < acc.1 then v else acc.1
          let mx := if acc.2 < v then v else acc.2
          (mn, mx))
        (x, x)

private def isNonIncreasing : List Rat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => b <= a && isNonIncreasing (b :: rest)

/-- Fraction of adjacent pairs where loss is non-increasing (`b <= a`). -/
def monotonicityScore (hist : List Rat) : Rat :=
  match hist with
  | [] | [_] => 1
  | _ =>
      let pairs := hist.zip hist.tail
      let nonInc : Nat :=
        pairs.foldl
          (fun acc p =>
            if p.2 <= p.1 then acc + 1 else acc)
          0
      (Int.ofNat nonInc : Rat) / (Int.ofNat pairs.length : Rat)

private def plateauSpan (hist : List Rat) (window : Nat) : Rat :=
  let sample := lastN hist (max 1 window)
  match minMax sample with
  | none => 0
  | some (mn, mx) => absRat (mx - mn)

def temperatureAt (cfg : Config) (iteration : Nat) : Rat :=
  let maxIter := max 1 cfg.maxIterations
  let step := cfg.annealStart - cfg.annealEnd
  let frac : Rat := (Int.ofNat (min iteration maxIter) : Rat) / (Int.ofNat maxIter : Rat)
  let t := cfg.annealStart - (step * frac)
  if t <= 0 then cfg.annealEnd else t

def evaluate (cfg : Config) (st : GDState) (psrCurrent : Rat := 0) (dialecticCurrent : Rat := 0) : Verdict :=
  let hist := st.lossHistory
  let span := plateauSpan hist cfg.plateauWindow
  let monoScore := monotonicityScore hist
  let reached := st.currentLoss <= cfg.lossThreshold
  let psrConverged := psrCurrent <= cfg.psrThreshold
  let budget := st.iteration >= cfg.maxIterations
  let plateau := span <= cfg.plateauEpsilon
  let converged := reached && psrConverged
  let stuck := (!converged) && (budget || plateau)
  let reason :=
    if converged then
      "loss_and_psr_below_threshold"
    else if reached && !psrConverged then
      "psr_not_converged"
    else if plateau then
      "loss_plateau"
    else if budget then
      "iteration_budget_exhausted"
    else
      "in_progress"
  {
    converged := converged
    stuck := stuck
    reason := reason
    temperature := temperatureAt cfg st.iteration
    monotoneNonIncreasing := isNonIncreasing hist
    monotonicityScore := monoScore
    plateauSpan := span
    psrLoss := psrCurrent
    psrConverged := psrConverged
    dialecticLoss := dialecticCurrent
  }

end ConvergenceOracle

end DifferentiableATP
end ATP
end HeytingLean
