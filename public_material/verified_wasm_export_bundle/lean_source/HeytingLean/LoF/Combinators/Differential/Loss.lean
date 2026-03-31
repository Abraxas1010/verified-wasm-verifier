import HeytingLean.LoF.Combinators.Differential.LinearComb
import HeytingLean.LoF.Combinators.Differential.Compute

/-!
# Differential combinators: loss functions (coordinate gradients)

The DiLL inspiration treats proofs/terms as “vectorized” objects and differentiates through their
combinator structure. For a runnable synthesis loop we additionally need a *computable* loss and
gradient. In this codebase we provide:

* Library layer (`FormalSum K`): noncomputable coordinate gradients parameterized by a finite basis.
* Runtime layer (`Compute.FSum`): fully computable `Rat` coordinate gradients used by executables.

The coordinate-gradient approach matches the demo in `HeytingLean.CLI.DifferentialSKYDemoMain`:
we only learn coefficients for a fixed list of “parameter terms” (a finite basis).
-/

noncomputable section

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Differential

open scoped BigOperators

/-! ## Library layer: `FormalSum` losses -/

namespace Loss

structure IOExample (K : Type*) [Zero K] where
  input : FormalSum K
  expected : FormalSum K

section FormalSumLoss

variable {K : Type*} [CommRing K]

def error (w : FormalSum K) (ex : IOExample K) : FormalSum K :=
  FormalSum.app (K := K) w ex.input - ex.expected

def singleIOLoss (w : FormalSum K) (ex : IOExample K) : K :=
  FormalSum.l2NormSq (K := K) (error (K := K) w ex)

def ioLoss (w : FormalSum K) (examples : List (IOExample K)) : K :=
  examples.foldl (fun acc ex => acc + singleIOLoss (K := K) w ex) 0

/-- L2 regularization (squared norm). -/
def l2Reg (w : FormalSum K) : K :=
  FormalSum.l2NormSq (K := K) w

def totalLoss (regularization : K) (w : FormalSum K) (examples : List (IOExample K)) : K :=
  ioLoss (K := K) w examples + regularization * l2Reg (K := K) w

/-- Coordinate gradient of `singleIOLoss` over a finite list of basis terms. -/
def ioLossCoordGrad (params : List LoF.Comb) (w : FormalSum K) (ex : IOExample K) : FormalSum K :=
  let err := error (K := K) w ex
  params.foldl
    (fun g t =>
      let phi := FormalSum.app (K := K) (single (K := K) t) ex.input
      let gc : K := (2 : K) * FormalSum.dot (K := K) err phi
      g + gc • single (K := K) t)
    0

def ioLossCoordGradDataset (params : List LoF.Comb) (w : FormalSum K) (examples : List (IOExample K)) :
    FormalSum K :=
  examples.foldl (fun g ex => g + ioLossCoordGrad (K := K) params w ex) 0

/-!
`ioLossGradient` is a convenience wrapper: it chooses the current support as the coordinate basis.
This is not a “true” Fréchet gradient on an infinite-dimensional space; it is the most convenient
noncomputable finite approximation compatible with the rest of this file.
-/
def ioLossGradient (w : FormalSum K) (examples : List (IOExample K)) : FormalSum K :=
  ioLossCoordGradDataset (K := K) (w.support.toList) w examples

def totalGrad (params : List LoF.Comb) (regularization : K) (w : FormalSum K) (examples : List (IOExample K)) :
    FormalSum K :=
  ioLossCoordGradDataset (K := K) params w examples + ((2 : K) * regularization) • w

/-! ### Optional extensions (placeholders for the aspirational spec) -/

/-- A placeholder “type loss” hook: currently zero (no type constraints enforced here). -/
def typeLoss (_w _targetType : FormalSum K) : K :=
  0

/-- A simple complexity proxy: L2 regularization. -/
def complexityLoss (w : FormalSum K) : K :=
  l2Reg (K := K) w

end FormalSumLoss

end Loss

/-! ## Runtime layer: `Compute.FSum` losses -/

namespace Compute

open HeytingLean.LoF.Combinators.Differential.Compute

structure IOExample where
  input : FSum
  expected : FSum

def error (w : FSum) (ex : IOExample) : FSum :=
  sub (app w ex.input) ex.expected

def singleIOLoss (w : FSum) (ex : IOExample) : Rat :=
  l2NormSq (error w ex)

def ioLoss (w : FSum) (examples : List IOExample) : Rat :=
  examples.foldl (fun acc ex => acc + singleIOLoss w ex) 0

def l2Reg (w : FSum) : Rat :=
  l2NormSq w

def totalLoss (regularization : Rat) (w : FSum) (examples : List IOExample) : Rat :=
  ioLoss w examples + regularization * l2Reg w

/-- Coordinate gradient of `singleIOLoss` over a finite list of basis terms. -/
def ioLossCoordGrad (params : List Comb) (w : FSum) (ex : IOExample) : FSum :=
  let err := error w ex
  params.foldl
    (fun g t =>
      let phi := app (single t) ex.input
      let gc := (2 : Rat) * dot err phi
      add g (single t gc))
    []

def ioLossCoordGradDataset (params : List Comb) (w : FSum) (examples : List IOExample) : FSum :=
  examples.foldl (fun g ex => add g (ioLossCoordGrad params w ex)) []

def paramsOfWeights (w : FSum) : List Comb :=
  (w.map (fun tc => tc.1)).eraseDups

def ioLossGradient (w : FSum) (examples : List IOExample) : FSum :=
  ioLossCoordGradDataset (paramsOfWeights w) w examples

def totalGrad (params : List Comb) (regularization : Rat) (w : FSum) (examples : List IOExample) : FSum :=
  add (ioLossCoordGradDataset params w examples) (smul ((2 : Rat) * regularization) w)

/-- A placeholder “type loss” hook: currently zero (no type constraints enforced here). -/
def typeLoss (_w _targetType : FSum) : Rat :=
  0

/-- A simple complexity proxy: L2 regularization. -/
def complexityLoss (w : FSum) : Rat :=
  l2Reg w

/-- Soft L2 distance using the structural kernel. -/
def softL2Diff (depth : Nat) (a b : FSum) : Rat :=
  let diff := sub a b
  l2NormSq (liftFeatures depth diff)

theorem softL2Diff_nonneg (depth : Nat) (a b : FSum) : 0 ≤ softL2Diff depth a b := by
  unfold softL2Diff
  exact l2NormSq_nonneg _

/-- Step-based IO loss over the forward map `stepsIter fuel (app state input)`. -/
def stepIOLoss (depth fuel : Nat) (state : FSum) (ex : IOExample) : Rat :=
  softL2Diff depth (stepsIter fuel (app state ex.input)) ex.expected

/-- Dataset loss for step-based forward map. -/
def stepIOLossDataset (depth fuel : Nat) (state : FSum) (examples : List IOExample) : Rat :=
  examples.foldl (fun acc ex => acc + stepIOLoss depth fuel state ex) 0

/-- Finite-difference coordinate gradient for `stepIOLossDataset`. -/
def stepIOCoordGrad
    (depth fuel : Nat)
    (params : List Comb)
    (state : FSum)
    (examples : List IOExample) : FSum :=
  let eps : Rat := (1 : Rat) / 1000
  let loss0 := stepIOLossDataset depth fuel state examples
  params.foldl
    (fun g t =>
      let perturbed := add state (single t eps)
      let loss1 := stepIOLossDataset depth fuel perturbed examples
      let grad := (loss1 - loss0) / eps
      add g (single t grad))
    []

/-- Exact directional derivative for one parameter and one example.
    Uses linearity of `app` and `stepsIter` with chain rule under `softDot`. -/
def exactStepIOCoordGradOne
    (depth fuel : Nat)
    (state : FSum)
    (t : Comb)
    (ex : IOExample) : Rat :=
  let forward := stepsIter fuel (app state ex.input)
  let err := sub forward ex.expected
  let direction := stepsIter fuel (app (single t 1) ex.input)
  (2 : Rat) * softDot depth err direction

/-- Exact coordinate gradient for `stepIOLossDataset` (Issue B fix). -/
def exactStepIOCoordGrad
    (depth fuel : Nat)
    (params : List Comb)
    (state : FSum)
    (examples : List IOExample) : FSum :=
  params.foldl
    (fun g t =>
      let grad :=
        examples.foldl
          (fun acc ex => acc + exactStepIOCoordGradOne depth fuel state t ex)
          0
      add g (single t grad))
    []

/-- Diagnostic gradient norm. -/
def gradientNorm (grad : FSum) : Rat :=
  l2NormSq grad

/-- Complexity proxy: weighted absolute coefficient sum by term size. -/
def simplicityLoss (v : FSum) : Rat :=
  v.foldl
    (fun acc tc =>
      let sizeRat : Rat := (Int.ofNat (combSize tc.1) : Rat)
      let mag := if tc.2 < 0 then -tc.2 else tc.2
      acc + sizeRat * mag)
    0

/-- Subgradient-style sign used for L1-like simplicity penalty. -/
def signRat (r : Rat) : Rat :=
  if r < 0 then -1 else if r = 0 then 0 else 1

/-- Coordinate gradient for `simplicityLoss` over a finite parameter set. -/
def simplicityCoordGrad (params : List Comb) (state : FSum) : FSum :=
  let wn := normalize state
  params.foldl
    (fun g t =>
      let c := coeff t wn
      let sizeRat : Rat := (Int.ofNat (combSize t) : Rat)
      let grad := sizeRat * signRat c
      add g (single t grad))
    []

/-- Step IO loss with explicit simplicity regularization. -/
def combinedStepIOLoss
    (depth fuel : Nat)
    (simplicityWeight : Rat)
    (state : FSum)
    (examples : List IOExample) : Rat :=
  stepIOLossDataset depth fuel state examples + simplicityWeight * simplicityLoss state

/-- Coefficient overlap between reachability expansion and target.
    Measures how much of `b`'s support is "reachable" from `a` within `fuel` steps.
    Returns a value in [0, ∞); higher means more overlap. -/
def reachOverlap (fuel : Nat) (a b : FSum) : Rat :=
  let expanded := reachabilityBounded fuel a
  let expN := normalize expanded
  let bN := normalize b
  bN.foldl (fun acc tc =>
    let c := coeff tc.1 expN
    let mag := if c < 0 then -c else c
    acc + mag) 0

/-- Reachability loss: 1 - normalized overlap, clamped to [0, 1].
    Returns 0 when `b` is fully reachable from `a`; 1 when no overlap. -/
def reachLoss (fuel : Nat) (a b : FSum) : Rat :=
  let overlap := reachOverlap fuel a b
  let bNorm := l2NormSq (normalize b)
  if bNorm ≤ 0 then 0
  else
    let ratio := overlap / (bNorm + 1)
    let clamped := if ratio > 1 then 1 else ratio
    1 - clamped

/-- Reachability loss over a dataset of IO examples. -/
def reachLossDataset (fuel : Nat) (state : FSum) (examples : List IOExample) : Rat :=
  examples.foldl (fun acc ex =>
    acc + reachLoss fuel (app state ex.input) ex.expected) 0

/-- Finite-difference coordinate gradient of reachability loss. -/
def reachCoordGrad
    (fuel : Nat)
    (params : List Comb)
    (state : FSum)
    (examples : List IOExample) : FSum :=
  let eps : Rat := (1 : Rat) / 200
  let loss0 := reachLossDataset fuel state examples
  params.foldl
    (fun g t =>
      let perturbed := add state (single t eps)
      let loss1 := reachLossDataset fuel perturbed examples
      let grad := truncRat ((loss1 - loss0) / eps)
      add g (single t grad))
    []

end Compute

end Differential
end Combinators
end LoF
end HeytingLean
