import HeytingLean.LoF.Combinators.Differential.Loss
import HeytingLean.LoF.Combinators.Differential.NucleusDifferential

/-!
# Differential combinators: gradient descent (coordinate, finite basis)

This file provides a pragmatic optimization loop for the DiLL-inspired experiments:

* A noncomputable library API on `FormalSum K` (suitable for reasoning, not executables).
* A fully computable runtime API on `Compute.FSum` with `Rat` coefficients.

Both loops implement *coordinate gradient descent* over a finite list of parameter terms.
-/

noncomputable section

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Differential

open scoped BigOperators

/-! ## Library layer: `FormalSum` gradient descent -/

structure GDConfig (K : Type*) [Zero K] [One K] where
  learningRate : K := 1
  iterations : Nat := 100
  regularization : K := 0
  params : List LoF.Comb := []

structure GDState (K : Type*) [Zero K] where
  iteration : Nat
  currentProof : FormalSum K
  currentLoss : K
  lossHistory : List K

namespace GDConfig

variable {K : Type*} [Zero K] [One K]

noncomputable def default : GDConfig K :=
  { learningRate := 1
    iterations := 100
    regularization := 0
    params := [] }

end GDConfig

namespace GD

variable {K : Type*} [CommRing K]

noncomputable def projectToParams (params : List LoF.Comb) (w : FormalSum K) : FormalSum K :=
  if params = [] then
    w
  else
    let keep : Finset LoF.Comb := params.toFinset
    w.filter (fun t => t ∈ keep)

noncomputable def gradientStep (config : GDConfig K) (examples : List (Loss.IOExample K)) (w : FormalSum K) :
    FormalSum K :=
  let g := Loss.totalGrad (K := K) config.params config.regularization w examples
  projectToParams (K := K) config.params (w - config.learningRate • g)

noncomputable def gradientDescentLoop (config : GDConfig K) (examples : List (Loss.IOExample K))
    (initial : FormalSum K) : GDState K :=
  let rec go : Nat → Nat → FormalSum K → List K → GDState K
    | 0, iter, w, hist =>
        let l := Loss.totalLoss (K := K) config.regularization w examples
        { iteration := iter, currentProof := w, currentLoss := l, lossHistory := hist.reverse }
    | Nat.succ fuel, iter, w, hist =>
        let l := Loss.totalLoss (K := K) config.regularization w examples
        let w' := gradientStep (K := K) config examples w
        go fuel (iter + 1) w' (l :: hist)
  go config.iterations 0 initial []

noncomputable def bestTermSupport? (w : FormalSum K) : Option LoF.Comb :=
  w.support.toList.head?

noncomputable def synthesize (examples : List (Loss.IOExample K))
    (config : GDConfig K := GDConfig.default (K := K)) :
    GDState K × FormalSum K :=
  let initial : FormalSum K := single (K := K) LoF.Comb.I
  let st := gradientDescentLoop (K := K) config examples initial
  let best := (bestTermSupport? (K := K) st.currentProof).getD LoF.Comb.K
  (st, single (K := K) best)

noncomputable def synthesizeStable (R : LoF.Comb → LoF.Comb) (examples : List (Loss.IOExample K))
    (config : GDConfig K := GDConfig.default (K := K)) : GDState K × FormalSum K :=
  let (st, proof) := synthesize (K := K) examples config
  (st, FormalSum.projectToFixed (K := K) R proof)

end GD

/-! ## Runtime layer: `Compute` gradient descent -/

namespace Compute

open HeytingLean.LoF.Combinators.Differential.Compute

structure GDConfig where
  learningRate : Rat := (1 : Rat) / 5
  iterations : Nat := 20
  regularization : Rat := 0
  params : List Comb := []

namespace GDConfig

def default : GDConfig :=
  { learningRate := (1 : Rat) / 5
    iterations := 20
    regularization := 0
    params := [] }

end GDConfig

structure GDState where
  iteration : Nat
  currentWeights : FSum
  currentLoss : Rat
  lossHistory : List Rat

def absRat (r : Rat) : Rat :=
  if r < 0 then -r else r

def projectToParams (params : List Comb) (w : FSum) : FSum :=
  if params = [] then
    w
  else
    w.foldl (fun acc tc => if tc.1 ∈ params then addTerm tc.1 tc.2 acc else acc) []

def gradientStep (config : GDConfig) (examples : List IOExample) (w : FSum) : FSum :=
  let g := totalGrad config.params config.regularization w examples
  projectToParams config.params (sub w (smul config.learningRate g))

def gradientDescentLoop (config : GDConfig) (examples : List IOExample) (initial : FSum := []) : GDState :=
  let rec go : Nat → Nat → FSum → List Rat → GDState
    | 0, iter, w, hist =>
        let l := totalLoss config.regularization w examples
        { iteration := iter, currentWeights := w, currentLoss := l, lossHistory := hist.reverse }
    | Nat.succ fuel, iter, w, hist =>
        let l := totalLoss config.regularization w examples
        let w' := gradientStep config examples w
        go fuel (iter + 1) w' (l :: hist)
  go config.iterations 0 initial []

def bestTermByAbs? (w : FSum) : Option Comb :=
  let rec go : List (Comb × Rat) → Option (Comb × Rat) → Option (Comb × Rat)
    | [], best => best
    | (t, c) :: rest, none => go rest (some (t, c))
    | (t, c) :: rest, some (tb, cb) =>
        if absRat c ≤ absRat cb then go rest (some (tb, cb)) else go rest (some (t, c))
  (go w none).map (fun tc => tc.1)

def synthesize (examples : List IOExample) (config : GDConfig := GDConfig.default) : GDState × Option Comb :=
  let st := gradientDescentLoop config examples []
  (st, bestTermByAbs? st.currentWeights)

end Compute

end Differential
end Combinators
end LoF
end HeytingLean
