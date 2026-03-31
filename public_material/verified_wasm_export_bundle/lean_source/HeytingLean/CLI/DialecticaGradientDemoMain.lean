import HeytingLean.LoF.Combinators.Differential.GradientDescent
import Lean

/-!
# CLI.DialecticaGradientDemoMain

An **empirical-first** validation harness for the “Differentiable Dialectica” idea.

We treat a tiny Dialectica-style witness/challenge game as:
- witness: a finite weight vector `w : Compute.FSum` over a fixed parameter basis,
- challenge: a finite dataset of inputs,
- relation: `app w input ≈ expected`,
and compare:
1) gradient descent (coordinate gradients),
2) exhaustive grid search (objective optimum on a restricted discrete space),
3) greedy coordinate descent (deterministic hillclimb).

This does **not** claim a full categorical model of DiLL on `Dial C`. It is a capability test.
-/

open HeytingLean.LoF
open HeytingLean.LoF.Combinators.Differential
open HeytingLean.LoF.Combinators.Differential.Compute
open Lean

namespace HeytingLean.CLI.DialecticaGradientDemo

def listBind {α β : Type} (xs : List α) (f : α → List β) : List β :=
  xs.foldr (fun x acc => f x ++ acc) []

private def hasFlag (flag : String) (args : List String) : Bool :=
  args.any (fun x => x == flag)

private def getFlagValue? (flag : String) (args : List String) : Option String :=
  let rec go : List String → Option String
    | [] => none
    | x :: y :: xs => if x == flag then some y else go (y :: xs)
    | _ :: [] => none
  go args

private def natOr (s : Option String) (dflt : Nat) : Nat :=
  s.bind String.toNat? |>.getD dflt

private def ratOr (s : Option String) (dflt : Rat) : Rat :=
  match s with
  | none => dflt
  | some t =>
      let t := t.trim
      match t.splitOn "/" with
      | [a, b] =>
          match a.toInt?, b.toNat? with
          | some ai, some bn =>
              if bn = 0 then dflt else (ai : Rat) / (bn : Rat)
          | _, _ => dflt
      | _ =>
          match t.toInt? with
          | some ai => (ai : Rat)
          | none =>
              match t.toNat? with
              | some n => (n : Rat)
              | none => dflt

private def rotate {α} (k : Nat) (xs : List α) : List α :=
  match xs with
  | [] => []
  | _ =>
      let n := xs.length
      let k := k % n
      (xs.drop k) ++ (xs.take k)

private def coeffFromIdx (i : Nat) : Rat :=
  -- map 0..4 to -2..2
  match i % 5 with
  | 0 => (-2 : Int)
  | 1 => (-1 : Int)
  | 2 => (0 : Int)
  | 3 => (1 : Int)
  | _ => (2 : Int)

private def absRat (r : Rat) : Rat := if r < 0 then -r else r

private def nearestGrid (r : Rat) : Rat :=
  let candidates : List Rat := [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)].map (fun z => (z : Rat))
  let rec go (cs : List Rat) (best : Rat) : Rat :=
    match cs with
    | [] => best
    | c :: rest =>
        if absRat (r - c) < absRat (r - best) then go rest c else go rest best
  match candidates with
  | [] => 0
  | c :: rest => go rest c

structure Task where
  name : String
  params : List Comb
  regularization : Rat
  examples : List IOExample
  groundTruth : FSum

def evalLoss (regularization : Rat) (w : FSum) (examples : List IOExample) : Rat :=
  totalLoss regularization w examples

def dynPred (fuel : Nat) (w x : FSum) : FSum :=
  reachabilityBounded fuel (app w x)

def dynError (fuel : Nat) (w : FSum) (ex : IOExample) : FSum :=
  sub (dynPred fuel w ex.input) ex.expected

def dynSingleIOLoss (fuel : Nat) (w : FSum) (ex : IOExample) : Rat :=
  l2NormSq (dynError fuel w ex)

def dynIoLoss (fuel : Nat) (w : FSum) (examples : List IOExample) : Rat :=
  examples.foldl (fun acc ex => acc + dynSingleIOLoss fuel w ex) 0

def dynTotalLoss (fuel : Nat) (regularization : Rat) (w : FSum) (examples : List IOExample) : Rat :=
  dynIoLoss fuel w examples + regularization * l2Reg w

def dynIoLossCoordGrad (fuel : Nat) (params : List Comb) (w : FSum) (ex : IOExample) : FSum :=
  let err := dynError fuel w ex
  params.foldl
    (fun g t =>
      let phi := dynPred fuel (single t) ex.input
      let gc := (2 : Rat) * dot err phi
      add g (single t gc))
    []

def dynIoLossCoordGradDataset (fuel : Nat) (params : List Comb) (w : FSum) (examples : List IOExample) : FSum :=
  examples.foldl (fun g ex => add g (dynIoLossCoordGrad fuel params w ex)) []

def dynTotalGrad (fuel : Nat) (params : List Comb) (regularization : Rat) (w : FSum) (examples : List IOExample) : FSum :=
  add (dynIoLossCoordGradDataset fuel params w examples) (smul ((2 : Rat) * regularization) w)

def weightForParams (params : List Comb) (coeffs : List Rat) : FSum :=
  (List.zip params coeffs).foldl (fun acc pc => add acc (single pc.1 pc.2)) []

private def snapWeightsToGrid (params : List Comb) (w : FSum) : FSum :=
  let coeffs := params.map (fun p => nearestGrid (coeff p w))
  weightForParams params coeffs

private def insertOrReplace (t : Comb) (c : Rat) (w : FSum) : FSum :=
  addTerm t (c - coeff t w) w

private def absCoeff (t : Comb) (w : FSum) : Rat :=
  absRat (coeff t w)

private def topKParams (k : Nat) (params : List Comb) (w : FSum) : List Comb :=
  if k = 0 then [] else
  let scored := params.map (fun t => (absCoeff t w, t))
  let rec insertDesc (x : Rat × Comb) (xs : List (Rat × Comb)) : List (Rat × Comb) :=
    match xs with
    | [] => [x]
    | y :: ys => if x.1 > y.1 then x :: y :: ys else y :: insertDesc x ys
  let sorted := scored.foldl (fun acc x => insertDesc x acc) []
  (sorted.take k).map (fun p => p.2)

private def projectTopK (k : Nat) (params : List Comb) (w : FSum) : FSum :=
  if k = 0 || k >= params.length then
    projectToParams params w
  else
    let keep := (topKParams k params w).toFinset
    w.foldl (fun acc tc => if tc.1 ∈ keep then addTerm tc.1 tc.2 acc else acc) []

def gridVals : List Rat := [(-2 : Int), -1, 0, 1, 2].map (fun z => (z : Rat))

def allCoeffVectors (dim : Nat) : List (List Rat) :=
  let rec go : Nat → List (List Rat)
    | 0 => [[]]
    | Nat.succ n =>
        let tails := go n
        listBind gridVals (fun v => tails.map (fun t => v :: t))
  go dim

structure MethodResult where
  method : String
  loss : Rat
  weights : FSum
  evals : Nat
  iters : Nat

def snapResult (lossFn : FSum → Rat) (params : List Comb) (r : MethodResult) : MethodResult :=
  let w' := snapWeightsToGrid params r.weights
  let l' := lossFn w'
  { method := r.method ++ "_snap"
    loss := l'
    weights := w'
    evals := r.evals + 1
    iters := r.iters }

def runCoordDesc (lossFn : FSum → Rat)
    (pred : FSum → IOExample → FSum)
    (params : List Comb) (examples : List IOExample)
    (passes : Nat) (topk : Nat := 0) : MethodResult :=
  let params0 := params
  let rec passLoop : Nat → FSum → Rat → Nat → Nat → MethodResult
    | 0, w, l, evals, used =>
        { method := if topk = 0 then "coord_cd" else s!"coord_cd_top{topk}"
          loss := l
          weights := w
          evals := evals
          iters := used }
    | Nat.succ fuel, w, l, evals, used =>
        let params := if topk = 0 then params0 else topKParams topk params0 w
        -- One full coordinate sweep with closed-form best step per coordinate.
        let (w', l', evals') :=
          params.foldl
            (fun st t =>
              let (wCur, lCur, n) := st
              -- numerator = Σ dot(err_i, phi_i), denom = Σ dot(phi_i, phi_i)
              let (num, denom) :=
                examples.foldl
                  (fun st2 ex =>
                    let (nn, dd) := st2
                    let yhat := pred wCur ex
                    let err := sub yhat ex.expected
                    let phi := pred (single t) ex
                    (nn + dot err phi, dd + dot phi phi))
                  (0, 0)
              if denom = 0 then
                (wCur, lCur, n)
              else
                let delta := - num / denom
                if delta = 0 then
                  (wCur, lCur, n)
                else
                  let wNew := insertOrReplace t (coeff t wCur + delta) wCur |> projectToParams params0 |> projectTopK topk params0
                  let lNew := lossFn wNew
                  if lNew < lCur then (wNew, lNew, n + 1) else (wCur, lCur, n + 1))
            (w, l, evals)
        if l' < l then
          passLoop fuel w' l' evals' (used + 1)
        else
          { method := if topk = 0 then "coord_cd" else s!"coord_cd_top{topk}"
            loss := l
            weights := w
            evals := evals'
            iters := used + 1 }
  let w0 : FSum := []
  let l0 := lossFn w0
  passLoop passes w0 l0 1 0

def runCoordDescFrom (lossFn : FSum → Rat)
    (pred : FSum → IOExample → FSum)
    (params : List Comb) (examples : List IOExample)
    (passes : Nat) (init : FSum) (topk : Nat := 0) : MethodResult :=
  let init := projectToParams params init |> projectTopK topk params
  let l0 := lossFn init
  -- reuse the main implementation by temporarily shadowing the starting point
  let rec passLoop : Nat → FSum → Rat → Nat → Nat → MethodResult
    | 0, w, l, evals, used =>
        { method := if topk = 0 then "coord_cd" else s!"coord_cd_top{topk}"
          loss := l
          weights := w
          evals := evals
          iters := used }
    | Nat.succ fuel, w, l, evals, used =>
        let paramsUse := if topk = 0 then params else topKParams topk params w
        let (w', l', evals') :=
          paramsUse.foldl
            (fun st t =>
              let (wCur, lCur, n) := st
              let (num, denom) :=
                examples.foldl
                  (fun st2 ex =>
                    let (nn, dd) := st2
                    let yhat := pred wCur ex
                    let err := sub yhat ex.expected
                    let phi := pred (single t) ex
                    (nn + dot err phi, dd + dot phi phi))
                  (0, 0)
              if denom = 0 then
                (wCur, lCur, n)
              else
                let delta := - num / denom
                if delta = 0 then
                  (wCur, lCur, n)
                else
                  let wNew := insertOrReplace t (coeff t wCur + delta) wCur |> projectToParams params |> projectTopK topk params
                  let lNew := lossFn wNew
                  if lNew < lCur then (wNew, lNew, n + 1) else (wCur, lCur, n + 1))
            (w, l, evals)
        if l' < l then
          passLoop fuel w' l' evals' (used + 1)
        else
          { method := if topk = 0 then "coord_cd" else s!"coord_cd_top{topk}"
            loss := l
            weights := w
            evals := evals'
            iters := used + 1 }
  passLoop passes init l0 1 0

def runExhaustive (t : Task) : MethodResult :=
  let dim := t.params.length
  let coeffs := allCoeffVectors dim
  let initBest : Option (Rat × FSum) := none
  let (best, evals) :=
    coeffs.foldl
      (fun st cs =>
        let (best?, n) := st
        let w := weightForParams t.params cs
        let l := evalLoss t.regularization w t.examples
        let best?' :=
          match best? with
          | none => some (l, w)
          | some (lb, wb) => if l ≤ lb then some (l, w) else some (lb, wb)
        (best?', n + 1))
      (initBest, 0)
  let (loss, weights) := best.getD (0, [])
  { method := "exhaustive"
    loss := loss
    weights := weights
    evals := evals
    iters := 1 }

def coordStep : Rat := (1 : Rat)

def tryNeighbors (params : List Comb) (w : FSum) : List FSum :=
  listBind params (fun p =>
    let bumpPlus := add w (single p coordStep)
    let bumpMinus := add w (single p (-coordStep))
    [bumpPlus, bumpMinus])

def runGreedy (t : Task) (maxIters : Nat) : MethodResult :=
  let rec go : Nat → FSum → Rat → Nat → Nat → MethodResult
    | 0, w, bestLoss, evals, itersUsed =>
        { method := "greedy"
          loss := bestLoss
          weights := w
          evals := evals
          iters := itersUsed }
    | Nat.succ itersLeft, w, bestLoss, evals, itersUsed =>
        let neigh := tryNeighbors t.params w
        let (bestW, bestL, evals') :=
          neigh.foldl
            (fun st w' =>
              let (bw, bl, n) := st
              let l := evalLoss t.regularization w' t.examples
              if l < bl then (w', l, n + 1) else (bw, bl, n + 1))
            (w, bestLoss, evals)
        if bestL < bestLoss then
          go itersLeft bestW bestL evals' (itersUsed + 1)
        else
          { method := "greedy"
            loss := bestLoss
            weights := w
            evals := evals'
            iters := itersUsed + 1 }
  let w0 : FSum := []
  let l0 := evalLoss t.regularization w0 t.examples
  go maxIters w0 l0 1 0

def runGradient (t : Task) (iters : Nat) (lr : Rat) : MethodResult :=
  let nEx := t.examples.length
  let lr :=
    if nEx = 0 then lr else lr / (nEx : Rat)
  let cfg : Compute.GDConfig :=
    { learningRate := lr
      iterations := iters
      regularization := t.regularization
      params := t.params }
  let st := Compute.gradientDescentLoop cfg t.examples []
  { method := "gradient"
    loss := st.currentLoss
    weights := st.currentWeights
    evals := (iters + 1) -- loss computed each iter in the loop; conservative
    iters := iters }

def runGradientLineSearch (t : Task) (iters : Nat) (lrs : List Rat) : MethodResult :=
  let params := t.params
  let reg := t.regularization
  let examples := t.examples
  let nEx := examples.length
  let lrs :=
    if nEx = 0 then lrs else lrs.map (fun lr => lr / (nEx : Rat))
  let rec loop : Nat → FSum → Rat → Nat → MethodResult
    | 0, w, l, evals =>
        { method := "gradient_ls"
          loss := l
          weights := w
          evals := evals
          iters := iters }
    | Nat.succ fuel, w, l, evals =>
        let g := totalGrad params reg w examples
        let candidates := lrs.map (fun lr => projectToParams params (sub w (smul lr g)))
        let (bestW, bestL, evals') :=
          candidates.foldl
            (fun st w' =>
              let (bw, bl, n) := st
              let l' := evalLoss reg w' examples
              if l' < bl then (w', l', n + 1) else (bw, bl, n + 1))
            (w, l, evals)
        if bestL < l then
          loop fuel bestW bestL evals'
        else
          { method := "gradient_ls"
            loss := l
            weights := w
            evals := evals'
            iters := iters - fuel }
  let w0 : FSum := []
  let l0 := evalLoss reg w0 examples
  loop iters w0 l0 1

def runGreedyDyn (fuel : Nat) (t : Task) (maxIters : Nat) : MethodResult :=
  let lossFn := dynTotalLoss fuel t.regularization
  let rec go : Nat → FSum → Rat → Nat → Nat → MethodResult
    | 0, w, bestLoss, evals, itersUsed =>
        { method := "greedy_dyn"
          loss := bestLoss
          weights := w
          evals := evals
          iters := itersUsed }
    | Nat.succ itersLeft, w, bestLoss, evals, itersUsed =>
        let neigh := tryNeighbors t.params w
        let (bestW, bestL, evals') :=
          neigh.foldl
            (fun st w' =>
              let (bw, bl, n) := st
              let l := lossFn w' t.examples
              if l < bl then (w', l, n + 1) else (bw, bl, n + 1))
            (w, bestLoss, evals)
        if bestL < bestLoss then
          go itersLeft bestW bestL evals' (itersUsed + 1)
        else
          { method := "greedy_dyn"
            loss := bestLoss
            weights := w
            evals := evals'
            iters := itersUsed + 1 }
  let w0 : FSum := []
  let l0 := lossFn w0 t.examples
  go maxIters w0 l0 1 0

def runGradientDyn (fuel : Nat) (t : Task) (iters : Nat) (lr : Rat) : MethodResult :=
  let params := t.params
  let reg := t.regularization
  let examples := t.examples
  let nEx := examples.length
  let lr := if nEx = 0 then lr else lr / (nEx : Rat)
  let rec loop : Nat → FSum → Rat → Nat → MethodResult
    | 0, w, l, evals =>
        { method := "gradient_dyn"
          loss := l
          weights := w
          evals := evals
          iters := iters }
    | Nat.succ fuelI, w, l, evals =>
        let g := dynTotalGrad fuel params reg w examples
        let w' := projectToParams params (sub w (smul lr g))
        let l' := dynTotalLoss fuel reg w' examples
        if l' < l then
          loop fuelI w' l' (evals + 1)
        else
          { method := "gradient_dyn"
            loss := l
            weights := w
            evals := evals + 1
            iters := iters - fuelI }
  let w0 : FSum := []
  let l0 := dynTotalLoss fuel reg w0 examples
  loop iters w0 l0 1

def runGradientLineSearchDyn (fuel : Nat) (t : Task) (iters : Nat) (lrs : List Rat) : MethodResult :=
  let params := t.params
  let reg := t.regularization
  let examples := t.examples
  let nEx := examples.length
  let lrs := if nEx = 0 then lrs else lrs.map (fun lr => lr / (nEx : Rat))
  let rec loop : Nat → FSum → Rat → Nat → MethodResult
    | 0, w, l, evals =>
        { method := "gradient_ls_dyn"
          loss := l
          weights := w
          evals := evals
          iters := iters }
    | Nat.succ fuelI, w, l, evals =>
        let g := dynTotalGrad fuel params reg w examples
        let candidates := lrs.map (fun lr => projectToParams params (sub w (smul lr g)))
        let (bestW, bestL, evals') :=
          candidates.foldl
            (fun st w' =>
              let (bw, bl, n) := st
              let l' := dynTotalLoss fuel reg w' examples
              if l' < bl then (w', l', n + 1) else (bw, bl, n + 1))
            (w, l, evals)
        if bestL < l then
          loop fuelI bestW bestL evals'
        else
          { method := "gradient_ls_dyn"
            loss := l
            weights := w
            evals := evals'
            iters := iters - fuelI }
  let w0 : FSum := []
  let l0 := dynTotalLoss fuel reg w0 examples
  loop iters w0 l0 1

def runGradientLineSearchDynProjected (fuel : Nat) (t : Task) (iters : Nat) (lrs : List Rat)
    (snapPeriod : Nat := 1) (topk : Nat := 0) : MethodResult :=
  let params0 := t.params
  let params := t.params
  let reg := t.regularization
  let examples := t.examples
  let nEx := examples.length
  let lrs := if nEx = 0 then lrs else lrs.map (fun lr => lr / (nEx : Rat))
  let lossFn := fun w => dynTotalLoss fuel reg w examples
  let rec loop : Nat → Nat → FSum → Rat → Nat → MethodResult
    | 0, _iter, w, l, evals =>
        { method := if topk = 0 then "gradient_ls_dyn_proj" else s!"gradient_ls_dyn_proj_top{topk}"
          loss := l
          weights := w
          evals := evals
          iters := iters }
    | Nat.succ fuelI, iter, w, l, evals =>
        let g := dynTotalGrad fuel params reg w examples
        let candidates := lrs.map (fun lr => projectToParams params (sub w (smul lr g)))
        let (bestW, _bestL, evals') :=
          candidates.foldl
            (fun st w' =>
              let (bw, bl, n) := st
              let w'' := projectTopK topk params0 w'
              let l' := lossFn w''
              if l' < bl then (w'', l', n + 1) else (bw, bl, n + 1))
            (w, l, evals)
        let wNext :=
          if snapPeriod != 0 && (iter + 1) % snapPeriod == 0 then
            snapWeightsToGrid params0 bestW |> projectToParams params0 |> projectTopK topk params0
          else
            bestW
        let lNext := lossFn wNext
        if lNext < l then
          loop fuelI (iter + 1) wNext lNext (evals' + 1)
        else
          { method := if topk = 0 then "gradient_ls_dyn_proj" else s!"gradient_ls_dyn_proj_top{topk}"
            loss := l
            weights := w
            evals := evals' + 1
            iters := iters - fuelI }
  let w0 : FSum := []
  let l0 := lossFn w0
  loop iters 0 w0 l0 1

def runGradientLineSearchDynProjectedFrom (fuel : Nat) (t : Task) (iters : Nat) (lrs : List Rat)
    (init : FSum) (snapPeriod : Nat := 1) (topk : Nat := 0) : MethodResult :=
  let params0 := t.params
  let params := t.params
  let reg := t.regularization
  let examples := t.examples
  let nEx := examples.length
  let lrs := if nEx = 0 then lrs else lrs.map (fun lr => lr / (nEx : Rat))
  let lossFn := fun w => dynTotalLoss fuel reg w examples
  let init := projectToParams params0 init |> projectTopK topk params0
  let rec loop : Nat → Nat → FSum → Rat → Nat → MethodResult
    | 0, _iter, w, l, evals =>
        { method := if topk = 0 then "gradient_ls_dyn_proj" else s!"gradient_ls_dyn_proj_top{topk}"
          loss := l
          weights := w
          evals := evals
          iters := iters }
    | Nat.succ fuelI, iter, w, l, evals =>
        let g := dynTotalGrad fuel params reg w examples
        let candidates := lrs.map (fun lr => projectToParams params (sub w (smul lr g)))
        let (bestW, _bestL, evals') :=
          candidates.foldl
            (fun st w' =>
              let (bw, bl, n) := st
              let w'' := projectTopK topk params0 w'
              let l' := lossFn w''
              if l' < bl then (w'', l', n + 1) else (bw, bl, n + 1))
            (w, l, evals)
        let wNext :=
          if snapPeriod != 0 && (iter + 1) % snapPeriod == 0 then
            snapWeightsToGrid params0 bestW |> projectToParams params0 |> projectTopK topk params0
          else
            bestW
        let lNext := lossFn wNext
        if lNext < l then
          loop fuelI (iter + 1) wNext lNext (evals' + 1)
        else
          { method := if topk = 0 then "gradient_ls_dyn_proj" else s!"gradient_ls_dyn_proj_top{topk}"
            loss := l
            weights := w
            evals := evals' + 1
            iters := iters - fuelI }
  let l0 := lossFn init
  loop iters 0 init l0 1

def runRandomSearch (t : Task) (samples seed : Nat) : MethodResult :=
  let dim := t.params.length
  let rec mkCoeffs : Nat → Nat → List Rat
    | 0, _ => []
    | Nat.succ k, s => coeffFromIdx (s + k) :: mkCoeffs k (s * 1103515245 + 12345)
  let rec loop : Nat → Nat → Option (Rat × FSum) → Nat → MethodResult
    | 0, _s, best?, evals =>
        let (loss, w) := best?.getD (0, [])
        { method := "random"
          loss := loss
          weights := w
          evals := evals
          iters := samples }
    | Nat.succ n, s, best?, evals =>
        let coeffs := mkCoeffs dim s
        let w := weightForParams t.params coeffs
        let l := evalLoss t.regularization w t.examples
        let best?' :=
          match best? with
          | none => some (l, w)
          | some (lb, wb) => if l ≤ lb then some (l, w) else some (lb, wb)
        loop n (s * 1103515245 + 12345) best?' (evals + 1)
  loop samples seed none 0

def basisPool : List Comb :=
  [ .K, .S, .Y, .I
  , .app .K .K, .app .K .S, .app .K .Y, .app .K .I
  , .app .S .K, .app .S .S, .app .S .Y, .app .S .I
  , .app .Y .K, .app .Y .S, .app .Y .Y, .app .Y .I
  , .app (.app .K .S) .Y
  , .app (.app .S .K) .Y
  , .app (.app .S .S) .Y
  , .app (.app .K .K) .Y
  ]

def inputPool : List Comb :=
  [ .Y, .K, .S, .I
  , .app .S .Y
  , .app .K .Y
  , .app (.app .K .S) .Y
  , .app (.app .S .K) .Y
  ]

def mkPlantedTask (dim examples seed : Nat) (reg : Rat) : Task :=
  let params := (rotate seed basisPool).take dim
  let coeffs := (List.range dim).map (fun i => coeffFromIdx (seed + 7 * i))
  let coeffs :=
    if coeffs.all (fun c => c = 0) then
      -- ensure nontrivial planted witness
      coeffs.set 0 (1 : Rat)
    else coeffs
  let wStar := weightForParams params coeffs
  let inputs := (rotate (seed + 1) inputPool).take (Nat.max 1 examples)
  let exs :=
    inputs.map (fun c =>
      let x : FSum := single c
      let y : FSum := app wStar x
      { input := x, expected := y })
  { name := s!"planted_dim{dim}_ex{examples}_seed{seed}"
    params := params
    regularization := reg
    examples := exs
    groundTruth := wStar }

def mkPlantedTaskDyn (fuel dim examples seed : Nat) (reg : Rat) : Task :=
  let t := mkPlantedTask dim examples seed reg
  let exs :=
    t.examples.map (fun ex =>
      { input := ex.input
        expected := dynPred fuel t.groundTruth ex.input })
  { t with
    name := t.name ++ s!"_fuel{fuel}"
    examples := exs }

def mkTask1 : Task :=
  -- target: w·x = 2*(K x) + 1*(S x)
  let params : List Comb := [.K, .S]
  let x : FSum := single .Y
  let y : FSum := add (smul 2 (single (.app .K .Y))) (single (.app .S .Y))
  let wStar := weightForParams params [(2 : Rat), (1 : Rat)]
  { name := "linear_KS"
    params := params
    regularization := 0
    examples := [{ input := x, expected := y }]
    groundTruth := wStar }

def mkTask2 : Task :=
  -- target: w·x = 1*(K x) + (-1)*(S x) + 2*(Y x)
  let params : List Comb := [.K, .S, .Y]
  let x : FSum := single (.app .S .Y)
  let y : FSum :=
    add (single (.app .K (.app .S .Y)) (1 : Rat))
      (add (single (.app .S (.app .S .Y)) (-1 : Rat))
        (single (.app .Y (.app .S .Y)) (2 : Rat)))
  let wStar := weightForParams params [(1 : Rat), (-1 : Rat), (2 : Rat)]
  { name := "linear_KSY"
    params := params
    regularization := 0
    examples := [{ input := x, expected := y }]
    groundTruth := wStar }

def mkTask3 : Task :=
  -- a slightly “coupled” target: include app-ed params as basis terms
  let p1 : Comb := .app .K .Y
  let p2 : Comb := .app .S .Y
  let params : List Comb := [p1, p2]
  let x : FSum := single (.app (.app .K .S) .Y)
  let y : FSum :=
    add (single (.app p1 (.app (.app .K .S) .Y)) (2 : Rat))
      (single (.app p2 (.app (.app .K .S) .Y)) (1 : Rat))
  let wStar := weightForParams params [(2 : Rat), (1 : Rat)]
  { name := "coupled_app_basis"
    params := params
    regularization := 0
    examples := [{ input := x, expected := y }]
    groundTruth := wStar }

def tasks : List Task := [mkTask1, mkTask2, mkTask3]

def showFSumShort (w : FSum) : String :=
  showFSum w

def jsonMethod (r : MethodResult) : Lean.Json :=
  Lean.Json.mkObj
    [ ("method", Lean.Json.str r.method)
    , ("loss", Lean.Json.str (toString r.loss))
    , ("evals", Lean.Json.num (Lean.JsonNumber.fromNat r.evals))
    , ("iters", Lean.Json.num (Lean.JsonNumber.fromNat r.iters))
    , ("weights", Lean.Json.str (showFSumShort r.weights))
    ]

def jsonTask (t : Task) (ms : List MethodResult) : Lean.Json :=
  Lean.Json.mkObj
    [ ("task", Lean.Json.str t.name)
    , ("params", Lean.Json.num (Lean.JsonNumber.fromNat t.params.length))
    , ("methods", Lean.Json.arr (ms.map jsonMethod |>.toArray))
    ]

def emitJSON (rows : List (Task × List MethodResult)) : Lean.Json :=
  Lean.Json.mkObj
    [ ("suite", Lean.Json.str "differentiable_dialectica_v1")
    , ("tasks", Lean.Json.arr (rows.map (fun (t, ms) => jsonTask t ms) |>.toArray))
    ]

def runTask (t : Task) : Task × List MethodResult :=
  let exhaustive := runExhaustive t
  let greedy := runGreedy t 50
  let grad := runGradient t 10 ((1 : Rat) / 2)
  let gradLS := runGradientLineSearch t 10 [ (1 : Rat), (1 : Rat) / 2, (1 : Rat) / 4, (1 : Rat) / 8 ]
  (t, [exhaustive, greedy, grad, gradLS])

def runScaledSweep (dims : List Nat) (examples dimSeedRuns iters : Nat) (lr reg : Rat) (randSamples : Nat) :
    Lean.Json :=
  let seeds := List.range dimSeedRuns
  let rows : List (Task × List MethodResult) :=
    listBind dims (fun d =>
      seeds.map (fun s =>
        let t := mkPlantedTask d examples s reg
        let greedy := runGreedy t (Nat.min 200 (20 * d))
        let grad := runGradient t iters lr
        let gradLS := runGradientLineSearch t iters [ (1 : Rat), (1 : Rat) / 2, (1 : Rat) / 4, (1 : Rat) / 8 ]
        let lossFn := fun w => totalLoss t.regularization w t.examples
        let pred := fun w ex => app w ex.input
        let cd := runCoordDesc lossFn (fun w ex => pred w ex) t.params t.examples (Nat.min 50 (5 * d)) (topk := 0)
        let cdTop := runCoordDesc lossFn (fun w ex => pred w ex) t.params t.examples (Nat.min 50 (5 * d)) (topk := Nat.min 8 d)
        let rnd := runRandomSearch t randSamples (12345 + 97 * s + 13 * d)
        (t, [rnd, greedy, grad, gradLS, cd, cdTop])
      )
    )
  Lean.Json.mkObj
    [ ("suite", Lean.Json.str "differentiable_dialectica_scaled_v1")
    , ("dims", Lean.Json.arr (dims.map (fun d => Lean.Json.num (Lean.JsonNumber.fromNat d)) |>.toArray))
    , ("examples", Lean.Json.num (Lean.JsonNumber.fromNat examples))
    , ("seedRuns", Lean.Json.num (Lean.JsonNumber.fromNat dimSeedRuns))
    , ("iters", Lean.Json.num (Lean.JsonNumber.fromNat iters))
    , ("lr", Lean.Json.str (toString lr))
    , ("reg", Lean.Json.str (toString reg))
    , ("randSamples", Lean.Json.num (Lean.JsonNumber.fromNat randSamples))
    , ("tasks", Lean.Json.arr (rows.map (fun (t, ms) => jsonTask t ms) |>.toArray))
    ]

def runScaledSweepDyn (fuel : Nat) (dims : List Nat) (examples dimSeedRuns iters : Nat) (lr reg : Rat) (randSamples : Nat) :
    Lean.Json :=
  let seeds := List.range dimSeedRuns
  let rows : List (Task × List MethodResult) :=
    listBind dims (fun d =>
      seeds.map (fun s =>
        let t0 := mkPlantedTaskDyn fuel d examples s reg
        let lossFn := fun w => dynTotalLoss fuel t0.regularization w t0.examples
        let pred := fun w ex => dynPred fuel w ex.input
        let greedy := runGreedyDyn fuel t0 (Nat.min 400 (30 * d))
        let grad := runGradientDyn fuel t0 iters lr
        let gradLS := runGradientLineSearchDyn fuel t0 iters [ (1 : Rat), (1 : Rat) / 2, (1 : Rat) / 4, (1 : Rat) / 8 ]
        let gradSnap := snapResult lossFn t0.params grad
        let gradLSSnap := snapResult lossFn t0.params gradLS
        let gradProj := runGradientLineSearchDynProjected fuel t0 iters [ (1 : Rat), (1 : Rat) / 2, (1 : Rat) / 4, (1 : Rat) / 8 ] (snapPeriod := 1) (topk := 0)
        let gradProjSnap := snapResult lossFn t0.params gradProj
        let gradProjTop := runGradientLineSearchDynProjected fuel t0 iters [ (1 : Rat), (1 : Rat) / 2, (1 : Rat) / 4, (1 : Rat) / 8 ] (snapPeriod := 1) (topk := Nat.min 8 d)
        let gradProjTopSnap := snapResult lossFn t0.params gradProjTop
        let cd := runCoordDesc lossFn (fun w ex => pred w ex) t0.params t0.examples (Nat.min 80 (6 * d)) (topk := 0)
        let cdSnap := snapResult lossFn t0.params cd
        let cdTop := runCoordDesc lossFn (fun w ex => pred w ex) t0.params t0.examples (Nat.min 80 (6 * d)) (topk := Nat.min 8 d)
        let cdTopSnap := snapResult lossFn t0.params cdTop
        let rnd := runRandomSearch t0 randSamples (12345 + 97 * s + 13 * d)
        (t0, [rnd, greedy, grad, gradSnap, gradLS, gradLSSnap, gradProj, gradProjSnap, gradProjTop, gradProjTopSnap, cd, cdSnap, cdTop, cdTopSnap])
      )
    )
  Lean.Json.mkObj
    [ ("suite", Lean.Json.str "differentiable_dialectica_scaled_dyn_v1")
    , ("fuel", Lean.Json.num (Lean.JsonNumber.fromNat fuel))
    , ("dims", Lean.Json.arr (dims.map (fun d => Lean.Json.num (Lean.JsonNumber.fromNat d)) |>.toArray))
    , ("examples", Lean.Json.num (Lean.JsonNumber.fromNat examples))
    , ("seedRuns", Lean.Json.num (Lean.JsonNumber.fromNat dimSeedRuns))
    , ("iters", Lean.Json.num (Lean.JsonNumber.fromNat iters))
    , ("lr", Lean.Json.str (toString lr))
    , ("reg", Lean.Json.str (toString reg))
    , ("randSamples", Lean.Json.num (Lean.JsonNumber.fromNat randSamples))
    , ("tasks", Lean.Json.arr (rows.map (fun (t, ms) => jsonTask t ms) |>.toArray))
    ]

def parseNatList (s : String) : List Nat :=
  s.splitOn "," |>.filterMap (fun t => t.trim.toNat?)

def runCurriculum (fuels : List Nat) (dims : List Nat) (examples seedRuns iters : Nat) (lr reg : Rat)
    (snapPeriod : Nat := 1) (topk : Nat := 0) : Lean.Json :=
  let seeds := List.range seedRuns
  let lrs : List Rat := [ (1 : Rat), (1 : Rat)/2, (1 : Rat)/4, (1 : Rat)/8 ]
  let rows :=
    listBind seeds (fun s =>
      listBind dims (fun d =>
        let rec goFuel : List Nat → FSum → List Lean.Json
          | [], _w => []
          | f :: fs, wPrev =>
              let t := mkPlantedTaskDyn f d examples s reg
              let lossFn := fun w => dynTotalLoss f reg w t.examples
              let pred := fun w ex => dynPred f w ex.input
              let grad := runGradientLineSearchDynProjectedFrom f t iters lrs wPrev (snapPeriod := snapPeriod) (topk := topk)
              let gradSnap := snapResult lossFn t.params grad
              let cd := runCoordDescFrom lossFn (fun w ex => pred w ex) t.params t.examples (Nat.min 80 (6 * d)) wPrev (topk := topk)
              let cdSnap := snapResult lossFn t.params cd
              let stage :=
                Lean.Json.mkObj
                  [ ("seed", Lean.Json.num (Lean.JsonNumber.fromNat s))
                  , ("dim", Lean.Json.num (Lean.JsonNumber.fromNat d))
                  , ("fuel", Lean.Json.num (Lean.JsonNumber.fromNat f))
                  , ("gradient", jsonMethod grad)
                  , ("gradientSnap", jsonMethod gradSnap)
                  , ("coord", jsonMethod cd)
                  , ("coordSnap", jsonMethod cdSnap)
                  ]
              let wNext := gradSnap.weights
              stage :: goFuel fs wNext
        goFuel fuels []))
  Lean.Json.mkObj
    [ ("suite", Lean.Json.str "differentiable_dialectica_curriculum_v1")
    , ("fuels", Lean.Json.arr (fuels.map (fun f => Lean.Json.num (Lean.JsonNumber.fromNat f)) |>.toArray))
    , ("dims", Lean.Json.arr (dims.map (fun d => Lean.Json.num (Lean.JsonNumber.fromNat d)) |>.toArray))
    , ("examples", Lean.Json.num (Lean.JsonNumber.fromNat examples))
    , ("seedRuns", Lean.Json.num (Lean.JsonNumber.fromNat seedRuns))
    , ("iters", Lean.Json.num (Lean.JsonNumber.fromNat iters))
    , ("lr", Lean.Json.str (toString lr))
    , ("reg", Lean.Json.str (toString reg))
    , ("snapPeriod", Lean.Json.num (Lean.JsonNumber.fromNat snapPeriod))
    , ("topk", Lean.Json.num (Lean.JsonNumber.fromNat topk))
    , ("stages", Lean.Json.arr (rows.toArray))
    ]

def main (_argv : List String) : IO Unit := do
  let argv := _argv
  if argv.isEmpty || hasFlag "--help" argv then
    IO.println "usage: dialectica_gradient_demo [--mode toy|scaled|curriculum]"
    IO.println "  toy (default): runs 3 fixed tiny tasks + exhaustive/greedy/gradient"
    IO.println "  scaled: planted tasks + baselines (random/greedy/gradient/gradient_ls)"
    IO.println "  curriculum: stage-wise (fuel/dim) warm-start tests"
    IO.println ""
    IO.println "scaled flags:"
    IO.println "  --dims 2,4,8,12,16   (default)"
    IO.println "  --examples N         (default: 8)"
    IO.println "  --seeds N            (default: 5)"
    IO.println "  --iters N            (default: 25)"
    IO.println "  --lr A/B             (default: 1/4)"
    IO.println "  --reg A/B            (default: 0)"
    IO.println "  --rand N             (default: 2000)"
    IO.println "  --fuel N             (default: 0; if >0 uses reachabilityBounded dynamics objective)"
    IO.println ""
    IO.println "curriculum flags:"
    IO.println "  --fuels 0,1,2,3      (default: 0,1,2)"
    IO.println "  --dims 2,4,8,12,16   (default)"
    IO.println "  --examples N         (default: 8)"
    IO.println "  --seeds N            (default: 5)"
    IO.println "  --iters N            (default: 30)"
    IO.println "  --snapPeriod N       (default: 1)"
    IO.println "  --topk N             (default: 0)"
    return
  let mode := (getFlagValue? "--mode" argv).getD "toy"
  if mode == "scaled" then
    let dimsStr := (getFlagValue? "--dims" argv).getD "2,4,8,12,16"
    let dims :=
      (dimsStr.splitOn "," |>.filterMap (fun s => s.trim.toNat?))
    let examples := natOr (getFlagValue? "--examples" argv) 8
    let seeds := natOr (getFlagValue? "--seeds" argv) 5
    let iters := natOr (getFlagValue? "--iters" argv) 25
    let lr := ratOr (getFlagValue? "--lr" argv) ((1 : Rat) / 4)
    let reg := ratOr (getFlagValue? "--reg" argv) 0
    let randN := natOr (getFlagValue? "--rand" argv) 2000
    let fuel := natOr (getFlagValue? "--fuel" argv) 0
    IO.println "[dialectica_gradient_demo] scaled sweep"
    if fuel = 0 then
      IO.println (toString (runScaledSweep dims examples seeds iters lr reg randN))
    else
      IO.println (toString (runScaledSweepDyn fuel dims examples seeds iters lr reg randN))
  else if mode == "curriculum" then
    let fuelsStr := (getFlagValue? "--fuels" argv).getD "0,1,2"
    let fuels := parseNatList fuelsStr
    let dimsStr := (getFlagValue? "--dims" argv).getD "2,4,8,12,16"
    let dims := parseNatList dimsStr
    let examples := natOr (getFlagValue? "--examples" argv) 8
    let seeds := natOr (getFlagValue? "--seeds" argv) 5
    let iters := natOr (getFlagValue? "--iters" argv) 30
    let lr := ratOr (getFlagValue? "--lr" argv) ((1 : Rat) / 4)
    let reg := ratOr (getFlagValue? "--reg" argv) 0
    let snapPeriod := natOr (getFlagValue? "--snapPeriod" argv) 1
    let topk := natOr (getFlagValue? "--topk" argv) 0
    IO.println "[dialectica_gradient_demo] curriculum"
    IO.println (toString (runCurriculum fuels dims examples seeds iters lr reg (snapPeriod := snapPeriod) (topk := topk)))
  else
    IO.println "[dialectica_gradient_demo] running objective capability tests"
    let rows := tasks.map runTask
    for (t, ms) in rows do
      IO.println s!"\n== task: {t.name} (params={t.params.length}) =="
      for r in ms do
        IO.println s!"- {r.method}: loss={r.loss} evals={r.evals} iters={r.iters}"
    IO.println "\n--- JSON ---"
    IO.println (toString (emitJSON rows))

end HeytingLean.CLI.DialecticaGradientDemo

def main := HeytingLean.CLI.DialecticaGradientDemo.main
