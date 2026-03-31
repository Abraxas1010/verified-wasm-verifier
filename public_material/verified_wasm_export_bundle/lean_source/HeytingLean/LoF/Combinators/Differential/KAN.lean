import HeytingLean.LoF.Combinators.Differential.Compute

/-!
# Differential.KAN

Minimal, executable KAN-style infrastructure for differentiable ATP experiments.

This module uses open-uniform B-spline edge activations over `Rat`:
- edge basis weights are computed via Cox-de Boor recursion,
- forward pass is total and numerically stable,
- backward pass propagates through all layers (control-point gradients exact, input derivatives finite-difference).
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Differential
namespace KAN

open Compute

private def absRat (r : Rat) : Rat :=
  if r < 0 then -r else r

private def clampRat (x lo hi : Rat) : Rat :=
  if x < lo then lo else if x > hi then hi else x

private def safeDenom (r : Rat) : Rat :=
  if r = 0 then 1 else r

private def arrayGetRat (xs : Array Rat) (i : Nat) : Rat :=
  xs.getD i 0

structure KANEdge where
  controlPoints : List Rat
  gridMin : Rat := -1
  gridMax : Rat := 1
  order : Nat := 3
  deriving Repr

/-- Adaptive edge with explicit centers/widths, used for D2 goal-conditioned remeshing. -/
structure AdaptiveKANEdge where
  centers : List Rat
  widths : List Rat
  coefficients : List Rat
  gridMin : Rat := -1
  gridMax : Rat := 1
  deriving Repr

structure KANEdgeGrad where
  controlPointGrad : List Rat
  deriving Repr

private def gridSpan (e : KANEdge) : Rat :=
  safeDenom (e.gridMax - e.gridMin)

private def gridSpanAdaptive (e : AdaptiveKANEdge) : Rat :=
  safeDenom (e.gridMax - e.gridMin)

private def knotAt (e : KANEdge) (idx n : Nat) : Rat :=
  if n ≤ 1 then
    e.gridMin
  else
    let ratio : Rat := (Int.ofNat idx : Rat) / (Int.ofNat (n - 1) : Rat)
    e.gridMin + ratio * (gridSpan e)

private def knotAtAdaptive (e : AdaptiveKANEdge) (idx n : Nat) : Rat :=
  if n ≤ 1 then
    e.gridMin
  else
    let ratio : Rat := (Int.ofNat idx : Rat) / (Int.ofNat (n - 1) : Rat)
    e.gridMin + ratio * (gridSpanAdaptive e)

private def safeWidth (w : Rat) : Rat :=
  let a := absRat w
  if a = 0 then (1 : Rat) / 10 else a

private def defaultAdaptiveCenters (e : AdaptiveKANEdge) (n : Nat) : List Rat :=
  (List.range n).map (fun i => knotAtAdaptive e i n)

private def defaultAdaptiveWidths (e : AdaptiveKANEdge) (n : Nat) : List Rat :=
  let base := (gridSpanAdaptive e) / (Int.ofNat (max 1 n) : Rat)
  List.replicate n (safeWidth base)

/-- Cauchy-kernel adaptive edge evaluation with learnable centers and widths. -/
def AdaptiveKANEdge.eval (e : AdaptiveKANEdge) (x : Rat) : Rat :=
  let coeffs := if e.coefficients.isEmpty then [0] else e.coefficients
  let n := coeffs.length
  let centers :=
    if e.centers.length = n then
      e.centers
    else
      defaultAdaptiveCenters e n
  let widths :=
    if e.widths.length = n then
      e.widths
    else
      defaultAdaptiveWidths e n
  let rows := List.zip (List.zip coeffs centers) widths
  let num :=
    rows.foldl
      (fun acc row =>
        let coeff := row.1.1
        let c := row.1.2
        let w := safeWidth row.2
        let k := (1 : Rat) / (1 + absRat (x - c) / w)
        acc + coeff * k)
      0
  let den :=
    rows.foldl
      (fun acc row =>
        let c := row.1.2
        let w := safeWidth row.2
        acc + ((1 : Rat) / (1 + absRat (x - c) / w)))
      0
  if den = 0 then 0 else num / den

def AdaptiveKANEdge.fromEdge (e : KANEdge) : AdaptiveKANEdge :=
  let coeffs := if e.controlPoints.isEmpty then [0] else e.controlPoints
  let n := coeffs.length
  {
    centers := (List.range n).map (fun i => knotAt e i n)
    widths := List.replicate n ((gridSpan e) / (Int.ofNat (max 1 n) : Rat))
    coefficients := coeffs
    gridMin := e.gridMin
    gridMax := e.gridMax
  }

def AdaptiveKANEdge.toEdge (e : AdaptiveKANEdge) : KANEdge :=
  {
    controlPoints := if e.coefficients.isEmpty then [0] else e.coefficients
    gridMin := e.gridMin
    gridMax := e.gridMax
    order := 3
  }

def AdaptiveKANEdge.adaptByFeatures (e : AdaptiveKANEdge) (features : Array Rat) : AdaptiveKANEdge :=
  let shift := ((features.getD 0 0) - (features.getD 1 0)) / 20
  let widen := absRat (features.getD 2 0) / 20
  let gain := 1 + (features.getD 3 0) / 50
  let coeffs := e.coefficients.map (fun c => c * gain)
  let centers := e.centers.map (fun c => clampRat (c + shift) e.gridMin e.gridMax)
  let widths := e.widths.map (fun w => safeWidth (w + widen))
  { e with coefficients := coeffs, centers := centers, widths := widths }

/-- Open-uniform knot vector for B-spline evaluation. -/
def KANEdge.knotVector (e : KANEdge) : Array Rat :=
  let n := e.controlPoints.length
  if n = 0 then
    #[]
  else
    let p := min e.order (n - 1)
    let left := List.replicate (p + 1) e.gridMin
    let right := List.replicate (p + 1) e.gridMax
    let interiorCount := n - (p + 1)
    let interior :=
      (List.range interiorCount).map (fun j =>
        let ratio : Rat := (Int.ofNat (j + 1) : Rat) / (Int.ofNat (interiorCount + 1) : Rat)
        e.gridMin + ratio * (gridSpan e))
    (left ++ interior ++ right).toArray

private def basisAt (knots : Array Rat) (gridMax : Rat) (i p : Nat) (x : Rat) : Rat :=
  match p with
  | 0 =>
      let l := knots.getD i 0
      let r := knots.getD (i + 1) l
      let inSpan := (l ≤ x) && (x < r)
      let rightClosed := (x = gridMax) && (r = gridMax) && (l < r)
      if inSpan || rightClosed then 1 else 0
  | Nat.succ p' =>
      let l := knots.getD i 0
      let m := knots.getD (i + p' + 1) l
      let l' := knots.getD (i + 1) l
      let r := knots.getD (i + p' + 2) l'
      let den1 := m - l
      let den2 := r - l'
      let a :=
        if den1 = 0 then
          0
        else
          ((x - l) / den1) * basisAt knots gridMax i p' x
      let b :=
        if den2 = 0 then
          0
        else
          ((r - x) / den2) * basisAt knots gridMax (i + 1) p' x
      a + b

/-- B-spline interpolation weights centered on an open-uniform knot vector. -/
def KANEdge.basisWeights (e : KANEdge) (x : Rat) : List Rat :=
  let cps := e.controlPoints
  let n := cps.length
  if n = 0 then
    []
  else
    let x' := clampRat x e.gridMin e.gridMax
    let p := min e.order (n - 1)
    let knots := e.knotVector
    (List.range n).map (fun i => basisAt knots e.gridMax i p x')

def KANEdge.eval (e : KANEdge) (x : Rat) : Rat :=
  let ws := e.basisWeights x
  let num := (e.controlPoints.zip ws).foldl (fun acc p => acc + p.1 * p.2) 0
  let den := ws.foldl (fun acc w => acc + w) 0
  if den = 0 then 0 else num / den

/-- Gradient wrt control points (for fixed input x): normalized basis weights. -/
def KANEdge.controlPointGrad (e : KANEdge) (x : Rat) : List Rat :=
  let ws := e.basisWeights x
  let den := ws.foldl (fun acc w => acc + w) 0
  if den = 0 then ws.map (fun _ => 0) else ws.map (fun w => w / den)

/-- Approximate input derivative via symmetric finite difference. -/
def KANEdge.inputGrad (e : KANEdge) (x : Rat) : Rat :=
  let span := gridSpan e
  let eps := if span = 0 then (1 : Rat) / 100 else span / 100
  let xLo := clampRat (x - eps) e.gridMin e.gridMax
  let xHi := clampRat (x + eps) e.gridMin e.gridMax
  let den := xHi - xLo
  if den = 0 then 0 else (e.eval xHi - e.eval xLo) / den

def KANEdge.symbolicSummary (e : KANEdge) : String :=
  match e.controlPoints with
  | [] => "0"
  | [a] => s!"{a}"
  | a :: b :: _ =>
      s!"{a} + ({b - a})*x"

private def defaultEdge : KANEdge :=
  { controlPoints := [0, 1], gridMin := -1, gridMax := 1, order := 3 }

structure KANLayer where
  inputDim : Nat
  outputDim : Nat
  edges : Array (Array KANEdge)
  deriving Repr

private def layerEdge (layer : KANLayer) (o i : Nat) : KANEdge :=
  let row := layer.edges.getD o #[]
  row.getD i defaultEdge

def KANLayer.forward (layer : KANLayer) (input : Array Rat) : Array Rat :=
  List.toArray <| (List.range layer.outputDim).map (fun o =>
      (List.range layer.inputDim).foldl
        (fun acc i => acc + (layerEdge layer o i).eval (arrayGetRat input i))
        0)

structure KANLayerGrad where
  edgeGrads : Array (Array KANEdgeGrad)
  deriving Repr

structure KANetwork where
  layers : List KANLayer
  deriving Repr

structure KANGradient where
  layerGrads : List KANLayerGrad
  deriving Repr

def KANetwork.forward (net : KANetwork) (input : Array Rat) : Array Rat :=
  net.layers.foldl (fun x layer => layer.forward x) input

private def layerControlGrad (layer : KANLayer) (input dOutput : Array Rat) : KANLayerGrad :=
  let rows :=
    (List.range layer.outputDim).map (fun o =>
      let upstream := arrayGetRat dOutput o
      let row := layer.edges.getD o #[]
      List.toArray <| (List.range row.size).map (fun i =>
        let e := row.getD i defaultEdge
        let grad := e.controlPointGrad (arrayGetRat input i)
        { controlPointGrad := grad.map (fun g => upstream * g) }))
  { edgeGrads := List.toArray rows }

private def layerInputGrad (layer : KANLayer) (input dOutput : Array Rat) : Array Rat :=
  List.toArray <| (List.range layer.inputDim).map (fun i =>
    (List.range layer.outputDim).foldl
      (fun acc o =>
        let upstream := arrayGetRat dOutput o
        let e := layerEdge layer o i
        acc + upstream * e.inputGrad (arrayGetRat input i))
      0)

private def forwardActivations (layers : List KANLayer) (input : Array Rat) : List (KANLayer × Array Rat) :=
  let rec go (rest : List KANLayer) (curr : Array Rat) (acc : List (KANLayer × Array Rat)) : List (KANLayer × Array Rat) :=
    match rest with
    | [] => acc.reverse
    | layer :: tl =>
        let next := layer.forward curr
        go tl next ((layer, curr) :: acc)
  go layers input []

/--
Layer-wise backward pass:
- control-point gradients are exact for the fixed B-spline basis values,
- input gradients use a symmetric finite-difference edge derivative.
-/
def KANetwork.backward (net : KANetwork) (input dOutput : Array Rat) : KANGradient :=
  let activations := forwardActivations net.layers input
  let rec back
      (actsRev : List (KANLayer × Array Rat))
      (upstream : Array Rat)
      (acc : List KANLayerGrad) : List KANLayerGrad :=
    match actsRev with
    | [] => acc
    | (layer, layerInput) :: tl =>
        let gLayer := layerControlGrad layer layerInput upstream
        let nextUpstream := layerInputGrad layer layerInput upstream
        back tl nextUpstream (gLayer :: acc)
  { layerGrads := back activations.reverse dOutput [] }

def KANetwork.symbolicSummary (net : KANetwork) (maxRows : Nat := 8) : List String :=
  let rows :=
    net.layers.foldl
      (fun acc layer =>
        acc ++ layer.edges.toList.foldl (fun acc2 row => acc2 ++ row.toList) [])
      []
  (rows.take (max 1 maxRows)).map (fun e => e.symbolicSummary)

/-- Build a dense KAN layer with homogeneous edge templates. -/
def denseLayer (inputDim outputDim : Nat) (template : KANEdge) : KANLayer :=
  let row := Array.replicate (max 1 inputDim) template
  { inputDim := max 1 inputDim, outputDim := max 1 outputDim, edges := Array.replicate (max 1 outputDim) row }

/-- Minimal default network used by Track A warm-start path. -/
def defaultKANetwork (inputDim outputDim : Nat) : KANetwork :=
  {
    layers :=
      [denseLayer (max 1 inputDim) (max 1 (inputDim / 2 + 1))
        { controlPoints := [0, 1, 0], gridMin := -2, gridMax := 2, order := 3}
      ,denseLayer (max 1 (inputDim / 2 + 1)) (max 1 outputDim)
        { controlPoints := [0, 1], gridMin := -2, gridMax := 2, order := 1}
      ]
  }

end KAN
end Differential
end Combinators
end LoF
end HeytingLean
