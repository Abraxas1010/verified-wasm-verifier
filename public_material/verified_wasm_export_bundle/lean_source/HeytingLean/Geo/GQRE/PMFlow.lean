import Mathlib.Data.Real.Basic
import HeytingLean.Geo.GQRE.Core

namespace HeytingLean.Geo.GQRE

open Field2

/-- Forward-difference gradient on a 2D grid with simple
Neumann-style (copy) boundary conditions. -/
def grad (φ : Field2) : Grad2 := Id.run do
  let h := Field2.height φ
  let w := Field2.width φ
  let mut gxArr : Array (Array Float) := Array.mkEmpty h
  let mut gyArr : Array (Array Float) := Array.mkEmpty h
  for i in List.range h do
    let row := φ[i]!
    let mut rowGx : Array Float := Array.mkEmpty w
    let mut rowGy : Array Float := Array.mkEmpty w
    for j in List.range w do
      let v := row.getD j 0.0
      let vRight :=
        if j + 1 < w then
          row.getD (j + 1) v
        else
          v
      let vDown :=
        if i + 1 < h then
          let rowNext := φ[i + 1]!
          rowNext.getD j v
        else
          v
      rowGx := rowGx.push (vRight - v)
      rowGy := rowGy.push (vDown - v)
    gxArr := gxArr.push rowGx
    gyArr := gyArr.push rowGy
  pure { gx := gxArr, gy := gyArr }

/-- Pointwise squared norm `|∇φ|^2` of a discrete gradient. -/
def gradNormSq (g : Grad2) : Field2 := Id.run do
  let rows := Nat.min g.gx.size g.gy.size
  let mut out : Field2 := Array.mkEmpty rows
  for i in List.range rows do
    let rowX := g.gx[i]!
    let rowY := g.gy[i]!
    let cols := Nat.min rowX.size rowY.size
    let mut rowOut : Array Float := Array.mkEmpty cols
    for j in List.range cols do
      let gx := rowX.getD j 0.0
      let gy := rowY.getD j 0.0
      rowOut := rowOut.push (gx * gx + gy * gy)
    out := out.push rowOut
  pure out

/-- Conduction function ρ(s) = 1 / (1 + α s). -/
def rho (p : Params) (s : Float) : Float :=
  1.0 / (1.0 + p.alpha * s)

/-- Pointwise product of two scalar fields on the same grid. -/
def mulField (a b : Field2) : Field2 := Id.run do
  let rows := Nat.min a.size b.size
  let mut out : Field2 := Array.mkEmpty rows
  for i in List.range rows do
    let rowA := a[i]!
    let rowB := b[i]!
    let cols := Nat.min rowA.size rowB.size
    let mut rowOut : Array Float := Array.mkEmpty cols
    for j in List.range cols do
      let va := rowA.getD j 0.0
      let vb := rowB.getD j 0.0
      rowOut := rowOut.push (va * vb)
    out := out.push rowOut
  pure out

/-- Divergence of a 2D vector field (vx, vy) using a simple
backward-difference scheme with zero-flux boundaries. -/
def divergence (vx vy : Field2) : Field2 := Id.run do
  let h := Nat.min vx.size vy.size
  let w := Nat.min (Field2.width vx) (Field2.width vy)
  let mut out : Field2 := Array.mkEmpty h
  for i in List.range h do
    let rowX := vx[i]!
    let rowY := vy[i]!
    let mut rowOut : Array Float := Array.mkEmpty w
    for j in List.range w do
      let xHere := rowX.getD j 0.0
      let xPrev :=
        if j = 0 then
          0.0
        else
          rowX.getD (j - 1) 0.0
      let yHere := rowY.getD j 0.0
      let yPrev :=
        if i = 0 then
          0.0
        else
          let rowPrev := vy[i - 1]!
          rowPrev.getD j 0.0
      let div := (xHere - xPrev) + (yHere - yPrev)
      rowOut := rowOut.push div
    out := out.push rowOut
  pure out

/-- One explicit Perona–Malik update step
`φ^{t+1} = φ^t + Δt * α * ∇·(ρ(|∇φ^t|^2) ∇φ^t)`. -/
def pmStep (p : Params) (dt : Float) (φ : Field2) : Field2 := Id.run do
  let h := Field2.height φ
  let w := Field2.width φ
  if h = 0 ∨ w = 0 then
    pure φ
  else
    let g := grad φ
    let nrm := gradNormSq g
    -- Scale gradient by ρ(|∇φ|^2).
    let mut vx : Field2 := Array.mkEmpty h
    let mut vy : Field2 := Array.mkEmpty h
    for i in List.range h do
      let rowX := g.gx[i]!
      let rowY := g.gy[i]!
      let rowN := nrm[i]!
      let cols := Nat.min (Nat.min rowX.size rowY.size) rowN.size
      let mut rowVx : Array Float := Array.mkEmpty cols
      let mut rowVy : Array Float := Array.mkEmpty cols
      for j in List.range cols do
        let s := rowN.getD j 0.0
        let r := rho p s
        let gx := rowX.getD j 0.0
        let gy := rowY.getD j 0.0
        rowVx := rowVx.push (r * gx)
        rowVy := rowVy.push (r * gy)
      vx := vx.push rowVx
      vy := vy.push rowVy
    let div := divergence vx vy
    -- Apply update step.
    let mut out : Field2 := Array.mkEmpty h
    for i in List.range h do
      let row := φ[i]!
      let rowDiv :=
        if i < div.size then div[i]! else #[]
      let cols := Nat.min row.size rowDiv.size
      let mut rowOut : Array Float := Array.mkEmpty cols
      for j in List.range cols do
        let v := row.getD j 0.0
        let d := rowDiv.getD j 0.0
        rowOut := rowOut.push (v + dt * p.alpha * d)
      out := out.push rowOut
    pure out

/-- Iterate the Perona–Malik step `iters` times starting from `φ₀`. -/
def pmIter (p : Params) (dt : Float) (iters : Nat) (φ₀ : Field2) : Field2 :=
  Nat.recOn iters φ₀ (fun _ acc => pmStep p dt acc)

/-- Full trajectory of the Perona–Malik flow:
`iters + 1` snapshots including the initial field. -/
def pmTrajectory (p : Params) (dt : Float) (iters : Nat) (φ₀ : Field2) :
    Array Field2 := Id.run do
  let mut out : Array Field2 := #[φ₀]
  let mut cur := φ₀
  for _k in List.range iters do
    let nxt := pmStep p dt cur
    out := out.push nxt
    cur := nxt
  pure out

/-- One-step stability check based on GQRE action difference.
Returns `true` if `|S(φ') - S(φ)| ≤ tol`. -/
def stableStep (p : Params) (dt : Float) (φ : Field2) (tol : Float) : Bool :=
  let g₀ := grad φ
  let S₀ := action p g₀.gx g₀.gy
  let φ' := pmStep p dt φ
  let g₁ := grad φ'
  let S₁ := action p g₁.gx g₁.gy
  let diff := Float.abs (S₁ - S₀)
  decide (diff ≤ tol)

end HeytingLean.Geo.GQRE

