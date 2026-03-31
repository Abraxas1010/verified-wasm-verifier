import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

namespace HeytingLean.Geo.GQRE

/-- Parameters for the GQRE / Perona–Malik flow. -/
structure Params where
  /-- The conduction strength `α` in the GQRE Lagrangian. -/
  alpha : Float
  deriving Repr, Inhabited

/-- Background Euclidean metric on a 2D grid. -/
structure Metric2 where
  g : Matrix (Fin 2) (Fin 2) Float

/-- Discrete 2D scalar field (e.g. grayscale image). -/
abbrev Field2 := Array (Array Float)

/-- Discrete 2D gradient components on the same grid. -/
structure Grad2 where
  gx : Array (Array Float)
  gy : Array (Array Float)
  deriving Repr

namespace Field2

/-- Height (number of rows) of a discrete field. -/
def height (φ : Field2) : Nat :=
  φ.size

/-- Width (number of columns) of a discrete field, if nonempty. -/
def width (φ : Field2) : Nat :=
  match φ[0]? with
  | some row => row.size
  | none => 0

/-- Well‑formed fields have all rows of the same length. -/
def WellFormed (φ : Field2) : Prop :=
  match φ[0]? with
  | some row =>
      ∀ r ∈ φ.toList, r.size = row.size
  | none => True

end Field2

namespace Grad2

/-- Shape‑consistency predicate for a discrete gradient. -/
def WellFormed (g : Grad2) : Prop :=
  Field2.WellFormed g.gx ∧ Field2.WellFormed g.gy ∧
    g.gx.size = g.gy.size ∧
    (g.gx[0]?).bind (fun row => some row.size) =
      (g.gy[0]?).bind (fun row => some row.size)

end Grad2

def lagPoint (p : Params) (gx gy : Float) : Float :=
  - Float.log (1.0 + p.alpha * (gx * gx + gy * gy))

def action (p : Params) (gradX gradY : Field2) : Float := Id.run do
  let rows := Nat.min gradX.size gradY.size
  let mut acc : Float := 0.0
  for i in List.range rows do
    let rowX? := gradX[i]?
    let rowY? := gradY[i]?
    match rowX?, rowY? with
    | some rowX, some rowY =>
        let cols := Nat.min rowX.size rowY.size
        for j in List.range cols do
          let gx := rowX.getD j 0.0
          let gy := rowY.getD j 0.0
          acc := acc + lagPoint p gx gy
    | _, _ => ()
  pure (-0.5 * acc)

def lagMean (p : Params) (gradX gradY : Field2) : Float := Id.run do
  let rows := Nat.min gradX.size gradY.size
  if rows = 0 then
    pure 0.0
  else
    let mut count : Nat := 0
    let mut acc : Float := 0.0
    for i in List.range rows do
      let rowX? := gradX[i]?
      let rowY? := gradY[i]?
      match rowX?, rowY? with
      | some rowX, some rowY =>
          let cols := Nat.min rowX.size rowY.size
          for j in List.range cols do
            let gx := rowX.getD j 0.0
            let gy := rowY.getD j 0.0
            acc := acc + lagPoint p gx gy
            count := count + 1
      | _, _ => ()
    if count = 0 then
      pure 0.0
    else
      pure (acc / Float.ofNat count)

end HeytingLean.Geo.GQRE
