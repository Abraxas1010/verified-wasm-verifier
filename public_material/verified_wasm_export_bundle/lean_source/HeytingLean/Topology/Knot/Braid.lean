import Std
import HeytingLean.Topology.Knot.PlanarDiagram
import HeytingLean.Topology.Knot.PDGraph
import HeytingLean.Topology.Knot.Jones
import HeytingLean.Topology.Knot.TemperleyLieb

/-!
# Knot theory: closed braids (Phase 2, executable)

This module provides two executable views of a **closed braid** given by a braid word:

1. A conversion into the `PlanarDiagram` PD encoding (for Kauffman bracket evaluation).
2. A Temperley–Lieb evaluation for the same braid word using the standard skein mapping
   `crossing ↦ A·eᵢ + A⁻¹·1`.

The main purpose is to enable regression cross-checks of the bracket against a compositional
Temperley–Lieb computation on small examples.
-/

namespace HeytingLean
namespace Topology
namespace Knot

open Std

namespace Braid

open Reidemeister
open Kauffman
open TemperleyLieb

/-- A braid generator `σ_i` (or its inverse) on `n` strands. Indexing is 0-based. -/
structure Gen where
  i : Nat
  sign : CurlKind := .pos
deriving Repr, Inhabited, DecidableEq

namespace Gen

/-- Inverse braid generator: flips the crossing sign. -/
def inv (g : Gen) : Gen :=
  { g with sign := match g.sign with | .pos => .neg | .neg => .pos }

end Gen

namespace Word

/-- Word inverse: reverse the word and invert each generator. -/
def inv (gens : List Gen) : List Gen :=
  (gens.reverse.map Gen.inv)

end Word

private def markActive (n : Nat) (gens : List Gen) : Except String (Array Bool) := do
  let mut active : Array Bool := Array.replicate n false
  for g in gens do
    if g.i + 1 >= n then
      throw s!"braid generator index out of range: i={g.i} (n={n})"
    active := active.set! g.i true
    active := active.set! (g.i + 1) true
  return active

/-- Convert a closed braid word into a `PlanarDiagram` (PD encoding).

Convention for each crossing record `{a,b,c,d}`:
- `a` = top-left strand label,
- `b` = top-right strand label,
- `c` = bottom-right strand label,
- `d` = bottom-left strand label.

This aligns with `Kauffman`'s smoothing convention where:
- A-smoothing connects `(a,b)` and `(c,d)` (cap+cup, TL generator `eᵢ`),
- B-smoothing connects `(a,d)` and `(b,c)` (two verticals, TL identity on the two strands).
-/
def closurePlanarDiagram (n : Nat) (gens : List Gen) : Except String PlanarDiagram := do
  let active ← markActive n gens
  let freeLoops :=
    (List.range n).foldl (fun acc p => if active[p]! then acc else acc + 1) 0

  -- Fresh labels for the strand segments just above the first crossing ("top labels").
  let mut nextLbl : Nat := 0
  let mut top : Array Nat := Array.replicate n 0
  let mut cur : Array Nat := Array.replicate n 0
  for p in [0:n] do
    top := top.set! p nextLbl
    cur := cur.set! p nextLbl
    nextLbl := nextLbl + 1

  -- Build crossings from top to bottom.
  let mut cs : Array Crossing := #[]
  for g in gens do
    let i := g.i
    if i + 1 >= n then
      throw s!"closurePlanarDiagram: index out of range i={i} (n={n})"
    let inL := cur[i]!
    let inR := cur[i + 1]!
    let outL := nextLbl
    nextLbl := nextLbl + 1
    let outR := nextLbl
    nextLbl := nextLbl + 1
    -- We model crossing polarity via a PD mirror: swapping `b` and `d` interchanges A/B smoothings,
    -- hence swaps the skein coefficients. We choose the convention that `CurlKind.pos` corresponds
    -- to the braid generator whose closure has positive writhe under the Jones normalisation.
    cs :=
      cs.push <|
        match g.sign with
        | .pos => { a := inL, b := outR, c := outL, d := inR }
        | .neg => { a := inL, b := inR, c := outL, d := outR }
    -- Strands swap positions after a braid generator.
    cur := cur.set! i outR
    cur := cur.set! (i + 1) outL

  -- Close the braid: identify the final segment at each position with the corresponding top label.
  let mut ren : Std.HashMap Nat Nat := {}
  for p in [0:n] do
    ren := ren.insert cur[p]! top[p]!
  let rename (x : Nat) : Nat :=
    match ren[x]? with
    | some y => y
    | none => x
  let cs' :=
    cs.map (fun c =>
      { a := rename c.a, b := rename c.b, c := rename c.c, d := rename c.d })

  let dgm : PlanarDiagram := { freeLoops, crossings := cs' }
  PlanarDiagram.validate dgm
  return dgm

/-- Convert a closed braid word into a sign-enriched graph for Jones-style normalisation (toy). -/
def closureSignedPDGraph (n : Nat) (gens : List Gen) : Except String Kauffman.SignedPDGraph := do
  let dgm ← closurePlanarDiagram n gens
  let g ← PDGraph.ofPlanarDiagram dgm
  let sign : Array CurlKind := gens.toArray.map (fun g => g.sign)
  return { graph := g, sign }

/-- Temperley–Lieb evaluation of a braid word via `σᵢ ↦ A·eᵢ + A⁻¹·1` and `σᵢ⁻¹ ↦ A⁻¹·eᵢ + A·1`.

This is aligned with the PD encoding convention above, where `.pos` uses the mirrored crossing. -/
def evalTL (n : Nat) (gens : List Gen) : Except String LaurentPoly := do
  let mut acc : Diagram.Expr n := Diagram.Expr.ofDiagram (Diagram.id n) 1
  for g in gens do
    let e ← Diagram.gen n g.i
    let step : Diagram.Expr n :=
      match g.sign with
      | .pos =>
          Diagram.Expr.add
            (Diagram.Expr.ofDiagram e Kauffman.Ainv)
            (Diagram.Expr.ofDiagram (Diagram.id n) Kauffman.A)
      | .neg =>
          Diagram.Expr.add
            (Diagram.Expr.ofDiagram e Kauffman.A)
            (Diagram.Expr.ofDiagram (Diagram.id n) Kauffman.Ainv)
    acc ← Diagram.Expr.mul acc step
  Diagram.Expr.eval acc

/-- Kauffman bracket of the closed braid, via the PD encoding. -/
def bracketPD (n : Nat) (gens : List Gen) : Except String LaurentPoly := do
  let dgm ← closurePlanarDiagram n gens
  Kauffman.bracket dgm

end Braid

end Knot
end Topology
end HeytingLean
