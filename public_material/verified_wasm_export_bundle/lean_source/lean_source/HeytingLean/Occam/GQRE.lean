import Mathlib.Data.Real.Basic
import HeytingLean.Geo.GQRE.Core
import HeytingLean.Geo.GQRE.PMFlow
import HeytingLean.Logic.Nucleus.R_GQRE

/-!
# GQRE / Perona–Malik scoring hooks for Occam

This module provides lightweight scoring helpers for the GQRE lens:

* `gqreAction` and `GQREGain` on discrete fields;
* a simple edge detector and Jaccard-based edge preservation metric;
* an average GQRE Lagrangian `LgqreMean` suitable as an Occam term.

The logical Occam operators themselves live in
`HeytingLean.Epistemic.Occam`.  Here we only add numerical scores
that can be combined with existing Occam / PSR / Dialectic lenses.
-/

namespace HeytingLean
namespace Occam
namespace GQRE

open HeytingLean.Geo.GQRE

/-- Re-expose the GQRE action on fields under the Occam namespace. -/
def gqreAction (p : Params) (φ : Field2) : Float :=
  HeytingLean.Logic.Nucleus.GQRE.gqreAction p φ

/-- GQRE action gain between input and output fields. -/
def GQREGain (p : Params) (φIn φOut : Field2) : Float :=
  gqreAction p φOut - gqreAction p φIn

/-- Mean GQRE Lagrangian `L = - log (1 + α |∇φ|^2)` over the grid. -/
def LgqreMean (p : Params) (φ : Field2) : Float :=
  let g := grad φ
  lagMean p g.gx g.gy

/-- Edge set extracted from a field as the indices of the top-`q`
fraction of gradient magnitudes.  This is a simple, deterministic
proxy for “sharp contours”. -/
def Edges (φ : Field2) (q : Float) : Std.HashSet (Nat × Nat) := Id.run do
  let g := grad φ
  let nrm := gradNormSq g
  let mut vals : Array (Float × (Nat × Nat)) := #[]
  let h := nrm.size
  for i in List.range h do
    let row := nrm[i]!
    let w := row.size
    for j in List.range w do
      let v := row.getD j 0.0
      vals := vals.push (v, (i, j))
  let total := vals.size
  let mut out : Std.HashSet (Nat × Nat) := {}
  if total = 0 then
    pure out
  else
    let qClamped :=
      if q ≤ 0.0 then 0.0
      else if q ≥ 1.0 then 1.0
      else q
    let kApprox : Float := Float.ofNat total * qClamped
    let k0 : Nat := kApprox.toUInt64.toNat
    let k : Nat :=
      if qClamped ≤ 0.0 then
        0
      else
        Nat.max 1 k0
    let mut arr := vals
    -- Naive partial selection: sort descending by value and take first k.
    arr := arr.qsort (fun a b => a.fst > b.fst)
    for idx in List.range (Nat.min k arr.size) do
      let (_, ij) := arr[idx]!
      out := out.insert ij
    pure out

/-- Jaccard index between two finite edge sets. -/
def jaccard (A B : Std.HashSet (Nat × Nat)) : Float := Id.run do
  if A.isEmpty ∧ B.isEmpty then
    pure 1.0
  else
    let mut inter : Nat := 0
    let mut union : Nat := 0
    let mut seen : Std.HashSet (Nat × Nat) := {}
    for a in A.toArray do
      union := union + 1
      seen := seen.insert a
      if B.contains a then
        inter := inter + 1
    for b in B.toArray do
      if ¬ seen.contains b then
        union := union + 1
        seen := seen.insert b
    if union = 0 then
      pure 0.0
    else
      pure (Float.ofNat inter / Float.ofNat union)

/-- Edge preservation score between input and output fields, using
the Jaccard index of top-`q`% gradient-magnitude edge sets. -/
def edgePreserve (φIn φOut : Field2) (q : Float := 0.1) : Float :=
  let edgesIn  := Edges φIn q
  let edgesOut := Edges φOut q
  jaccard edgesIn edgesOut

end GQRE
end Occam
end HeytingLean
