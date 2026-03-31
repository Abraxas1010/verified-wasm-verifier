import HeytingLean.Topology.Knot.Bracket
import HeytingLean.Topology.Knot.Reidemeister

/-!
# Knot theory: Jones normalisation (toy, executable)

The Kauffman bracket is invariant under Reidemeister II/III (regular isotopy) and transforms
by a known scaling factor under Reidemeister I. For oriented diagrams, the standard Jones
normalisation multiplies by `(-A)^{-3 w(D)}` where `w(D)` is the writhe (sum of crossing signs),
yielding an ambient-isotopy invariant.

This module provides a minimal *executable* version of that normalisation by enriching a
`PDGraph` with an explicit sign per crossing.
-/

namespace HeytingLean
namespace Topology
namespace Knot

open Std

namespace Kauffman

open Reidemeister

/-- A PD graph together with a sign (`pos/neg`) for each crossing (toy oriented data). -/
structure SignedPDGraph where
  graph : PDGraph
  sign : Array CurlKind
deriving Repr, Inhabited

namespace SignedPDGraph

def validate (s : SignedPDGraph) : Except String Unit := do
  PDGraph.validate s.graph
  if s.sign.size != s.graph.n then
    throw s!"sign array length {s.sign.size} (expected {s.graph.n})"

def writhe (s : SignedPDGraph) : Int :=
  s.sign.foldl (fun acc k => acc + match k with | .pos => 1 | .neg => -1) 0

private def normCoeff (w : Int) : Int :=
  if w % 2 = 0 then 1 else -1

/-- The normalisation factor `(-A)^{-3w}` as a Laurent monomial `coeff * A^exp`. -/
def normFactor (w : Int) : LaurentPoly :=
  LaurentPoly.mon ((-3 : Int) * w) (normCoeff w)

/-- Normalised bracket (Jones-style), as a Laurent polynomial in `A` (toy). -/
def normalizedBracket (s : SignedPDGraph) : Except String LaurentPoly := do
  validate s
  let b ← Kauffman.bracketGraph s.graph
  return (normFactor s.writhe) * b

private def pop1 {α} (a : Array α) : Except String (Array α) := do
  if a.isEmpty then
    throw "pop1: empty array"
  return a.extract 0 (a.size - 1)

private def pop2 {α} (a : Array α) : Except String (Array α) := do
  if a.size < 2 then
    throw "pop2: need at least 2 elements"
  return a.extract 0 (a.size - 2)

def r1Add (s : SignedPDGraph) (x : Nat) (kind : CurlKind) : Except String SignedPDGraph := do
  let g' ← Reidemeister.r1Add s.graph x kind
  return { graph := g', sign := s.sign.push kind }

def r1RemoveLast (s : SignedPDGraph) (kind : CurlKind) : Except String SignedPDGraph := do
  validate s
  if s.sign.isEmpty then
    throw "r1RemoveLast: empty sign array"
  let last := s.sign[s.sign.size - 1]!
  if last != kind then
    throw "r1RemoveLast: sign kind mismatch"
  let g' ← Reidemeister.r1RemoveLast s.graph kind
  let sign' ← pop1 s.sign
  return { graph := g', sign := sign' }

def r2Add (s : SignedPDGraph) (x u : Nat) : Except String SignedPDGraph := do
  let g' ← Reidemeister.r2Add s.graph x u
  let sign' := (s.sign.push .pos).push .neg
  return { graph := g', sign := sign' }

def r2RemoveLast (s : SignedPDGraph) : Except String SignedPDGraph := do
  validate s
  let g' ← Reidemeister.r2RemoveLast s.graph
  let sign' ← pop2 s.sign
  return { graph := g', sign := sign' }

def r3BraidLeft (s : SignedPDGraph) (x u w : Nat) : Except String SignedPDGraph := do
  validate s
  let g' ← Reidemeister.r3BraidLeft s.graph x u w
  let sign' := ((s.sign.push .pos).push .pos).push .pos
  return { graph := g', sign := sign' }

def r3BraidRight (s : SignedPDGraph) (x u w : Nat) : Except String SignedPDGraph := do
  validate s
  let g' ← Reidemeister.r3BraidRight s.graph x u w
  let sign' := ((s.sign.push .pos).push .pos).push .pos
  return { graph := g', sign := sign' }

end SignedPDGraph

end Kauffman

end Knot
end Topology
end HeytingLean
