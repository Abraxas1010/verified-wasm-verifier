import Std
import HeytingLean.Topology.Knot.Bracket

/-!
# Knot theory: Temperley–Lieb diagrams (Phase 2, executable)

This module implements an **executable** Temperley–Lieb diagram calculus:

- A diagram on `n` strands is represented as an involution (a matching) on `2*n` boundary
  endpoints (top `0..n-1`, bottom `n..2*n-1`), plus an explicit count of internal closed loops.
- Composition stacks two diagrams (glues bottom of the first to top of the second), producing
  a new diagram and counting any newly created internal loops.
- A (toy) closure evaluation maps a diagram to a Laurent polynomial via the Kauffman bracket
  loop factor `d = -A^2 - A^{-2}`.

We include an (optional) planarity/noncrossing check; the algebraic operations themselves
do not require planarity but the intended Temperley–Lieb subcategory is planar.
-/

namespace HeytingLean
namespace Topology
namespace Knot

open Std

namespace TemperleyLieb

open Kauffman

/-- A (toy) Temperley–Lieb diagram on `n` strands. -/
structure Diagram (n : Nat) where
  loops : Nat := 0
  nbr : Array Nat := #[]
deriving Repr, Inhabited, DecidableEq

namespace Diagram

def key {n : Nat} (d : Diagram n) : List Nat :=
  d.loops :: d.nbr.toList

def numEndpoints (n : Nat) : Nat :=
  2 * n

def validate {n : Nat} (d : Diagram n) : Except String Unit := do
  let m := numEndpoints n
  if d.nbr.size != m then
    throw s!"nbr length {d.nbr.size} (expected {m})"
  for i in [0:m] do
    let j := d.nbr[i]!
    if j >= m then
      throw s!"nbr[{i}]={j} out of range (m={m})"
    if j == i then
      throw s!"nbr has a fixed point at {i}"
    if d.nbr[j]! != i then
      throw s!"nbr not an involution at {i} ↦ {j} ↦ {d.nbr[j]!}"

private def circlePos (n : Nat) (idx : Nat) : Nat :=
  if idx < n then idx else (2 * n - 1 - idx)

private def chords {n : Nat} (d : Diagram n) : List (Nat × Nat) :=
  let m := numEndpoints n
  let pos := circlePos n
  (List.range m).foldl
    (fun acc i =>
      let j := d.nbr[i]!
      if i < j then
        let a := pos i
        let b := pos j
        if a < b then (a, b) :: acc else (b, a) :: acc
      else
        acc)
    []

private def chordsCross (p q r s : Nat) : Bool :=
  (p < r && r < q && q < s) || (r < p && p < s && s < q)

/-- Check whether the boundary matching is planar (noncrossing) in the standard TL sense. -/
def isPlanar {n : Nat} (d : Diagram n) : Except String Bool := do
  validate d
  let cs := chords d
  let rec anyCross : List (Nat × Nat) → Bool
    | [] => false
    | (p, q) :: rest =>
        let crosses :=
          rest.any (fun (r, s) => chordsCross p q r s)
        crosses || anyCross rest
  return !anyCross cs

/-- The identity diagram on `n` strands (all vertical pairings). -/
def id (n : Nat) : Diagram n :=
  let m := numEndpoints n
  { loops := 0
    nbr :=
      Array.ofFn (n := m) (fun idx =>
        let i := idx.1
        if i < n then
          n + i
        else
          i - n) }

/-- The Temperley–Lieb generator diagram `e_i` (cap on top, cup on bottom). -/
def gen (n i : Nat) : Except String (Diagram n) := do
  if i + 1 >= n then
    throw s!"gen: need i+1 < n (n={n}, i={i})"
  let nbr :=
    Array.ofFn (n := numEndpoints n) (fun idx =>
      let k := idx.1
      if k == i then
        i + 1
      else if k == i + 1 then
        i
      else if k == n + i then
        n + (i + 1)
      else if k == n + (i + 1) then
        n + i
      else if k < n then
        n + k
      else
        k - n)
  return { loops := 0, nbr }

private def addNeighbor
    (adj : Array (Nat × Nat)) (u v : Nat) (noneVal : Nat) : Except String (Array (Nat × Nat)) := do
  if u >= adj.size then
    throw "addNeighbor: index out of bounds"
  let (a, b) := adj[u]!
  if a == noneVal then
    return adj.set! u (v, b)
  else if b == noneVal then
    return adj.set! u (a, v)
  else
    throw "addNeighbor: degree > 2"

private def addEdge
    (adj : Array (Nat × Nat)) (u v : Nat) (noneVal : Nat) : Except String (Array (Nat × Nat)) := do
  let adj ← addNeighbor adj u v noneVal
  addNeighbor adj v u noneVal

private def isExternal (n : Nat) (v : Nat) : Bool :=
  v < n || v >= 3 * n

private def outIndex (n : Nat) (v : Nat) : Except String Nat := do
  if v < n then
    return v
  if v >= 3 * n && v < 4 * n then
    return n + (v - 3 * n)
  throw "outIndex: not an external vertex"

/-- Stack/compose two diagrams on `n` strands, counting any internal loops created by the stacking. -/
def compose {n : Nat} (d₁ d₂ : Diagram n) : Except String (Diagram n) := do
  validate d₁
  validate d₂
  if n = 0 then
    return { loops := d₁.loops + d₂.loops, nbr := #[] }

  let m := numEndpoints n
  let vCount := 2 * m
  let noneVal := vCount
  let mut adj : Array (Nat × Nat) := Array.replicate vCount (noneVal, noneVal)

  -- Matching edges of `d₁` (0..m-1)
  for i in [0:m] do
    let j := d₁.nbr[i]!
    if i < j then
      adj ← addEdge adj i j noneVal

  -- Matching edges of `d₂` (shifted by m)
  for i in [0:m] do
    let j := d₂.nbr[i]!
    if i < j then
      adj ← addEdge adj (m + i) (m + j) noneVal

  -- Glue bottom of `d₁` (n..2n-1) to top of `d₂` (m..m+n-1).
  for p in [0:n] do
    adj ← addEdge adj (n + p) (m + p) noneVal

  let mut visited : Array Bool := Array.replicate vCount false
  let mut outNbr : Array Nat := Array.replicate m 0

  -- Follow paths between external endpoints to determine the resulting boundary matching.
  for e in [0:vCount] do
    if isExternal n e && !visited[e]! then
      let start := e
      let mut prev := noneVal
      let mut cur := e
      while true do
        visited := visited.set! cur true
        let (a, b) := adj[cur]!
        let nxt :=
          if prev == noneVal then
            if a != noneVal then a else b
          else if a == prev then
            b
          else
            a
        if nxt == noneVal then
          throw "compose: unexpected dead-end in adjacency"
        prev := cur
        cur := nxt
        if isExternal n cur then
          visited := visited.set! cur true
          let i ← outIndex n start
          let j ← outIndex n cur
          outNbr := outNbr.set! i j
          outNbr := outNbr.set! j i
          break

  -- Any remaining unvisited vertices form internal cycles (loops).
  let mut newLoops := 0
  for v in [0:vCount] do
    if !visited[v]! then
      newLoops := newLoops + 1
      let start := v
      let mut prev := noneVal
      let mut cur := v
      while true do
        visited := visited.set! cur true
        let (a, b) := adj[cur]!
        let nxt :=
          if prev == noneVal then a
          else if a == prev then b else a
        if nxt == noneVal then
          throw "compose: cycle walk hit dead-end"
        prev := cur
        cur := nxt
        if cur == start then
          break

  return { loops := d₁.loops + d₂.loops + newLoops, nbr := outNbr }

private def closureNeighbor (n : Nat) (idx : Nat) : Nat :=
  if idx < n then n + idx else idx - n

/-- Close a diagram by connecting each top endpoint to the corresponding bottom endpoint. -/
def closeLoops {n : Nat} (d : Diagram n) : Except String Nat := do
  validate d
  let m := numEndpoints n
  if m = 0 then
    return d.loops
  let mut visited : Array Bool := Array.replicate m false
  let mut loops := 0
  for i in [0:m] do
    if !visited[i]! then
      loops := loops + 1
      let start := i
      let mut prev := m
      let mut cur := i
      while true do
        visited := visited.set! cur true
        let nMatch := d.nbr[cur]!
        let nClose := closureNeighbor n cur
        let nxt :=
          if prev == m then nMatch
          else if prev == nMatch then nClose else nMatch
        prev := cur
        cur := nxt
        if cur == start then
          break
  return d.loops + loops

/-- Evaluate the closure of a diagram as a Laurent polynomial using the Kauffman loop factor. -/
def evalClosed {n : Nat} (d : Diagram n) : Except String LaurentPoly := do
  let loops ← closeLoops d
  if loops = 0 then
    return 1
  return Kauffman.d ^ (loops - 1)

/-- A finite linear combination of TL diagrams with Laurent-polynomial coefficients. -/
structure Expr (n : Nat) where
  terms : List (Diagram n × LaurentPoly) := []
deriving Inhabited, Repr

namespace Expr

private def absorbLoops {n : Nat} (d : Diagram n) : (Diagram n × LaurentPoly) :=
  if d.loops = 0 then
    (d, 1)
  else
    ({ d with loops := 0 }, Kauffman.d ^ d.loops)

private def insertTerm {n : Nat} (d : Diagram n) (c : LaurentPoly) :
    List (Diagram n × LaurentPoly) → List (Diagram n × LaurentPoly)
  | [] =>
      if c.isZero then [] else [(d, c)]
  | (d', c') :: xs =>
      if d = d' then
        let c'' := c' + c
        if c''.isZero then xs else (d', c'') :: xs
      else
        (d', c') :: insertTerm d c xs

def zero (n : Nat) : Expr n :=
  { terms := [] }

def ofDiagram {n : Nat} (d : Diagram n) (c : LaurentPoly := 1) : Expr n :=
  if c.isZero then
    zero n
  else
    let (d', factor) := absorbLoops d
    { terms := [(d', factor * c)] }

def add {n : Nat} (x y : Expr n) : Expr n :=
  { terms := y.terms.foldl (fun acc (d, c) => insertTerm d c acc) x.terms }

def mul {n : Nat} (x y : Expr n) : Except String (Expr n) := do
  let mut acc : List (Diagram n × LaurentPoly) := []
  for (d₁, c₁) in x.terms do
    for (d₂, c₂) in y.terms do
      let d ← Diagram.compose d₁ d₂
      let (d', factor) := absorbLoops d
      acc := insertTerm d' (factor * c₁ * c₂) acc
  return { terms := acc }

def eval {n : Nat} (x : Expr n) : Except String LaurentPoly := do
  let mut acc : LaurentPoly := 0
  for (d, c) in x.terms do
    let v ← Diagram.evalClosed d
    acc := acc + (c * v)
  return acc

private def lexLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | a :: as, b :: bs =>
      if a < b then true else if a > b then false else lexLt as bs

private def diagramLt {n : Nat} (a b : Diagram n) : Bool :=
  lexLt a.key b.key

private def insertSorted {n : Nat} (t : Diagram n × LaurentPoly) :
    List (Diagram n × LaurentPoly) → List (Diagram n × LaurentPoly)
  | [] => [t]
  | x :: xs =>
      if diagramLt t.1 x.1 then
        t :: x :: xs
      else
        x :: insertSorted t xs

/-- Deterministic ordering of terms (useful for regression checks). -/
def sortedTerms {n : Nat} (x : Expr n) : List (Diagram n × LaurentPoly) :=
  x.terms.foldl (fun acc t => insertSorted t acc) []

end Expr

end Diagram

end TemperleyLieb

end Knot
end Topology
end HeytingLean
