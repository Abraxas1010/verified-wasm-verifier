/-
  Wolfram Physics Project: Universe 1867 Formalization

  Source: https://www.wolframphysics.org/universes/wm1867/

  This file formalizes Universe 1867 from the Wolfram Physics Project Registry
  of Notable Universes. The hypergraph rewriting rule and initial conditions
  are directly transcribed from the official Wolfram Language specification.

  Rule: {{{1, 2}, {2, 3}} → {{2, 3}, {2, 3}, {3, 4}, {1, 3}}}
  Initial: {{1, 1}, {1, 1}}
  Steps: 7 generations

  IMPORTANT: WolframModel semantics apply ALL non-overlapping matches per
  generation simultaneously. This formalization implements that parallel
  rewriting semantics, not sequential single-match application.

  Reference results from Wolfram:
  - 7 generations
  - 74 total events (rule applications)
  - 150 final edges
  - 75 vertices
-/

namespace HeytingLean.WolframPhysics

/-- A hyperedge is an ordered pair of vertices (binary relation) -/
structure Hyperedge where
  src : Nat
  tgt : Nat
deriving DecidableEq, Repr, Inhabited, BEq

instance : ToString Hyperedge where
  toString e := s!"({e.src}, {e.tgt})"

/-- A hypergraph is a list of hyperedges -/
abbrev Hypergraph := List Hyperedge

/-- Universe 1867 initial condition: {{1, 1}, {1, 1}} (two self-loops on vertex 1) -/
def universe1867_initial : Hypergraph :=
  [⟨1, 1⟩, ⟨1, 1⟩]

/-- Get the maximum vertex ID in a hypergraph -/
def maxVertex (g : Hypergraph) : Nat :=
  g.foldl (fun acc e => max acc (max e.src e.tgt)) 0

/-- A match is a pair of edge indices where e1.tgt = e2.src -/
structure Match where
  idx1 : Nat  -- Index of first edge
  idx2 : Nat  -- Index of second edge
deriving DecidableEq, Repr

/-- Find ALL valid matches in the hypergraph (for parallel application)
    A match occurs when edge i has target equal to edge j's source (i ≠ j) -/
def findAllMatches (g : Hypergraph) : List Match := Id.run do
  let mut result : List Match := []
  for i in [:g.length] do
    for j in [:g.length] do
      if i != j then
        if let (some e1, some e2) := (g[i]?, g[j]?) then
          if e1.tgt == e2.src then
            result := ⟨i, j⟩ :: result
  return result.reverse

/-- Apply Universe 1867 rule to a matched pair of edges:
    {{1, 2}, {2, 3}} → {{2, 3}, {2, 3}, {3, 4}, {1, 3}}

    Given edges (a→b) and (b→c), produces:
    - (b→c) [kept]
    - (b→c) [duplicate]
    - (c→fresh) [new vertex]
    - (a→c) [shortcut]
-/
def applyRule (e1 e2 : Hyperedge) (fresh : Nat) : List Hyperedge :=
  let a := e1.src
  let b := e1.tgt  -- = e2.src by matching condition
  let c := e2.tgt
  [⟨b, c⟩, ⟨b, c⟩, ⟨c, fresh⟩, ⟨a, c⟩]

/-- Check if two matches overlap (share an edge index) -/
def matchesOverlap (m1 m2 : Match) : Bool :=
  m1.idx1 == m2.idx1 || m1.idx1 == m2.idx2 ||
  m1.idx2 == m2.idx1 || m1.idx2 == m2.idx2

/-- Select non-overlapping matches with specific ordering
    WolframModel uses "RuleOrdering" -> "OldestEdgeFirst" by default
    This means matches involving lower-indexed edges are prioritized -/
def selectNonOverlapping (matchList : List Match) : List Match := Id.run do
  -- Sort by minimum edge index to prioritize oldest edges
  let sorted := matchList.toArray.qsort (fun m1 m2 =>
    min m1.idx1 m1.idx2 < min m2.idx1 m2.idx2 ||
    (min m1.idx1 m1.idx2 == min m2.idx1 m2.idx2 &&
     max m1.idx1 m1.idx2 < max m2.idx1 m2.idx2))
  let mut selected : List Match := []
  for m in sorted.toList do
    let overlaps := selected.any (matchesOverlap m ·)
    if !overlaps then
      selected := m :: selected
  return selected.reverse

/-- Apply one generation: find all matches, select non-overlapping, apply in parallel -/
def stepGeneration (g : Hypergraph) : Hypergraph × Nat := Id.run do
  let allMatches := findAllMatches g
  let selected := selectNonOverlapping allMatches
  if selected.isEmpty then
    return (g, 0)

  -- Collect indices of edges consumed by matches
  let mut usedIndices : List Nat := []
  for m in selected do
    usedIndices := m.idx1 :: m.idx2 :: usedIndices

  -- Keep edges not consumed
  let mut remaining : Hypergraph := []
  for i in [:g.length] do
    if !usedIndices.contains i then
      if let some e := g[i]? then
        remaining := remaining ++ [e]

  -- Apply rules to all selected matches
  let mut fresh := maxVertex g + 1
  let mut newEdges : Hypergraph := []
  for m in selected do
    if let (some e1, some e2) := (g[m.idx1]?, g[m.idx2]?) then
      newEdges := newEdges ++ applyRule e1 e2 fresh
      fresh := fresh + 1

  return (remaining ++ newEdges, selected.length)

/-- Evolve for n generations, returning final state and total event count -/
def evolveGenerations (g : Hypergraph) (n : Nat) : Hypergraph × Nat :=
  match n with
  | 0 => (g, 0)
  | n + 1 =>
      let (g', events) := stepGeneration g
      let (final, moreEvents) := evolveGenerations g' n
      (final, events + moreEvents)

/-- Evolve for n generations, returning all intermediate states -/
def evolveStates (g : Hypergraph) (n : Nat) : List Hypergraph :=
  match n with
  | 0 => [g]
  | n + 1 =>
      let (g', _) := stepGeneration g
      g :: evolveStates g' n

/-- Universe 1867 after 7 generations -/
def universe1867_gen7 : Hypergraph × Nat :=
  evolveGenerations universe1867_initial 7

/-- Count edges in hypergraph -/
def edgeCount (g : Hypergraph) : Nat := g.length

/-- Count unique vertices in hypergraph -/
def vertexCount (g : Hypergraph) : Nat :=
  let vertices := g.foldl (fun acc e => acc ++ [e.src, e.tgt]) []
  vertices.eraseDups.length

-- ============================================
-- Verified Properties
-- ============================================

/-- Initial state has exactly 2 edges -/
theorem initial_edge_count : edgeCount universe1867_initial = 2 := rfl

/-- Initial state has exactly 1 unique vertex -/
theorem initial_vertex_count : vertexCount universe1867_initial = 1 := rfl

/-- The rule always produces exactly 4 new edges -/
theorem rule_produces_four_edges (e1 e2 : Hyperedge) (fresh : Nat) :
    (applyRule e1 e2 fresh).length = 4 := rfl

/-- Self-loops match with themselves: (1,1) and (1,1) form a valid match -/
theorem self_loops_match :
    let g := universe1867_initial
    let matchList := findAllMatches g
    matchList.length > 0 := by native_decide

-- ============================================
-- Evaluation (verify against Wolfram results)
-- ============================================

-- These should match Wolfram's output:
-- 7 generations, 74 events, 150 edges, 75 vertices

#eval edgeCount universe1867_initial  -- Expected: 2
#eval vertexCount universe1867_initial  -- Expected: 1

#eval let (g, events) := universe1867_gen7
      (edgeCount g, events, vertexCount g)
-- Expected: (150, 74, 75)

-- Show evolution step by step
#eval (evolveStates universe1867_initial 3).map edgeCount
-- Shows edge count at each generation

-- ============================================
-- Bridge Protocol Export
-- ============================================

/-- Convert hypergraph to list of pairs for export -/
def toEdgeList (g : Hypergraph) : List (Nat × Nat) :=
  g.map fun e => (e.src, e.tgt)

/-- Convert to format suitable for binary bridge protocol -/
def toBridgeFormat (g : Hypergraph) : List (List Nat) :=
  g.map fun e => [e.src, e.tgt]

end HeytingLean.WolframPhysics
