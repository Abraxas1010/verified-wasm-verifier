import HeytingLean.Topology.Knot.Bracket
import HeytingLean.Topology.Knot.Jones
import HeytingLean.Topology.Knot.Reidemeister

/-!
# Knot moves demo (Phase 1)

This executable is a tiny regression harness for Reidemeister move constructors:
- R1 add/remove (both curl kinds),
- R2 add/remove.

It checks that:
- `r1RemoveLast (r1Add g …)` returns the original graph, and
- the bracket scales for R1 and is invariant for R2 on a small toy input.
-/

namespace HeytingLean.CLI.KnotMovesMain

open HeytingLean.Topology.Knot
open HeytingLean.Topology.Knot.Kauffman
open HeytingLean.Topology.Knot.Kauffman.SignedPDGraph
open HeytingLean.Topology.Knot.Reidemeister

private def oneCrossingToy : PlanarDiagram :=
  { freeLoops := 0, crossings := #[{ a := 0, b := 1, c := 0, d := 1 }] }

private def twoCrossingToy : PlanarDiagram :=
  { freeLoops := 0
    crossings := #[{ a := 0, b := 1, c := 0, d := 1 }, { a := 2, b := 3, c := 2, d := 3 }] }

private def die (msg : String) : IO UInt32 := do
  IO.eprintln msg
  pure 1

private def ok (b : Bool) (msg : String) : IO Unit := do
  if !b then
    throw (IO.userError msg)

def main (_argv : List String) : IO UInt32 := do
  try
    let g0 ←
      match PDGraph.ofPlanarDiagram oneCrossingToy with
      | .ok g => pure g
      | .error e => throw (IO.userError s!"PDGraph error: {e}")
    let b0 ←
      match Kauffman.bracketGraph g0 with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"bracket error: {e}")
    let s0 : SignedPDGraph := { graph := g0, sign := #[.pos] }
    let nb0 ←
      match SignedPDGraph.normalizedBracket s0 with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"normalizedBracket error: {e}")

    -- Systematic R1 round-trip + scaling checks over all half-edges in `g0`.
    for x in [0:g0.numHalfEdges] do
      for kind in [CurlKind.pos, CurlKind.neg] do
        let kindName :=
          match kind with
          | .pos => "pos"
          | .neg => "neg"
        let g1 ←
          match Reidemeister.r1Add g0 x kind with
          | .ok g => pure g
          | .error e => throw (IO.userError s!"r1Add({kindName}) error (x={x}): {e}")
        let b1 ←
          match Kauffman.bracketGraph g1 with
          | .ok p => pure p
          | .error e => throw (IO.userError s!"bracket({kindName}) error (x={x}): {e}")
        let factor : LaurentPoly :=
          match kind with
          | .pos => -(Kauffman.A ^ 3)
          | .neg => -(Kauffman.Ainv ^ 3)
        ok (decide (b1 = factor * b0)) s!"R1({kindName}) scaling failed at x={x}"
        let s1 ←
          match SignedPDGraph.r1Add s0 x kind with
          | .ok s => pure s
          | .error e => throw (IO.userError s!"r1AddSigned({kindName}) error (x={x}): {e}")
        let nb1 ←
          match SignedPDGraph.normalizedBracket s1 with
          | .ok p => pure p
          | .error e => throw (IO.userError s!"normalizedBracket({kindName}) error (x={x}): {e}")
        ok (decide (nb1 = nb0)) s!"R1({kindName}) normalized invariance failed at x={x}"
        let gBack ←
          match Reidemeister.r1RemoveLast g1 kind with
          | .ok g => pure g
          | .error e => throw (IO.userError s!"r1RemoveLast({kindName}) error (x={x}): {e}")
        ok (decide (gBack.n = g0.n ∧ gBack.freeLoops = g0.freeLoops ∧ gBack.arcNbr = g0.arcNbr))
          s!"R1({kindName}) round-trip failed at x={x}"
        let sBack ←
          match SignedPDGraph.r1RemoveLast s1 kind with
          | .ok s => pure s
          | .error e => throw (IO.userError s!"r1RemoveLastSigned({kindName}) error (x={x}): {e}")
        ok (decide (sBack.graph.n = s0.graph.n ∧ sBack.graph.arcNbr = s0.graph.arcNbr ∧ sBack.sign = s0.sign))
          s!"R1({kindName}) signed round-trip failed at x={x}"

    -- R1 (+)
    let g1p ←
      match Reidemeister.r1Add g0 0 .pos with
      | .ok g => pure g
      | .error e => throw (IO.userError s!"r1Add(pos) error: {e}")
    let b1p ←
      match Kauffman.bracketGraph g1p with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"bracket(pos) error: {e}")
    let factorPos : LaurentPoly := -(Kauffman.A ^ 3)
    ok (decide (b1p = factorPos * b0)) "R1(pos): bracket scaling check failed"
    let s1p ←
      match SignedPDGraph.r1Add s0 0 .pos with
      | .ok s => pure s
      | .error e => throw (IO.userError s!"r1AddSigned(pos) error: {e}")
    let nb1p ←
      match SignedPDGraph.normalizedBracket s1p with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"normalizedBracket(pos) error: {e}")
    ok (decide (nb1p = nb0)) "R1(pos): normalized bracket invariance check failed"
    let g0' ←
      match Reidemeister.r1RemoveLast g1p .pos with
      | .ok g => pure g
      | .error e => throw (IO.userError s!"r1RemoveLast(pos) error: {e}")
    ok (decide (g0'.n = g0.n ∧ g0'.freeLoops = g0.freeLoops ∧ g0'.arcNbr = g0.arcNbr))
      "R1(pos): remove did not restore original graph"
    let s0' ←
      match SignedPDGraph.r1RemoveLast s1p .pos with
      | .ok s => pure s
      | .error e => throw (IO.userError s!"r1RemoveLastSigned(pos) error: {e}")
    ok (decide (s0'.graph.n = s0.graph.n ∧ s0'.graph.arcNbr = s0.graph.arcNbr ∧ s0'.sign = s0.sign))
      "R1(pos): signed remove did not restore original graph"

    -- R1 (-)
    let g1n ←
      match Reidemeister.r1Add g0 0 .neg with
      | .ok g => pure g
      | .error e => throw (IO.userError s!"r1Add(neg) error: {e}")
    let b1n ←
      match Kauffman.bracketGraph g1n with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"bracket(neg) error: {e}")
    let factorNeg : LaurentPoly := -(Kauffman.Ainv ^ 3)
    ok (decide (b1n = factorNeg * b0)) "R1(neg): bracket scaling check failed"
    let s1n ←
      match SignedPDGraph.r1Add s0 0 .neg with
      | .ok s => pure s
      | .error e => throw (IO.userError s!"r1AddSigned(neg) error: {e}")
    let nb1n ←
      match SignedPDGraph.normalizedBracket s1n with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"normalizedBracket(neg) error: {e}")
    ok (decide (nb1n = nb0)) "R1(neg): normalized bracket invariance check failed"
    let g0'' ←
      match Reidemeister.r1RemoveLast g1n .neg with
      | .ok g => pure g
      | .error e => throw (IO.userError s!"r1RemoveLast(neg) error: {e}")
    ok (decide (g0''.n = g0.n ∧ g0''.freeLoops = g0.freeLoops ∧ g0''.arcNbr = g0.arcNbr))
      "R1(neg): remove did not restore original graph"
    let s0'' ←
      match SignedPDGraph.r1RemoveLast s1n .neg with
      | .ok s => pure s
      | .error e => throw (IO.userError s!"r1RemoveLastSigned(neg) error: {e}")
    ok (decide (s0''.graph.n = s0.graph.n ∧ s0''.graph.arcNbr = s0.graph.arcNbr ∧ s0''.sign = s0.sign))
      "R1(neg): signed remove did not restore original graph"

    -- Systematic R2 round-trip + invariance checks on all disjoint arc pairs in `g0`.
    let m0 := g0.numHalfEdges
    for x in [0:m0] do
      for u in [0:m0] do
        if x != u then
          let y := g0.arcNbr[x]!
          let v := g0.arcNbr[u]!
          let disjoint := x != u ∧ x != v ∧ y != u ∧ y != v
          if disjoint then
            let g2 ←
              match Reidemeister.r2Add g0 x u with
              | .ok g => pure g
              | .error e => throw (IO.userError s!"r2Add error (x={x},u={u}): {e}")
            let b2 ←
              match Kauffman.bracketGraph g2 with
              | .ok p => pure p
              | .error e => throw (IO.userError s!"bracket(r2) error (x={x},u={u}): {e}")
            ok (decide (b2 = b0)) s!"R2 bracket invariance failed at x={x},u={u}"
            let s2 ←
              match SignedPDGraph.r2Add s0 x u with
              | .ok s => pure s
              | .error e => throw (IO.userError s!"r2AddSigned error (x={x},u={u}): {e}")
            let nb2 ←
              match SignedPDGraph.normalizedBracket s2 with
              | .ok p => pure p
              | .error e => throw (IO.userError s!"normalizedBracket(r2) error (x={x},u={u}): {e}")
            ok (decide (nb2 = nb0)) s!"R2 normalized invariance failed at x={x},u={u}"
            let gBack ←
              match Reidemeister.r2RemoveLast g2 with
              | .ok g => pure g
              | .error e => throw (IO.userError s!"r2RemoveLast error (x={x},u={u}): {e}")
            ok (decide (gBack.n = g0.n ∧ gBack.freeLoops = g0.freeLoops ∧ gBack.arcNbr = g0.arcNbr))
              s!"R2 round-trip failed at x={x},u={u}"
            let sBack ←
              match SignedPDGraph.r2RemoveLast s2 with
              | .ok s => pure s
              | .error e => throw (IO.userError s!"r2RemoveLastSigned error (x={x},u={u}): {e}")
            ok (decide (sBack.graph.n = s0.graph.n ∧ sBack.graph.arcNbr = s0.graph.arcNbr ∧ sBack.sign = s0.sign))
              s!"R2 signed round-trip failed at x={x},u={u}"

    -- R2
    let g2 ←
      match Reidemeister.r2Add g0 0 1 with
      | .ok g => pure g
      | .error e => throw (IO.userError s!"r2Add error: {e}")
    let b2 ←
      match Kauffman.bracketGraph g2 with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"bracket(r2) error: {e}")
    ok (decide (b2 = b0)) "R2: bracket invariance check failed"
    let s2 ←
      match SignedPDGraph.r2Add s0 0 1 with
      | .ok s => pure s
      | .error e => throw (IO.userError s!"r2AddSigned error: {e}")
    let nb2 ←
      match SignedPDGraph.normalizedBracket s2 with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"normalizedBracket(r2) error: {e}")
    ok (decide (nb2 = nb0)) "R2: normalized bracket invariance check failed"
    let g0''' ←
      match Reidemeister.r2RemoveLast g2 with
      | .ok g => pure g
      | .error e => throw (IO.userError s!"r2RemoveLast error: {e}")
    ok (decide (g0'''.n = g0.n ∧ g0'''.freeLoops = g0.freeLoops ∧ g0'''.arcNbr = g0.arcNbr))
      "R2: remove did not restore original graph"
    let s0''' ←
      match SignedPDGraph.r2RemoveLast s2 with
      | .ok s => pure s
      | .error e => throw (IO.userError s!"r2RemoveLastSigned error: {e}")
    ok (decide (s0'''.graph.n = s0.graph.n ∧ s0'''.graph.arcNbr = s0.graph.arcNbr ∧ s0'''.sign = s0.sign))
      "R2: signed remove did not restore original graph"

    -- R3 braid form (σ₁σ₂σ₁ = σ₂σ₁σ₂) on a toy base with ≥ 3 disjoint arcs
    let gBase ←
      match PDGraph.ofPlanarDiagram twoCrossingToy with
      | .ok g => pure g
      | .error e => throw (IO.userError s!"PDGraph error (base): {e}")
    let gL ←
      match Reidemeister.r3BraidLeft gBase 0 1 4 with
      | .ok g => pure g
      | .error e => throw (IO.userError s!"r3BraidLeft error: {e}")
    let gR ←
      match Reidemeister.r3BraidRight gBase 0 1 4 with
      | .ok g => pure g
      | .error e => throw (IO.userError s!"r3BraidRight error: {e}")
    let bL ←
      match Kauffman.bracketGraph gL with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"bracket(r3-left) error: {e}")
    let bR ←
      match Kauffman.bracketGraph gR with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"bracket(r3-right) error: {e}")
    ok (decide (bL = bR)) "R3: braid relation check failed"
    let sBase : SignedPDGraph := { graph := gBase, sign := #[.pos, .pos] }
    let sL ←
      match SignedPDGraph.r3BraidLeft sBase 0 1 4 with
      | .ok s => pure s
      | .error e => throw (IO.userError s!"r3BraidLeftSigned error: {e}")
    let sR ←
      match SignedPDGraph.r3BraidRight sBase 0 1 4 with
      | .ok s => pure s
      | .error e => throw (IO.userError s!"r3BraidRightSigned error: {e}")
    let nbL ←
      match SignedPDGraph.normalizedBracket sL with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"normalizedBracket(r3-left) error: {e}")
    let nbR ←
      match SignedPDGraph.normalizedBracket sR with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"normalizedBracket(r3-right) error: {e}")
    ok (decide (nbL = nbR)) "R3: normalized bracket check failed"

    IO.println "knot_moves_demo: ok"
    pure 0
  catch e =>
    die s!"knot_moves_demo: FAILED: {e}"

end HeytingLean.CLI.KnotMovesMain

open HeytingLean.CLI.KnotMovesMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.KnotMovesMain.main args
