import HeytingLean.Topology.Knot.Bracket

/-!
# Sanity checks: Kauffman bracket (toy)

These tests exercise the executable bracket implementation on tiny, self-contained diagrams.
-/

namespace HeytingLean.Tests.Topology.KauffmanBracketSanity

open HeytingLean.Topology.Knot

private def okEq {α} [BEq α] (e : Except String α) (x : α) : Bool :=
  match e with
  | .ok y => y == x
  | .error _ => false

private def unknot : PlanarDiagram :=
  { freeLoops := 1, crossings := #[] }

private def twoCircles : PlanarDiagram :=
  { freeLoops := 2, crossings := #[] }

private def oneCrossingToy : PlanarDiagram :=
  { freeLoops := 0, crossings := #[{ a := 0, b := 1, c := 0, d := 1 }] }

example :
    okEq ((Kauffman.bracket unknot).map LaurentPoly.toList) [(0, 1)] = true := by
  native_decide

example :
    okEq ((Kauffman.bracket twoCircles).map LaurentPoly.toList) [(-2, -1), (2, -1)] = true := by
  native_decide

example :
    okEq ((Kauffman.bracket oneCrossingToy).map LaurentPoly.toList) [(-1, 1), (1, 1)] = true := by
  native_decide

end HeytingLean.Tests.Topology.KauffmanBracketSanity
