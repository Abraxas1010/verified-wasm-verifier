import HeytingLean.Matula.Compute.Encoder
import HeytingLean.Matula.Compute.Decoder
import HeytingLean.Matula.Core.Canonicalize

namespace HeytingLean
namespace Matula

/-- Executable nat-side roundtrip value. -/
def natRoundtripValue (n : Nat) : Nat :=
  matulaEncode (matulaDecode n)

/-- Check nat-side roundtrips on `1..bound` (inclusive). -/
def natRoundtripUpTo (bound : Nat) : Bool :=
  (List.range bound).all (fun k => natRoundtripValue (k + 1) = k + 1)

example : natRoundtripUpTo 128 = true := by
  native_decide

/-- Executable tree-side roundtrip check against canonical form. -/
def treeRoundtripValue (t : RTree) : Bool :=
  matulaDecode (matulaEncode t) == RTree.canonicalizeByMatula t

/-- Check tree-side roundtrips on canonical trees obtained from `1..bound`. -/
def treeRoundtripUpToFromDecode (bound : Nat) : Bool :=
  (List.range bound).all (fun k => treeRoundtripValue (matulaDecode (k + 1)))

example : treeRoundtripUpToFromDecode 128 = true := by
  native_decide

/-- Hand-picked sample trees, including non-canonical forms like `.node []`. -/
def sampleTrees : List RTree :=
  [ .leaf
  , .node []
  , .node [.leaf]
  , .node [.leaf, .leaf]
  , .node [.node [.leaf], .leaf]
  , .node [.leaf, .node [.leaf, .leaf], .node [.leaf]]
  , .node [.node [.node [.leaf]], .leaf, .node []]
  ]

def treeRoundtripOnSamples : Bool :=
  sampleTrees.all treeRoundtripValue

example : treeRoundtripOnSamples = true := by
  native_decide

end Matula
end HeytingLean
