import HeytingLean.Matula.Core.Decoding

namespace HeytingLean
namespace Matula

/-- Roundtrip predicate (tree side). -/
def treeRoundtrip (t : RTree) : Prop :=
  fromMatula (matula t) = t.canonicalizeByMatula

/-- Roundtrip predicate (nat side). -/
def natRoundtrip (n : Nat) : Prop :=
  matula (fromMatula n) = n

/-- Base sanity check for the current scaffold. -/
example : matula RTree.leaf = 1 := by
  simp [matula]

end Matula
end HeytingLean
