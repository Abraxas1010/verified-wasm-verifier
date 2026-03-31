import Mathlib.Data.List.Sort
import HeytingLean.Matula.Core.Encoding

namespace HeytingLean
namespace Matula

/--
Matula-key canonicalization:
- recursively canonicalize children
- sort children by recursive Matula number
- collapse empty nodes to `.leaf`

Placed in a separate module so `RootedTree` remains independent of `Encoding`
and we avoid an import cycle.
-/
partial def RTree.canonicalizeByMatula : RTree → RTree
  | .leaf => .leaf
  | .node children =>
      let children' := children.map canonicalizeByMatula
      let sorted := children'.mergeSort (fun a b => matula a <= matula b)
      if sorted.isEmpty then .leaf else .node sorted

end Matula
end HeytingLean

