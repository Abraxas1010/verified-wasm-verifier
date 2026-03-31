import HeytingLean.Matula.Core.Canonicalize

namespace HeytingLean
namespace Matula

/--
Decode a natural into a rooted tree scaffold.
`0` is mapped to `.leaf` as a totality convention; the bijection target remains
positive naturals in proof-facing statements.
-/
partial def fromMatula : Nat → RTree
  | 0 => .leaf
  | 1 => .leaf
  | n + 2 =>
      let children :=
        (expandedPrimeFactors (n + 2)).map (fun p => fromMatula (primeIndex p))
      RTree.canonicalizeByMatula (.node children)

end Matula
end HeytingLean

