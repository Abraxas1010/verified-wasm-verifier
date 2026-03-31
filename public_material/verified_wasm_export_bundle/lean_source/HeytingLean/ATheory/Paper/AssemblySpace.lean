import Mathlib.Data.Set.Lattice

namespace HeytingLean
namespace ATheory
namespace Paper

universe u

/-- Paper-faithful assembly space data `(Ω, U, J)`.

This intentionally keeps `J` ternary (join predicate) as in the paper, rather than
immediately choosing a graph encoding.

The paper also defines `Ω` as the closure of `U` under `J`. We represent this closure
property via the `closed` field in `AssemblySpace.Closed` (see `AssemblyPath.lean`).
-/
structure AssemblySpace where
  Ω : Type u
  U : Set Ω
  /-- `J x y z` means `x` and `y` can be causally joined to form `z`. -/
  J : Ω → Ω → Ω → Prop

end Paper
end ATheory
end HeytingLean

