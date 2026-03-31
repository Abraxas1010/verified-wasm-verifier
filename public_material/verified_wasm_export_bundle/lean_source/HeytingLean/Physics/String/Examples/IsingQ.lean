import HeytingLean.Physics.String.ModularQ

/-!
Ising model `ModMatrices` for truncated q-series (3-dimensional example).
`S` and `T` are small real matrices acting on the coefficient vector;
this is a numeric demo, not a proof.
-/

namespace HeytingLean
namespace Physics
namespace String
namespace Examples
namespace IsingQ

open HeytingLean.Physics.String

@[simp] def mats : ModMatrices :=
  -- Simple symmetric S and diagonal-sign T for a 3-dimensional example
  { S := #[(#[(1.0), (1.0), (0.0)]),
           (#[(1.0), (1.0), (0.0)]),
           (#[(0.0), (0.0), (1.0)])]
  , T := #[(#[(1.0), (0.0), (0.0)]),
           (#[(0.0), (-1.0), (0.0)]),
           (#[(0.0), (0.0), (1.0)])] }

@[simp] def v0 : Array Float := #[1.0, 0.0, 1.0]

end IsingQ
end Examples
end String
end Physics
end HeytingLean
