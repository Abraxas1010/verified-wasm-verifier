import HeytingLean.Physics.String.QSeries

/-
Vertex Operator Algebra (VOA) scaffold (minimal, compile-friendly).
We record only a few fields reserved for later VOA structure.
-/

namespace HeytingLean
namespace Physics
namespace String

structure VOA (V : Type u) where
  name   : String
  vacuum : V
  -- For demos: an optional character/partition, kept finite for efficiency
  character? : Option (Array Float) := none
  charTrunc? : Option HeytingLean.Physics.String.QSeries := none
deriving Repr

end String
end Physics
end HeytingLean
