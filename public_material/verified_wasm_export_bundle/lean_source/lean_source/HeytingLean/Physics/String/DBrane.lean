/-
D-brane category scaffold (very small): objects are labeled branes; Hom-counts
are natural numbers with a deliberately simplistic composition law (demo only).
-/

namespace HeytingLean
namespace Physics
namespace String

structure Brane where
  label : String
deriving Repr, DecidableEq

@[simp] def HomCount (A B : Brane) : Nat :=
  if A = B then 1 else 0

@[simp] def composeHom (_A _B _C : Brane) (f : Nat) (g : Nat) : Nat :=
  -- Composition here is addition capped at 1 (idempotent); this is a small,
  -- explicit example category rather than a physically realistic model.
  let s := f + g
  if s = 0 then 0 else 1

end String
end Physics
end HeytingLean
