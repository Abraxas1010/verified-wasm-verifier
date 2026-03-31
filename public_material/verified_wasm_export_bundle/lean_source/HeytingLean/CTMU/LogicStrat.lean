/-
CTMU dimensional logic stratification: map a dimension to a logic kind
in a deliberately simple, explicit way.
-/

namespace HeytingLean
namespace CTMU

structure Dimension where
  n : Nat
deriving Repr

inductive LogicKind | HeytingLike | BooleanLike
deriving Repr

@[simp] def kind (d : Dimension) : LogicKind :=
  if d.n < 2 then LogicKind.HeytingLike else LogicKind.BooleanLike

end CTMU
end HeytingLean
