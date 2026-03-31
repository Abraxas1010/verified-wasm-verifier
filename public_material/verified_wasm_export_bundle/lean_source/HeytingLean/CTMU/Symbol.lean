/-
CTMU Symbol/RecursiveZero scaffold using Float (lightweight).
-/

namespace HeytingLean
namespace CTMU

structure RecursiveZero where
  real : Float
  imag : Float
  constraint : Prop := True
deriving Repr

@[simp] def nonZero (z : RecursiveZero) : Bool :=
  !(z.real == 0.0 && z.imag == 0.0)

structure Symbol where
  z : RecursiveZero
  isNonZero : Prop := True
deriving Repr

end CTMU
end HeytingLean

