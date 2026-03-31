/-
Minimal complex Float type and helpers (addition, multiplication, unit-phase).
-/

namespace HeytingLean
namespace Physics
namespace String

structure CFloat where
  re : Float
  im : Float
deriving Repr

instance : Inhabited CFloat := ⟨{re := 0.0, im := 0.0}⟩

namespace CFloat

@[simp] def add (a b : CFloat) : CFloat :=
  { re := a.re + b.re, im := a.im + b.im }

@[simp] def mul (a b : CFloat) : CFloat :=
  { re := a.re * b.re - a.im * b.im
  , im := a.re * b.im + a.im * b.re }

@[simp] def scale (k : Float) (a : CFloat) : CFloat :=
  { re := k * a.re, im := k * a.im }

@[simp] def unitPhase (θ : Float) : CFloat :=
  -- crude approximations using small Taylor polys would suffice, but reuse Float's cos/sin
  -- We avoid importing Complex; local approximations acceptable for demos
  -- Using Float.sin/cos if available; otherwise fallback to identity (Lean's Float has sin/cos)
  { re := Float.cos θ, im := Float.sin θ }

end CFloat

end String
end Physics
end HeytingLean
