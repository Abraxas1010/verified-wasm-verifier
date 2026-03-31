/-
Truncated q-series as a finite array of real coefficients.

This module is intentionally small and executable-first. It does not aim
to model modular forms in full generality; instead it provides concrete
finite data used by the string-physics example lenses and tests.
-/

namespace HeytingLean
namespace Physics
namespace String

structure QSeries where
  coeffs : Array Float
deriving Repr

namespace QSeries

@[simp] def length (q : QSeries) : Nat := q.coeffs.size

@[simp] def coeffAt (q : QSeries) (i : Nat) : Float :=
  if i < q.coeffs.size then q.coeffs[i]! else 0.0

@[simp] def fromList (xs : List Float) : QSeries :=
  { coeffs := Array.mk xs }

/-- Pointwise addition of truncated q-series. -/
@[simp] def add (q₁ q₂ : QSeries) : QSeries :=
  { coeffs := Id.run do
      let m := Nat.min q₁.coeffs.size q₂.coeffs.size
      let mut out : Array Float := Array.mkEmpty m
      for i in [:m] do
        out := out.push (q₁.coeffs[i]! + q₂.coeffs[i]!)
      out }

/-- Scalar multiplication of a truncated q-series. -/
@[simp] def scale (a : Float) (q : QSeries) : QSeries :=
  { coeffs := q.coeffs.map (fun x => a * x) }

@[simp] def zero : QSeries := { coeffs := #[] }

end QSeries

end String
end Physics
end HeytingLean
