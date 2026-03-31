import HeytingLean.Hyperseries.Eval

namespace HeytingLean
namespace Hyperseries

open CoreExpr

/-- `3 ↦ 3` under phase-1 evaluation. -/
example : CoreExpr.evalOmega (((3 : ℤ) : CoreExpr.Expr)) = (3 : Surreal) := by
  simpa using (CoreExpr.evalOmega_int 3)

/-- `X ↦ ω`. -/
example : CoreExpr.evalOmega CoreExpr.X = omegaSurreal := by
  exact CoreExpr.evalOmega_X

/-- `(X - 1) ↦ (ω - 1)`. -/
example : CoreExpr.evalOmega (CoreExpr.X - 1) = omegaSurreal - 1 := by
  simp [CoreExpr.evalOmega, CoreExpr.X]

end Hyperseries
end HeytingLean
