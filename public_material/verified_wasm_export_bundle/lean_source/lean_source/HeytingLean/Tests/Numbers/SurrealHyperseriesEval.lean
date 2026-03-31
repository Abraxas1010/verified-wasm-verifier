import HeytingLean.Hyperseries
import HeytingLean.Numbers.Surreal.Hyperseries

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Hyperseries
open HeytingLean.Hyperseries.CoreExpr

example : CoreExpr.evalOmega CoreExpr.X = omegaSurreal := by
  exact CoreExpr.evalOmega_X

example : CoreExpr.evalOmega (CoreExpr.X - 1) = omegaSurreal - 1 := by
  simp [CoreExpr.evalOmega, CoreExpr.X]

example :
    HeytingLean.Numbers.Surreal.Hyperseries.order
      (HeytingLean.Numbers.Surreal.Hyperseries.monomial 2
        (HeytingLean.Numbers.Ordinal.OrdinalCNF.ofNat 1)) =
    HeytingLean.Numbers.Ordinal.OrdinalCNF.max
      (HeytingLean.Numbers.Ordinal.OrdinalCNF.ofNat 1) 0 := by
  simp [HeytingLean.Numbers.Surreal.Hyperseries.order_monomial]

end Numbers
end Tests
end HeytingLean
