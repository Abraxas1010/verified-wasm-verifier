import HeytingLean.Hyperseries

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Hyperseries

example : evalOmega X = omegaSurreal := by
  simp

example (e : HExpr) :
    HyperserialDescription.realize (K := Surreal) (describeExprCode e) =
      HExpr.eval surrealModel e := by
  simp [eval_describeExprCode]

example (e : HExpr) :
    HyperserialDescription.describe (K := Surreal) (HExpr.eval surrealModel e) =
      describeExprCode e := by
  simpa using describe_eval_eq_describeExprCode e

example (a : Surreal) : ∃! h : HSNo, evalOmega h = a := by
  simpa using existsUnique_hyperseries a

end Numbers
end Tests
end HeytingLean
