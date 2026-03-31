import HeytingLean.Hyperseries

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Hyperseries

private def ratModel : HyperserialModel Rat where
  omega := 0
  exp := fun x => x
  log := fun x => x
  hyperExp := fun _ x => x
  hyperLog := fun _ x => x

open HExprQ

example : HExprQ.eval ratModel (HExprQ.C (3 / 2 : Rat)) = (3 / 2 : Rat) := by
  rfl

example : HExprQ.eval ratModel HExprQ.X = 0 := by
  rfl

example : HExprQ.eval ratModel (HExprQ.C 1 + HExprQ.C (2 / 3 : Rat)) = (5 / 3 : Rat) := by
  native_decide

example : HExprQ.eval ratModel (HExprQ.hyperExp (0 : Ordinal) (HExprQ.C (7 / 5 : Rat))) = (7 / 5 : Rat) := by
  rfl

end Numbers
end Tests
end HeytingLean
