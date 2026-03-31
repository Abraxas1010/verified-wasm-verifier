import HeytingLean.Hyperseries.ModelLaws
import HeytingLean.Hyperseries.Eval

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Hyperseries

noncomputable section

example : HyperserialModelLaws Surreal surrealModel := by
  infer_instance

example (x : Surreal) : surrealModel.exp (surrealModel.log x) = x := by
  simp [surrealModel]

example (x : Surreal) : surrealModel.log (surrealModel.exp x) = x := by
  simp [surrealModel]

example (α : Ordinal) (x : Surreal) :
    surrealModel.hyperExp (Order.succ α) x = surrealModel.exp (surrealModel.hyperExp α x) := by
  simp [surrealModel]

example (α : Ordinal) (x : Surreal) :
    surrealModel.hyperLog (Order.succ α) x = surrealModel.log (surrealModel.hyperLog α x) := by
  simp [surrealModel]

end
end Numbers
end Tests
end HeytingLean
