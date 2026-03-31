import HeytingLean.Hyperseries.Core

namespace HeytingLean
namespace Hyperseries

/--
Algebraic law layer for hyperserial models.

This stays separate from `HyperserialModel` so existing model definitions remain
lightweight while theorem modules can opt into stronger assumptions.
-/
class HyperserialModelLaws (K : Type*) [CommRing K] (M : HyperserialModel K) : Prop where
  exp_log : ∀ x : K, M.exp (M.log x) = x
  log_exp : ∀ x : K, M.log (M.exp x) = x
  hyperExp_zero : ∀ x : K, M.hyperExp 0 x = M.exp x
  hyperLog_zero : ∀ x : K, M.hyperLog 0 x = M.log x
  hyperExp_succ : ∀ α : Ordinal, ∀ x : K, M.hyperExp (Order.succ α) x = M.exp (M.hyperExp α x)
  hyperLog_succ : ∀ α : Ordinal, ∀ x : K, M.hyperLog (Order.succ α) x = M.log (M.hyperLog α x)

section

variable {K : Type*} [CommRing K] (M : HyperserialModel K) [HyperserialModelLaws K M]

@[simp] theorem exp_log (x : K) : M.exp (M.log x) = x :=
  HyperserialModelLaws.exp_log (K := K) (M := M) x

@[simp] theorem log_exp (x : K) : M.log (M.exp x) = x :=
  HyperserialModelLaws.log_exp (K := K) (M := M) x

@[simp] theorem hyperExp_zero (x : K) : M.hyperExp 0 x = M.exp x :=
  HyperserialModelLaws.hyperExp_zero (K := K) (M := M) x

@[simp] theorem hyperLog_zero (x : K) : M.hyperLog 0 x = M.log x :=
  HyperserialModelLaws.hyperLog_zero (K := K) (M := M) x

@[simp] theorem hyperExp_succ (α : Ordinal) (x : K) :
    M.hyperExp (Order.succ α) x = M.exp (M.hyperExp α x) :=
  HyperserialModelLaws.hyperExp_succ (K := K) (M := M) α x

@[simp] theorem hyperLog_succ (α : Ordinal) (x : K) :
    M.hyperLog (Order.succ α) x = M.log (M.hyperLog α x) :=
  HyperserialModelLaws.hyperLog_succ (K := K) (M := M) α x

end

end Hyperseries
end HeytingLean
