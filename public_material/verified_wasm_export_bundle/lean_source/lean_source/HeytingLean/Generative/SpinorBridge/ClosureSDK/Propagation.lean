import HeytingLean.Generative.SpinorBridge.ClosureSDK.HopfCoordinates

noncomputable section

open scoped Quaternion

namespace HeytingLean.Generative.SpinorBridge.ClosureSDK

/-- Running quaternion product for a finite sequence. -/
def closureProduct (xs : List Q) : Q :=
  xs.prod

@[simp] theorem closureProduct_nil : closureProduct [] = 1 := rfl

@[simp] theorem closureProduct_cons (x : Q) (xs : List Q) :
    closureProduct (x :: xs) = x * closureProduct xs := rfl

@[simp] theorem closureProduct_append (xs ys : List Q) :
    closureProduct (xs ++ ys) = closureProduct xs * closureProduct ys := by
  simp [closureProduct, List.prod_append]

/-- Isolate a single element inside a running product. -/
theorem closureProduct_split (left right : List Q) (g : Q) :
    closureProduct (left ++ g :: right) = closureProduct left * g * closureProduct right := by
  simp [closureProduct, List.prod_append, mul_assoc]

/-- The same factorization works after replacing the middle element. -/
theorem closureProduct_split_perturbed (left right : List Q) (g' : Q) :
    closureProduct (left ++ g' :: right) = closureProduct left * g' * closureProduct right := by
  simpa using closureProduct_split left right g'

end HeytingLean.Generative.SpinorBridge.ClosureSDK
