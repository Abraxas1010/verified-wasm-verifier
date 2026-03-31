import HeytingLean.LoF.CryptoSheaf.Gluing

namespace HeytingLean
namespace LoF
namespace CryptoSheaf
namespace Examples

open HeytingLean.LoF

variable {α : Type u} [PrimaryAlgebra α]

/-- For empty shards, `thresholdGlueTake` agrees with the `thresholdGlue` behavior. -/
theorem threshold_take_nil (R : Reentry α) :
    thresholdGlueTake (R := R) 0 [] = (⊤ : R.Omega)
    ∧ (∀ k, thresholdGlueTake (R := R) (Nat.succ k) [] = (⊥ : R.Omega)) := by
  constructor
  · simp
  · intro k; simp

example : True := trivial

end Examples
end CryptoSheaf
end LoF
end HeytingLean

