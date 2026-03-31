import HeytingLean.LoF.CryptoSheaf.Gluing
import HeytingLean.LoF.CryptoSheaf.CryptoNucleus

namespace HeytingLean
namespace LoF
namespace CryptoSheaf
namespace Examples

open HeytingLean.LoF

variable {α : Type u} [PrimaryAlgebra α]

-- Private aggregation as additive gluing over Ωᴿ.
def privateAgg (R : Reentry α) (xs : List α) : R.Omega :=
  let enc := xs.map (fun a => CryptoNucleus.encrypt (R := R) a)
  additiveGlue (R := R) enc

@[simp] theorem privateAgg_nil (R : Reentry α) : privateAgg (R := R) [] = (⊥ : R.Omega) := by
  simp [privateAgg, additiveGlue]

example : True := trivial

end Examples
end CryptoSheaf
end LoF
end HeytingLean
