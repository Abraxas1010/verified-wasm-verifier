import HeytingLean.LoF.Correspondence.LoFPrimarySKYBool

/-!
# LoFPrimarySKYBoolSanity

Sanity checks for the environment-parametrized bridge:

`LoFPrimary.Expr n` + `ρ : Fin n → Bool` → SKY Church boolean,
with a proof that the translation reduces to the canonical boolean matching `LoFPrimary.eval`.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF
open HeytingLean.LoF.LoFPrimary
open HeytingLean.LoF.Correspondence

open LoFPrimarySKYBool

namespace LoFPrimarySKYBoolSanity

def rhoTrue : Fin 1 → Bool := fun _ => true
def rhoFalse : Fin 1 → Bool := fun _ => false

def A : LoFPrimary.Expr 1 :=
  -- x ∨ ¬x  (always true)
  Expr.juxt (Expr.var 0) (Expr.mark (Expr.var 0))

#check LoFPrimarySKYBool.toSKYBool_correct A rhoTrue
#check LoFPrimarySKYBool.toSKYBool_correct A rhoFalse

end LoFPrimarySKYBoolSanity

end LoF
end Tests
end HeytingLean
