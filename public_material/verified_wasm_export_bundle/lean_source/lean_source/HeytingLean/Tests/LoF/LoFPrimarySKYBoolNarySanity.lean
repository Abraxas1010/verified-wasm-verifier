import HeytingLean.LoF.Correspondence.LoFPrimarySKYBoolNary

/-!
# LoFPrimarySKYBoolNarySanity

Compile-only sanity checks for the env-free `n`-ary LoFPrimary → SKY boolean encoding.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open scoped Classical

open HeytingLean.LoF
open HeytingLean.LoF.LoFPrimary
open HeytingLean.LoF.Correspondence

open LoFPrimary.Expr

open LoFPrimarySKYBoolNary

def ex2 : LoFPrimary.Expr 2 :=
  -- x₀ ∨ ¬x₁
  Expr.juxt (Expr.var 0) (Expr.mark (Expr.var 1))

def rho2 : Fin 2 → Bool := fun i => decide (i = 0)

#check LoFPrimarySKYBoolNary.toSKYFun (n := 2) ex2
#check LoFPrimarySKYBoolNary.toSKYFun_correct (n := 2) ex2 rho2
#check LoFPrimarySKYBoolNary.step_joinable_applyBools
#check LoFPrimarySKYBoolNary.steps_joinable_applyBools

end LoF
end Tests
end HeytingLean
