import HeytingLean.LoF.Correspondence.LoFPrimaryAIGOracleSKYBool

/-!
Sanity checks for `HeytingLean.LoF.Correspondence.LoFPrimaryAIGOracleSKYBool`.

This is compile-only: it checks the key joinability lemma typechecks.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF
open HeytingLean.LoF.LoFPrimary
open HeytingLean.LoF.Correspondence

namespace LoFPrimaryAIGOracleSKYBoolSanity

open LoFPrimary.Expr

def ex2 : LoFPrimary.Expr 2 :=
  -- ¬x0 ∨ x1
  .juxt (.mark (.var 0)) (.var 1)

example (ρ : Fin 2 → Bool) :
    ∃ r : Comb,
      Comb.Steps (LoFPrimarySKYBool.toSKYBool (n := 2) ex2 ρ) r ∧
        Comb.Steps (LoFPrimaryAIGOracleSKYBool.aigOracle (n := 2) ex2 ρ) r := by
  simpa using LoFPrimaryAIGOracleSKYBool.toSKYBool_join_aigOracle (n := 2) ex2 ρ

end LoFPrimaryAIGOracleSKYBoolSanity

end LoF
end Tests
end HeytingLean

