import HeytingLean.LoF.Correspondence.LoFPrimarySKYBool
import HeytingLean.LoF.LoFPrimary.AIG

/-!
# LoFPrimaryAIGOracleSKYBool — AIG “oracle” evaluation agrees with SKYBool semantics

This module records a small Phase 3 connection point:

* `LoFPrimary.Expr n` already compiles to a verified AIG (`LoFPrimary.AIG`),
* `LoFPrimarySKYBool.toSKYBool` already reduces to the canonical SKY Church boolean.

Here we package “evaluate via AIG, then inject as a SKYBool” as an *oracle* term and show it is
joinable with the SKY translation (both reduce to the same canonical boolean).
-/

namespace HeytingLean
namespace LoF
namespace Correspondence

open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.LoFPrimary

open LoFPrimary.Expr
open SKYBool

namespace LoFPrimaryAIGOracleSKYBool

/-- “Oracle” term: evaluate `A` via the verified AIG pipeline, then inject as a SKY Church boolean. -/
def aigOracle {n : Nat} (A : LoFPrimary.Expr n) (ρ : Fin n → Bool) : Comb :=
  SKYBool.ofBool ((LoFPrimary.AIG.ofMuxNet (LoFPrimary.MuxNet.toMuxNet (n := n) A)).eval ρ)

theorem aigOracle_correct {n : Nat} (A : LoFPrimary.Expr n) (ρ : Fin n → Bool) :
    Comb.Steps (aigOracle (n := n) A ρ) (SKYBool.ofBool (LoFPrimary.eval A ρ)) := by
  -- `AIG` evaluation matches `LoFPrimary.eval` by a verified compiler correctness theorem.
  refine Comb.Steps.of_eq ?_
  simp [aigOracle, LoFPrimary.AIG.loFToAIG_correct]

theorem toSKYBool_join_aigOracle {n : Nat} (A : LoFPrimary.Expr n) (ρ : Fin n → Bool) :
    ∃ r : Comb,
      Comb.Steps (LoFPrimarySKYBool.toSKYBool (n := n) A ρ) r ∧
        Comb.Steps (aigOracle (n := n) A ρ) r := by
  refine ⟨SKYBool.ofBool (LoFPrimary.eval A ρ), ?_, ?_⟩
  · exact LoFPrimarySKYBool.toSKYBool_correct (n := n) A ρ
  · exact aigOracle_correct (n := n) A ρ

end LoFPrimaryAIGOracleSKYBool

end Correspondence
end LoF
end HeytingLean

