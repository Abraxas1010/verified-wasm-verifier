import HeytingLean.Numbers.Surreal.QuotOps

namespace HeytingLean
namespace Numbers
namespace Surreal

/-!
Normalized order on `SurrealQ`.

We provide a lightweight “order modulo normalization” where two
quotient surreals are compared by equality of their normalized `Game`
representatives. This yields reflexivity, transitivity, and an
antisymmetry result that identifies elements up to the `normalizeQ`
projection. It complements the budgeted `leN` on `Game` (`repr` bridge)
and the `leQ` surrogate over `PreGame`.
-/

noncomputable section

/-- Normalized comparison on `SurrealQ`: equality after quotient-level normalization. -/
def leNQ (x y : SurrealQ) : Prop :=
  normalizeQ x = normalizeQ y

@[simp] lemma leNQ_refl (x : SurrealQ) : leNQ x x := rfl

lemma leNQ_trans {x y z : SurrealQ} :
    leNQ x y → leNQ y z → leNQ x z := by
  intro hxy hyz
  exact Eq.trans hxy hyz

/-- Antisymmetry modulo normalization: if `x ≤ y` and `y ≤ x` in the
normalized sense, then their `normalizeQ` projections are equal. -/
lemma leNQ_antisymm_norm {x y : SurrealQ} :
    leNQ x y → leNQ y x → normalizeQ x = normalizeQ y := by
  intro hxy _hyx
  exact hxy

end

end Surreal
end Numbers
end HeytingLean
