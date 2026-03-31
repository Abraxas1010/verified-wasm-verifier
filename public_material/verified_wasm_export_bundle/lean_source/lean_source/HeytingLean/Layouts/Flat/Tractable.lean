import HeytingLean.Layouts.Flat.Basic

/-!
# CuTe layouts: tractability and non-degeneracy (flat)

This file encodes the key “well-behavedness” predicate from the CuTe layout-categories paper:
the **tractability** divisibility condition on strides, plus a small “non-degeneracy” predicate.

We provide both:
- a `Prop`-level predicate (for proofs), and
- a `Bool` checker (for executable sanity tests).
-/

namespace HeytingLean
namespace Layouts
namespace Flat

open Flat

namespace ShapeStridePair

/-- Lexicographic-style order used by the tractability condition:
`(s,d) ⪯ (s',d')` iff `d < d'` or (`d = d'` and `s ≤ s'`). -/
def le (p q : ShapeStridePair) : Prop :=
  p.stride < q.stride ∨ (p.stride = q.stride ∧ p.shapeNat ≤ q.shapeNat)

/-- `ShapeStridePair.le` is decidable (used by `decide`-based checkers). -/
instance (p q : ShapeStridePair) : Decidable (le p q) := by
  unfold le
  infer_instance

/-- Boolean checker for `ShapeStridePair.le`. -/
def leB (p q : ShapeStridePair) : Bool :=
  decide (le p q)

theorem leB_eq (p q : ShapeStridePair) : leB p q = decide (le p q) := rfl

end ShapeStridePair

namespace FlatLayout

/-- Non-degeneracy: a trivial shape (`s = 1`) must have stride `0`. -/
def Nondegenerate (L : FlatLayout) : Prop :=
  ∀ (i : Fin L.length), (L.get i).shapeNat = 1 → (L.get i).stride = 0

/-- Tractability condition (flat case).

For any distinct modes `i ≠ j`, if `(sᵢ,dᵢ) ⪯ (sⱼ,dⱼ)` and both strides are nonzero, then
`(sᵢ * dᵢ)` divides `dⱼ`.
-/
def Tractable (L : FlatLayout) : Prop :=
  ∀ (i j : Fin L.length),
    i ≠ j →
    ShapeStridePair.le (L.get i) (L.get j) →
    (L.get i).stride ≠ 0 →
    (L.get j).stride ≠ 0 →
    (L.get i).shapeNat * (L.get i).stride ∣ (L.get j).stride

/-! ### Executable checkers -/

private def tractablePairB (p q : ShapeStridePair) : Bool :=
  if decide (p = q) then
    true
  else if p.stride == 0 || q.stride == 0 then
    true
  else if ShapeStridePair.leB p q then
    decide (q.stride % (p.shapeNat * p.stride) = 0)
  else
    true

private def allPairsB : List ShapeStridePair → Bool
  | [] => true
  | p :: ps =>
      let row := ps.all (fun q => tractablePairB p q && tractablePairB q p)
      row && allPairsB ps

/-- A simple `Bool` tractability check (suitable for smoke tests). -/
def tractableB (L : FlatLayout) : Bool :=
  allPairsB L

end FlatLayout

end Flat
end Layouts
end HeytingLean
