import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Bool.Basic
import HeytingLean.Crypto.Information.Hashing.UniversalHash

/-!
# 2-universal hash families (finite/combinatorial)

This is the collision-count formulation, avoiding probability theory.
-/

namespace HeytingLean
namespace Crypto
namespace Information
namespace Hashing

universe u v w

/-- 2-universal hash family: collision count is bounded by `|S|/|R|`. -/
class TwoUniversal (D : Type u) (R : Type v) (S : Type w)
    [Fintype R] [Fintype S] [DecidableEq R] extends HashFamily D R S where
  collision_bound :
    ∀ (x y : D), x ≠ y →
      (Finset.filter (fun s : S => hash s x = hash s y) Finset.univ).card ≤
        Fintype.card S / Fintype.card R

/-!
## A tiny concrete witness: XOR hash on `Bool`

This is not meant to be a cryptographically relevant family; it is a compact example showing the
interface is inhabited without importing field theory.
-/

def xorHash : HashFamily Bool Bool Bool where
  hash := fun s x => Bool.xor s x

instance : TwoUniversal Bool Bool Bool where
  toHashFamily := xorHash
  collision_bound := by
    intro x y hxy
    cases x <;> cases y
    · cases hxy rfl
    ·
      have hEmpty :
          (Finset.filter (fun s : Bool => xorHash.hash s false = xorHash.hash s true) Finset.univ) = ∅ := by
        ext s
        cases s <;> simp [xorHash, Bool.xor]
      have hLhs :
          (Finset.filter (fun s : Bool => xorHash.hash s false = xorHash.hash s true) Finset.univ).card = 0 := by
        rw [hEmpty]
        simp
      have hRhs : Fintype.card Bool / Fintype.card Bool = 1 := by
        simp [Fintype.card_bool]
      rw [hLhs, hRhs]
      exact Nat.zero_le 1
    ·
      have hEmpty :
          (Finset.filter (fun s : Bool => xorHash.hash s true = xorHash.hash s false) Finset.univ) = ∅ := by
        ext s
        cases s <;> simp [xorHash, Bool.xor]
      have hLhs :
          (Finset.filter (fun s : Bool => xorHash.hash s true = xorHash.hash s false) Finset.univ).card = 0 := by
        rw [hEmpty]
        simp
      have hRhs : Fintype.card Bool / Fintype.card Bool = 1 := by
        simp [Fintype.card_bool]
      rw [hLhs, hRhs]
      exact Nat.zero_le 1
    · cases hxy rfl

end Hashing
end Information
end Crypto
end HeytingLean

