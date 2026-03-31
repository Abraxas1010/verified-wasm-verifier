import HeytingLean.IteratedVirtual.SpiralStrict22

/-!
# Tests.IteratedVirtual.StrictNKCellSanity

Compile-only checks that a “k-cell in an n-category” is available for `k ≤ n` using:
- `NGlobularSet.restrict`,
- `StrictNCategory.kCell`.
-/

namespace HeytingLean
namespace Tests
namespace IteratedVirtual

open HeytingLean.IteratedVirtual

-- A trivial 5-cell in the strict 22-category (by mapping everything to `PUnit.unit`).
def trivial5Cell : StrictNCategory.kCell (n := 22) spiral22Cat 5 (by decide) :=
  { map := by
      intro k _
      by_cases hk : k ≤ 5
      ·
        have hk22 : k ≠ 22 := by
          have : k < 22 := lt_of_le_of_lt hk (by decide : 5 < 22)
          exact ne_of_lt this
        simpa [NGlobularSet.restrict, hk, spiral22Cat, spiral22Globular, spiral22CellType, hk22] using
          (PUnit.unit : PUnit)
      ·
        simpa [NGlobularSet.restrict, hk] using (PUnit.unit : PUnit)
    map_src := by
      intro k hk x
      have hk' : k ≤ 5 := Nat.le_trans (Nat.le_of_lt_succ hk) (by decide : 4 ≤ 5)
      have hk22 : k ≠ 22 := by
        have : k < 22 := Nat.lt_trans hk (by decide : 5 < 22)
        exact ne_of_lt this
      haveI :
          Subsingleton ((spiral22Cat.G.restrict 5 (by decide)).Cell k) := by
        simpa [NGlobularSet.restrict, hk', spiral22Cat, spiral22Globular, spiral22CellType, hk22] using
          (by infer_instance : Subsingleton PUnit)
      exact Subsingleton.elim _ _
    map_tgt := by
      intro k hk x
      have hk' : k ≤ 5 := Nat.le_trans (Nat.le_of_lt_succ hk) (by decide : 4 ≤ 5)
      have hk22 : k ≠ 22 := by
        have : k < 22 := Nat.lt_trans hk (by decide : 5 < 22)
        exact ne_of_lt this
      haveI :
          Subsingleton ((spiral22Cat.G.restrict 5 (by decide)).Cell k) := by
        simpa [NGlobularSet.restrict, hk', spiral22Cat, spiral22Globular, spiral22CellType, hk22] using
          (by infer_instance : Subsingleton PUnit)
      exact Subsingleton.elim _ _ }

#check trivial5Cell

end IteratedVirtual
end Tests
end HeytingLean
