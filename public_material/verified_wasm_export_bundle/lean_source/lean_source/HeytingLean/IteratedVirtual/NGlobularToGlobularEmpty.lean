import HeytingLean.IteratedVirtual.NGlobular
import HeytingLean.IteratedVirtual.Globular

/-!
# IteratedVirtual.NGlobularToGlobularEmpty

Embed a truncated globular set `NGlobularSet n` into an (untruncated) `GlobularSet` by
declaring **no cells above dimension `n`** (use `PEmpty`).

This is the minimal strict-only way to interpret an `n`-category’s underlying globular data as
living on the full globe indexing category, without choosing any basepoints for “(n+1)-cells”.
-/

namespace HeytingLean
namespace IteratedVirtual

universe u

open NGlobularSet

namespace NGlobularSet

/-- A truncated globular set extends to a (full) globular set by making all higher cells empty. -/
def toGlobularSetEmpty {n : Nat} (G : NGlobularSet.{u} n) : GlobularSet.{u} := by
  classical
  -- Cells: keep `0..n`, make everything above `n` empty.
  let Cell' : Nat → Type u := fun k => if k ≤ n then G.Cell k else PEmpty

  -- Source/target at level `k` only matter when `k < n`. Otherwise the domain is empty.
  let src' : {k : Nat} → Cell' (k + 1) → Cell' k := by
    intro k x
    by_cases hk : k < n
    · have hk1 : k + 1 ≤ n := Nat.succ_le_of_lt hk
      have hk0 : k ≤ n := Nat.le_trans (Nat.le_succ k) hk1
      have x' : G.Cell (k + 1) := by simpa [Cell', hk1] using x
      have y : G.Cell k := G.src k hk x'
      exact (by simpa [Cell', hk0] using y)
    · have hk1 : ¬(k + 1 ≤ n) := by
        intro hk1_le
        have : k < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk1_le
        exact hk this
      cases (show PEmpty from (by simpa [Cell', hk1] using x))

  let tgt' : {k : Nat} → Cell' (k + 1) → Cell' k := by
    intro k x
    by_cases hk : k < n
    · have hk1 : k + 1 ≤ n := Nat.succ_le_of_lt hk
      have hk0 : k ≤ n := Nat.le_trans (Nat.le_succ k) hk1
      have x' : G.Cell (k + 1) := by simpa [Cell', hk1] using x
      have y : G.Cell k := G.tgt k hk x'
      exact (by simpa [Cell', hk0] using y)
    · have hk1 : ¬(k + 1 ≤ n) := by
        intro hk1_le
        have : k < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk1_le
        exact hk this
      cases (show PEmpty from (by simpa [Cell', hk1] using x))

  refine
    { Cell := Cell'
      src := @src'
      tgt := @tgt'
      src_src_eq_src_tgt := ?_
      tgt_src_eq_tgt_tgt := ?_ }

  · intro k x
    by_cases hk1 : k + 1 < n
    · have hk0 : k < n := Nat.lt_trans (Nat.lt_succ_self k) hk1
      have hk2 : k + 2 ≤ n := Nat.succ_le_of_lt hk1
      have hk1le : k + 1 ≤ n := Nat.succ_le_of_lt hk0
      have hk0le : k ≤ n := Nat.le_trans (Nat.le_succ k) hk1le
      -- Work in the truncated world, then `simp` transports back.
      have h := G.src_src_eq_src_tgt k hk0 hk1 (by simpa [Cell', hk2] using x)
      -- `simp` reduces `src'`/`tgt'` under the `< n` hypotheses.
      simpa [Cell', src', tgt', hk0, hk1, hk2, hk1le, hk0le] using h
    · -- Above the truncation, the `(k+2)`-cells are empty.
      have hk2 : ¬(k + 2 ≤ n) := by
        intro hk2_le
        have : k + 1 < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self (k + 1)) hk2_le
        exact hk1 this
      cases (show PEmpty from (by simpa [Cell', hk2] using x))

  · intro k x
    by_cases hk1 : k + 1 < n
    · have hk0 : k < n := Nat.lt_trans (Nat.lt_succ_self k) hk1
      have hk2 : k + 2 ≤ n := Nat.succ_le_of_lt hk1
      have hk1le : k + 1 ≤ n := Nat.succ_le_of_lt hk0
      have hk0le : k ≤ n := Nat.le_trans (Nat.le_succ k) hk1le
      have h := G.tgt_src_eq_tgt_tgt k hk0 hk1 (by simpa [Cell', hk2] using x)
      simpa [Cell', src', tgt', hk0, hk1, hk2, hk1le, hk0le] using h
    ·
      have hk2 : ¬(k + 2 ≤ n) := by
        intro hk2_le
        have : k + 1 < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self (k + 1)) hk2_le
        exact hk1 this
      cases (show PEmpty from (by simpa [Cell', hk2] using x))

end NGlobularSet

end IteratedVirtual
end HeytingLean
