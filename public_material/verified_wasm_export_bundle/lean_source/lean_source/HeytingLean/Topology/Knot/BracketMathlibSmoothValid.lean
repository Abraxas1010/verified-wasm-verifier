import HeytingLean.Topology.Knot.BracketMathlib
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Init.Data.List.Monadic
import Init.Data.Array.Lemmas
import Init.Data.Range.Lemmas

/-!
# Knot theory: smoothing preserves basic shape (Mathlib proof layer)

Helper lemmas about the *shape* of `Kauffman.smoothLastCoreML` outputs (notably array sizes).
-/

namespace HeytingLean
namespace Topology
namespace Knot

namespace Kauffman

open Std

noncomputable section

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

lemma List.forIn_array_size_eq
    {α : Type} (l : List α) (init : Array Nat)
    (f : α → Array Nat → Id (ForInStep (Array Nat)))
    (hf :
      ∀ a b,
        match f a b with
        | .done b' => b'.size = b.size
        | .yield b' => b'.size = b.size) :
    (forIn l init f).size = init.size := by
  induction l generalizing init with
  | nil =>
      simp [Pure.pure]
  | cons a l ih =>
      simp only [List.forIn_cons, Bind.bind, Pure.pure]
      cases h : f a init with
      | done b' =>
          have hb : b'.size = init.size := by
            simpa [h] using hf a init
          simp [hb]
      | yield b' =>
          have hb : b'.size = init.size := by
            simpa [h] using hf a init
          have ih' : (forIn l b' f).size = b'.size := ih (init := b')
          simp [ih', hb]

/--
Smoothing the last crossing drops the last block of 4 half-edges, hence the rewired `arcNbr`
has size `4*(n-1)`.
-/
theorem smoothLastCoreML_rewire_size
    {n : Nat} {arcNbr : Array Nat} {isB : Bool}
    (hn : 0 < n)
    (hsize : arcNbr.size = 4 * n) :
    (smoothLastCoreML_rewire n arcNbr isB).size = 4 * (n - 1) := by
  classical
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  -- `smoothLastCoreML_rewire` is now defined via `Array.ofFn`, so its size is definitional.
  simp [smoothLastCoreML_rewire, Nat.mul_succ]

/--
Main size lemma for the full smoothing step (free-loop counting + rewiring).
-/
theorem smoothLastCoreML_size
    {freeLoops n : Nat} {arcNbr : Array Nat} {isB : Bool}
    (hn : 0 < n)
    (hsize : arcNbr.size = 4 * n) :
    (smoothLastCoreML freeLoops n arcNbr isB).2.size = 4 * (n - 1) := by
  simpa [smoothLastCoreML] using
    (smoothLastCoreML_rewire_size (n := n) (arcNbr := arcNbr) (isB := isB) hn hsize)

private lemma smoothLastCoreML_smooth_lt
    {n : Nat} {isB : Bool} (hn : 0 < n) (r : Nat) :
    smoothLastCoreML_smooth n isB r < 4 * n := by
  have hn1 : 1 ≤ n := Nat.succ_le_iff.mp hn
  have h4le : 4 ≤ 4 * n := by
    simpa using (Nat.mul_le_mul_left 4 hn1)
  have hC : ∀ c, c < 4 → (4 * n - 4) + c < 4 * n := by
    intro c hc
    have : (4 * n - 4) + c < (4 * n - 4) + 4 :=
      Nat.add_lt_add_left hc (4 * n - 4)
    simpa [Nat.sub_add_cancel h4le] using this

  have hpos : r % 4 < 4 := Nat.mod_lt r (by decide)
  cases isB with
  | false =>
      cases h : r % 4 with
      | zero =>
          -- `pos = 0` ↦ `base + 1`
          simpa [smoothLastCoreML_smooth, h] using (hC 1 (by decide))
      | succ p1 =>
          cases p1 with
          | zero =>
              -- `pos = 1` ↦ `base + 0`
              simpa [smoothLastCoreML_smooth, h] using (hC 0 (by decide))
          | succ p2 =>
              cases p2 with
              | zero =>
                  -- `pos = 2` ↦ `base + 3`
                  simpa [smoothLastCoreML_smooth, h] using (hC 3 (by decide))
              | succ p3 =>
                  cases p3 with
                  | zero =>
                      -- `pos = 3` ↦ `base + 2`
                      simpa [smoothLastCoreML_smooth, h] using (hC 2 (by decide))
                  | succ p4 =>
                      exfalso
                      have : Nat.succ (Nat.succ (Nat.succ (Nat.succ p4))) < 4 := by
                        simpa [h] using hpos
                      have hge : 4 ≤ Nat.succ (Nat.succ (Nat.succ (Nat.succ p4))) :=
                        Nat.succ_le_succ
                          (Nat.succ_le_succ
                            (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))))
                      exact (Nat.not_lt_of_ge hge) this
  | true =>
      cases h : r % 4 with
      | zero =>
          -- `pos = 0` ↦ `base + 3`
          simpa [smoothLastCoreML_smooth, h] using (hC 3 (by decide))
      | succ p1 =>
          cases p1 with
          | zero =>
              -- `pos = 1` ↦ `base + 2`
              simpa [smoothLastCoreML_smooth, h] using (hC 2 (by decide))
          | succ p2 =>
              cases p2 with
              | zero =>
                  -- `pos = 2` ↦ `base + 1`
                  simpa [smoothLastCoreML_smooth, h] using (hC 1 (by decide))
              | succ p3 =>
                  cases p3 with
                  | zero =>
                      -- `pos = 3` ↦ `base + 0`
                      simpa [smoothLastCoreML_smooth, h] using (hC 0 (by decide))
                  | succ p4 =>
                      exfalso
                      have : Nat.succ (Nat.succ (Nat.succ (Nat.succ p4))) < 4 := by
                        simpa [h] using hpos
                      have hge : 4 ≤ Nat.succ (Nat.succ (Nat.succ (Nat.succ p4))) :=
                        Nat.succ_le_succ
                          (Nat.succ_le_succ
                            (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))))
                      exact (Nat.not_lt_of_ge hge) this

private lemma smoothLastCoreML_smooth_ge_base
    {n : Nat} {isB : Bool} (r : Nat) :
    4 * n - 4 ≤ smoothLastCoreML_smooth n isB r := by
  cases n with
  | zero =>
      simp [smoothLastCoreML_smooth]
  | succ k =>
      have hbase : 4 * (k + 1) - 4 = 4 * k := by
        simp [Nat.mul_succ]
      -- Avoid `simp` rewriting `a - b ≤ c` into `a ≤ c + b` by working directly with the unfolded
      -- definition and case-splitting on the finite `pos := r % 4`.
      unfold smoothLastCoreML_smooth
      -- Rewrite the base arithmetic for `n = k+1`.
      simp [hbase]
      set pos : Nat := r % 4 with hposDef
      have hpos : pos < 4 := by
        have : r % 4 < 4 := Nat.mod_lt r (by decide : 0 < 4)
        simpa [pos, hposDef] using this
      cases isB <;> interval_cases pos <;>
        simp [Nat.le_add_right]

private lemma smoothLastCoreML_smooth_ne_self_of_in_removed
    {n : Nat} {isB : Bool} (hn : 0 < n) {r : Nat}
    (hr : 4 * n - 4 ≤ r) (hrlt : r < 4 * n) :
    smoothLastCoreML_smooth n isB r ≠ r := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hbase : 4 * (k + 1) - 4 = 4 * k := by
    simp [Nat.mul_succ]
  have hr' : 4 * k ≤ r := by simpa [hbase] using hr
  have hrlt' : r < 4 * k + 4 := by
    simpa [Nat.mul_succ, Nat.add_assoc] using hrlt

  let off := r - 4 * k
  have hoff : off < 4 := by
    have : r - 4 * k < (4 * k + 4) - 4 * k := Nat.sub_lt_sub_right hr' hrlt'
    simpa [off, Nat.add_sub_cancel_left] using this

  have r_eq : r = 4 * k + off := by
    have : off + 4 * k = r := by
      simpa [off] using (Nat.sub_add_cancel hr')
    have : 4 * k + off = r := by
      simpa [Nat.add_comm] using this
    exact this.symm

  -- Reduce to the four offsets `0,1,2,3` using the bound `hoff : off < 4`.
  rw [r_eq]
  cases isB with
  | false =>
      interval_cases off
      · -- `off = 0`
        intro hEq
        have h' : 4 * k + 1 = 4 * k := by
          simpa [smoothLastCoreML_smooth, hbase, Nat.add_mod, Nat.mul_mod_right] using hEq
        have h'' : 4 * k + 1 = 4 * k + 0 := Eq.trans h' (Eq.symm (Nat.add_zero (4 * k)))
        have : (1 : Nat) = 0 := Nat.add_left_cancel h''
        exact (by decide : (1 : Nat) ≠ 0) this
      · -- `off = 1`
        intro hEq
        have h' : 4 * k = 4 * k + 1 := by
          simpa [smoothLastCoreML_smooth, hbase, Nat.add_mod, Nat.mul_mod_right] using hEq
        have : (0 : Nat) = 1 := Nat.add_left_cancel h'
        exact (by decide : (0 : Nat) ≠ 1) this
      · -- `off = 2`
        intro hEq
        have h' : 4 * k + 3 = 4 * k + 2 := by
          simpa [smoothLastCoreML_smooth, hbase, Nat.add_mod, Nat.mul_mod_right] using hEq
        have : (3 : Nat) = 2 := Nat.add_left_cancel h'
        exact (by decide : (3 : Nat) ≠ 2) this
      · -- `off = 3`
        intro hEq
        have h' : 4 * k + 2 = 4 * k + 3 := by
          simpa [smoothLastCoreML_smooth, hbase, Nat.add_mod, Nat.mul_mod_right] using hEq
        have : (2 : Nat) = 3 := Nat.add_left_cancel h'
        exact (by decide : (2 : Nat) ≠ 3) this
  | true =>
      interval_cases off
      · -- `off = 0`
        intro hEq
        have h' : 4 * k + 3 = 4 * k := by
          simpa [smoothLastCoreML_smooth, hbase, Nat.add_mod, Nat.mul_mod_right] using hEq
        have h'' : 4 * k + 3 = 4 * k + 0 := Eq.trans h' (Eq.symm (Nat.add_zero (4 * k)))
        have : (3 : Nat) = 0 := Nat.add_left_cancel h''
        exact (by decide : (3 : Nat) ≠ 0) this
      · -- `off = 1`
        intro hEq
        have h' : 4 * k + 2 = 4 * k + 1 := by
          simpa [smoothLastCoreML_smooth, hbase, Nat.add_mod, Nat.mul_mod_right] using hEq
        have : (2 : Nat) = 1 := Nat.add_left_cancel h'
        exact (by decide : (2 : Nat) ≠ 1) this
      · -- `off = 2`
        intro hEq
        have h' : 4 * k + 1 = 4 * k + 2 := by
          simpa [smoothLastCoreML_smooth, hbase, Nat.add_mod, Nat.mul_mod_right] using hEq
        have : (1 : Nat) = 2 := Nat.add_left_cancel h'
        exact (by decide : (1 : Nat) ≠ 2) this
      · -- `off = 3`
        intro hEq
        have h' : 4 * k = 4 * k + 3 := by
          simpa [smoothLastCoreML_smooth, hbase, Nat.add_mod, Nat.mul_mod_right] using hEq
        have : (0 : Nat) = 3 := Nat.add_left_cancel h'
        exact (by decide : (0 : Nat) ≠ 3) this

private lemma smoothLastCoreML_smooth_invol_of_in_removed
    {n : Nat} {isB : Bool} (hn : 0 < n) {r : Nat}
    (hr : 4 * n - 4 ≤ r) (hrlt : r < 4 * n) :
    smoothLastCoreML_smooth n isB (smoothLastCoreML_smooth n isB r) = r := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hbase : 4 * (k + 1) - 4 = 4 * k := by
    simp [Nat.mul_succ]
  have hr' : 4 * k ≤ r := by simpa [hbase] using hr
  have hrlt' : r < 4 * k + 4 := by
    simpa [Nat.mul_succ, Nat.add_assoc] using hrlt

  let off := r - 4 * k
  have hoff : off < 4 := by
    have : r - 4 * k < (4 * k + 4) - 4 * k := Nat.sub_lt_sub_right hr' hrlt'
    simpa [off, Nat.add_sub_cancel_left] using this

  have r_eq : r = 4 * k + off := by
    have : off + 4 * k = r := by
      simpa [off] using (Nat.sub_add_cancel hr')
    have : 4 * k + off = r := by
      simpa [Nat.add_comm] using this
    exact this.symm

  rw [r_eq]
  interval_cases off <;> cases isB <;>
    simp [smoothLastCoreML_smooth, hbase, Nat.add_mod, Nat.mul_mod_right]

theorem smoothLastCoreML_exitFromExternal_invol
    {n : Nat} {arcNbr : Array Nat} {isB : Bool} {x : Nat}
    (hn : 0 < n)
    (hg : PDGraph.Valid {freeLoops := 0, n := n, arcNbr := arcNbr})
    (hx : x < 4 * n - 4)
    (hinc : 4 * n - 4 ≤ arcNbr[x]!) :
    let y := smoothLastCoreML_exitFromExternal n arcNbr isB x
    y < 4 * n - 4 ∧ y ≠ x ∧ smoothLastCoreML_exitFromExternal n arcNbr isB y = x := by
  classical
  -- Remove the top-level `let y := ...`.
  dsimp
  let base : Nat := 4 * n - 4
  have hx_base : x < base := by simpa [base] using hx
  have hinc_base : base ≤ arcNbr[x]! := by simpa [base] using hinc

  have hn1 : 1 ≤ n := Nat.succ_le_iff.mp hn
  have h4le : 4 ≤ 4 * n := by
    simpa using (Nat.mul_le_mul_left 4 hn1)
  have hbase4 : base + 4 = 4 * n := by
    simp [base, Nat.sub_add_cancel h4le]

  have hx_m : x < 4 * n := Nat.lt_of_lt_of_le hx_base (Nat.sub_le _ _)
  let r0 : Nat := arcNbr[x]!
  have hr0_lt : r0 < 4 * n := PDGraph.Valid.get_lt hg (i := x) hx_m
  have hr0_ne_x : r0 ≠ x := PDGraph.Valid.get_ne hg (i := x) hx_m
  have harc_r0 : arcNbr[r0]! = x := PDGraph.Valid.invol hg (i := x) hx_m

  let s0 : Nat := smoothLastCoreML_smooth n isB r0
  have hs0_lt : s0 < 4 * n := smoothLastCoreML_smooth_lt (n := n) (isB := isB) hn r0
  have hs0_ge : base ≤ s0 := by
    simpa [base, s0] using (smoothLastCoreML_smooth_ge_base (n := n) (isB := isB) r0)
  let y1 : Nat := arcNbr[s0]!
  have hy1_lt_m : y1 < 4 * n := PDGraph.Valid.get_lt hg (i := s0) hs0_lt
  have hy1_ne_s0 : y1 ≠ s0 := PDGraph.Valid.get_ne hg (i := s0) hs0_lt
  have harc_y1 : arcNbr[y1]! = s0 := PDGraph.Valid.invol hg (i := s0) hs0_lt

  by_cases hy1_base : y1 < base
  · -- First step exits immediately: `exitFromExternal x = y1`.
    have hy : smoothLastCoreML_exitFromExternal n arcNbr isB x = y1 := by
      simp [smoothLastCoreML_exitFromExternal, smoothLastCoreML_exitFromExternalAux, base,
        r0, s0, y1, hy1_base]

    refine And.intro (by simpa [hy]) (And.intro ?_ ?_)
    · -- `exitFromExternal x ≠ x`
      intro hEq
      have hy1_eq_x : y1 = x := by simpa [hy] using hEq
      have hs0_eq_r0 : s0 = r0 := by
        have : arcNbr[x]! = s0 := by simpa [y1, hy1_eq_x] using harc_y1
        simpa [r0] using this.symm
      have hs0_ne_r0 :
          smoothLastCoreML_smooth n isB r0 ≠ r0 :=
        smoothLastCoreML_smooth_ne_self_of_in_removed (n := n) (isB := isB) hn
          (r := r0) hinc_base hr0_lt
      exact hs0_ne_r0 (by simpa [s0] using hs0_eq_r0)
    · -- Involution: `exitFromExternal y1 = x`.
      have hs0_invol : smoothLastCoreML_smooth n isB s0 = r0 := by
        have : smoothLastCoreML_smooth n isB (smoothLastCoreML_smooth n isB r0) = r0 :=
          smoothLastCoreML_smooth_invol_of_in_removed (n := n) (isB := isB) hn
            (r := r0) hinc_base hr0_lt
        simpa [s0] using this
      have : smoothLastCoreML_exitFromExternal n arcNbr isB y1 = x := by
        simp [smoothLastCoreML_exitFromExternal, smoothLastCoreML_exitFromExternalAux, base,
          y1, harc_y1, hs0_invol, harc_r0, hx_base, hy1_base]
      simpa [hy] using this
  · -- First step stays inside the removed region; exit on the second step.
    have hy1_ge : base ≤ y1 := Nat.le_of_not_gt hy1_base
    let s1 : Nat := smoothLastCoreML_smooth n isB y1
    have hs1_lt : s1 < 4 * n := smoothLastCoreML_smooth_lt (n := n) (isB := isB) hn y1
    have hs1_ge : base ≤ s1 := by
      simpa [base, s1] using (smoothLastCoreML_smooth_ge_base (n := n) (isB := isB) y1)
    let y2 : Nat := arcNbr[s1]!
    have hy2_lt_m : y2 < 4 * n := PDGraph.Valid.get_lt hg (i := s1) hs1_lt
    have hy2_ne_s1 : y2 ≠ s1 := PDGraph.Valid.get_ne hg (i := s1) hs1_lt
    have harc_y2 : arcNbr[y2]! = s1 := PDGraph.Valid.invol hg (i := s1) hs1_lt

    have hy1_ne_r0 : y1 ≠ r0 := by
      intro hEq
      have : arcNbr[r0]! = s0 := by simpa [hEq] using harc_y1
      have : base ≤ x := by simpa [harc_r0] using (hs0_ge.trans_eq this.symm)
      exact (Nat.not_lt_of_ge this) hx_base

    -- `y2` must be external: otherwise we get a fifth element in the 4-node removed block.
    have hy2_base : y2 < base := by
      by_contra hy2_ge
      have hy2_ge' : base ≤ y2 := Nat.le_of_not_gt hy2_ge
      have hy2_lt_base4 : y2 < base + 4 := by simpa [hbase4] using hy2_lt_m
      have hr0_lt_base4 : r0 < base + 4 := by simpa [hbase4] using hr0_lt
      have hs0_lt_base4 : s0 < base + 4 := by simpa [hbase4] using hs0_lt
      have hy1_lt_base4 : y1 < base + 4 := by simpa [hbase4] using hy1_lt_m
      have hs1_lt_base4 : s1 < base + 4 := by simpa [hbase4] using hs1_lt

      let removed : Finset Nat := Finset.Ico base (base + 4)
      have hremoved_card : removed.card = 4 := by
        -- `card (Ico base (base+4)) = (base+4) - base = 4`
        simpa [removed] using (Nat.card_Ico base (base + 4))

      have hy2_mem : y2 ∈ removed := by
        have : base ≤ y2 ∧ y2 < base + 4 := ⟨hy2_ge', hy2_lt_base4⟩
        simpa [removed, Finset.mem_Ico] using this
      have hr0_mem : r0 ∈ removed := by
        have : base ≤ r0 ∧ r0 < base + 4 := ⟨hinc_base, hr0_lt_base4⟩
        simpa [removed, Finset.mem_Ico] using this
      have hs0_mem : s0 ∈ removed := by
        have : base ≤ s0 ∧ s0 < base + 4 := ⟨hs0_ge, hs0_lt_base4⟩
        simpa [removed, Finset.mem_Ico] using this
      have hy1_mem : y1 ∈ removed := by
        have : base ≤ y1 ∧ y1 < base + 4 := ⟨hy1_ge, hy1_lt_base4⟩
        simpa [removed, Finset.mem_Ico] using this
      have hs1_mem : s1 ∈ removed := by
        have : base ≤ s1 ∧ s1 < base + 4 := ⟨hs1_ge, hs1_lt_base4⟩
        simpa [removed, Finset.mem_Ico] using this

      -- The four nodes `{r0, s0, y1, s1}` are distinct and fill the removed block.
      have hs0_ne_r0 : s0 ≠ r0 := by
        intro hEq
        have hs0_ne_r0' :
            smoothLastCoreML_smooth n isB r0 ≠ r0 :=
          smoothLastCoreML_smooth_ne_self_of_in_removed (n := n) (isB := isB) hn
            (r := r0) hinc_base hr0_lt
        exact hs0_ne_r0' (by simpa [s0] using hEq)
      have hs1_ne_y1 : s1 ≠ y1 := by
        -- `smooth` has no fixed points on the removed block.
        have hs1_ne_y1' :
            smoothLastCoreML_smooth n isB y1 ≠ y1 :=
          smoothLastCoreML_smooth_ne_self_of_in_removed (n := n) (isB := isB) hn
            (r := y1) hy1_ge hy1_lt_m
        simpa [s1] using hs1_ne_y1'
      have hs1_ne_r0 : s1 ≠ r0 := by
        intro hEq
        have hs1_invol : smoothLastCoreML_smooth n isB s1 = y1 := by
          have : smoothLastCoreML_smooth n isB (smoothLastCoreML_smooth n isB y1) = y1 :=
            smoothLastCoreML_smooth_invol_of_in_removed (n := n) (isB := isB) hn
              (r := y1) hy1_ge hy1_lt_m
          simpa [s1] using this
        have hcongr :
            smoothLastCoreML_smooth n isB s1 = smoothLastCoreML_smooth n isB r0 :=
          congrArg (smoothLastCoreML_smooth n isB) hEq
        have : y1 = s0 := by simpa [hs1_invol, s0] using hcongr
        exact hy1_ne_s0 this
      have hs1_ne_s0 : s1 ≠ s0 := by
        intro hEq
        have hs0_invol : smoothLastCoreML_smooth n isB s0 = r0 := by
          have : smoothLastCoreML_smooth n isB (smoothLastCoreML_smooth n isB r0) = r0 :=
            smoothLastCoreML_smooth_invol_of_in_removed (n := n) (isB := isB) hn
              (r := r0) hinc_base hr0_lt
          simpa [s0] using this
        have hs1_invol : smoothLastCoreML_smooth n isB s1 = y1 := by
          have : smoothLastCoreML_smooth n isB (smoothLastCoreML_smooth n isB y1) = y1 :=
            smoothLastCoreML_smooth_invol_of_in_removed (n := n) (isB := isB) hn
              (r := y1) hy1_ge hy1_lt_m
          simpa [s1] using this
        have hcongr :
            smoothLastCoreML_smooth n isB s1 = smoothLastCoreML_smooth n isB s0 :=
          congrArg (smoothLastCoreML_smooth n isB) hEq
        have : y1 = r0 := by simpa [hs1_invol, hs0_invol] using hcongr
        exact hy1_ne_r0 this

      -- Build the finset `S` and show it has card `4`.
      let S : Finset Nat := insert s1 (insert y1 (insert s0 (insert r0 (∅ : Finset Nat))))
      have hS_subset : S ⊆ removed := by
        -- insert subset chain
        have h0 : (∅ : Finset Nat) ⊆ removed := Finset.empty_subset _
        have h1 : insert r0 (∅ : Finset Nat) ⊆ removed := Finset.insert_subset hr0_mem h0
        have h2 : insert s0 (insert r0 (∅ : Finset Nat)) ⊆ removed := Finset.insert_subset hs0_mem h1
        have h3 : insert y1 (insert s0 (insert r0 (∅ : Finset Nat))) ⊆ removed := Finset.insert_subset hy1_mem h2
        have h4 : insert s1 (insert y1 (insert s0 (insert r0 (∅ : Finset Nat)))) ⊆ removed :=
          Finset.insert_subset hs1_mem h3
        simpa [S] using h4

      have hr0_card : (insert r0 (∅ : Finset Nat)).card = 1 := by simp
      have hs0_not_mem : s0 ∉ insert r0 (∅ : Finset Nat) := by simp [hs0_ne_r0]
      have hs0_card : (insert s0 (insert r0 (∅ : Finset Nat))).card = 2 := by
        have := Finset.card_insert_of_notMem (s := insert r0 (∅ : Finset Nat)) (a := s0) hs0_not_mem
        simpa [hr0_card] using this
      have hy1_not_mem : y1 ∉ insert s0 (insert r0 (∅ : Finset Nat)) := by
        simp [hy1_ne_s0, hy1_ne_r0]
      have hy1_card : (insert y1 (insert s0 (insert r0 (∅ : Finset Nat)))).card = 3 := by
        have h :=
          Finset.card_insert_of_notMem
            (s := insert s0 (insert r0 (∅ : Finset Nat))) (a := y1) hy1_not_mem
        -- Keep the insert-chain form so we can rewrite using `hs0_card`.
        calc
          (insert y1 (insert s0 (insert r0 (∅ : Finset Nat)))).card =
              (insert s0 (insert r0 (∅ : Finset Nat))).card + 1 := h
          _ = 2 + 1 := by rw [hs0_card]
          _ = 3 := by simp
      have hs1_not_mem : s1 ∉ insert y1 (insert s0 (insert r0 (∅ : Finset Nat))) := by
        simp [hs1_ne_y1, hs1_ne_s0, hs1_ne_r0]
      have hS_card : S.card = 4 := by
        have h :=
          Finset.card_insert_of_notMem
            (s := insert y1 (insert s0 (insert r0 (∅ : Finset Nat)))) (a := s1) hs1_not_mem
        calc
          S.card =
              (insert y1 (insert s0 (insert r0 (∅ : Finset Nat)))).card + 1 := by
                simpa [S] using h
          _ = 3 + 1 := by rw [hy1_card]
          _ = 4 := by simp

      have hEq : S = removed := by
        apply Finset.eq_of_subset_of_card_le hS_subset
        -- `removed.card = 4 ≤ S.card = 4`
        simpa [hremoved_card, hS_card]

      have hy2_in_S : y2 ∈ S := by simpa [hEq] using hy2_mem
      -- Membership in `S` gives `y2 = r0 ∨ y2 = s0 ∨ y2 = y1 ∨ y2 = s1`.
      have : y2 = s1 ∨ y2 = y1 ∨ y2 = s0 ∨ y2 = r0 := by
        simpa [S] using hy2_in_S
      rcases this with hEq_s1 | hrest
      · -- `y2 = s1` contradicts `arcNbr` having no fixed points
        exact hy2_ne_s1 hEq_s1
      rcases hrest with hEq_y1 | hrest
      · -- `y2 = y1` forces `s1 = s0`, contradicting `hs1_ne_s0`
        have : arcNbr[y1]! = s1 := by simpa [y2, hEq_y1] using harc_y2
        have : s0 = s1 := by simpa [harc_y1] using this
        exact hs1_ne_s0 this.symm
      rcases hrest with hEq_s0 | hEq_r0
      · -- `y2 = s0` contradicts `arcNbr[s0]! = y1`
        have : arcNbr[s0]! = s1 := by simpa [y2, hEq_s0] using harc_y2
        have hy1_eq_s1 : y1 = s1 := by simpa [y1] using this
        exact hs1_ne_y1 hy1_eq_s1.symm
      · -- `y2 = r0` contradicts `arcNbr[r0]! = x < base`
        have : arcNbr[r0]! = s1 := by simpa [y2, hEq_r0] using harc_y2
        have : x = s1 := by simpa [harc_r0] using this
        exact Nat.not_lt_of_ge hs1_ge (by simpa [this] using hx_base)

    have hy : smoothLastCoreML_exitFromExternal n arcNbr isB x = y2 := by
      simp [smoothLastCoreML_exitFromExternal, smoothLastCoreML_exitFromExternalAux, base,
        r0, s0, y1, s1, y2, hy1_base, hy2_base]

    refine And.intro (by simpa [hy]) (And.intro ?_ ?_)
    · intro hEq
      have hy2_eq_x : y2 = x := by simpa [hy] using hEq
      have hr0_eq_s1 : r0 = s1 := by
        have : arcNbr[x]! = s1 := by simpa [hy2_eq_x] using harc_y2
        simpa [r0] using this
      have hs1_invol : smoothLastCoreML_smooth n isB s1 = y1 := by
        have : smoothLastCoreML_smooth n isB (smoothLastCoreML_smooth n isB y1) = y1 :=
          smoothLastCoreML_smooth_invol_of_in_removed (n := n) (isB := isB) hn
            (r := y1) hy1_ge hy1_lt_m
        simpa [s1] using this
      have hcongr : smoothLastCoreML_smooth n isB r0 = smoothLastCoreML_smooth n isB s1 :=
        congrArg (smoothLastCoreML_smooth n isB) hr0_eq_s1
      have : s0 = y1 := by simpa [s0, hs1_invol] using hcongr
      exact hy1_ne_s0 (this.symm)
    · have hs0_invol : smoothLastCoreML_smooth n isB s0 = r0 := by
        have : smoothLastCoreML_smooth n isB (smoothLastCoreML_smooth n isB r0) = r0 :=
          smoothLastCoreML_smooth_invol_of_in_removed (n := n) (isB := isB) hn
            (r := r0) hinc_base hr0_lt
        simpa [s0] using this
      have hs1_invol : smoothLastCoreML_smooth n isB s1 = y1 := by
        have : smoothLastCoreML_smooth n isB (smoothLastCoreML_smooth n isB y1) = y1 :=
          smoothLastCoreML_smooth_invol_of_in_removed (n := n) (isB := isB) hn
            (r := y1) hy1_ge hy1_lt_m
        simpa [s1] using this
      have : smoothLastCoreML_exitFromExternal n arcNbr isB y2 = x := by
        have hs0_nlt : ¬ s0 < base := Nat.not_lt_of_ge hs0_ge
        simp [smoothLastCoreML_exitFromExternal, smoothLastCoreML_exitFromExternalAux, base,
          y2, harc_y2, hs1_invol, harc_y1, hs0_invol, harc_r0, hy2_base, hy1_base, hx_base, hs0_nlt]
      simpa [hy] using this

/-!
## Validity preservation for the smoothing rewiring

The executable-facing checker `PDGraph.validate` works over the last-crossing smoothing algorithm,
but Phase‑1 proofs need a Prop-level invariant that survives the local rewiring step.
-/

theorem smoothLastCoreML_exitFromExternal_inc
    {n : Nat} {arcNbr : Array Nat} {isB : Bool} {x : Nat}
    (hn : 0 < n)
    (hg : PDGraph.Valid {freeLoops := 0, n := n, arcNbr := arcNbr})
    (hx : x < 4 * n - 4)
    (hinc : 4 * n - 4 ≤ arcNbr[x]!) :
    let y := smoothLastCoreML_exitFromExternal n arcNbr isB x
    4 * n - 4 ≤ arcNbr[y]! := by
  classical
  -- Use the already-proved involution lemma to rule out fuel exhaustion and focus on the
  -- concrete “exit” branch, where `y` is the external endpoint paired with some removed index.
  have hinvol :=
    (smoothLastCoreML_exitFromExternal_invol (n := n) (arcNbr := arcNbr) (isB := isB) (x := x)
      hn hg hx hinc)
  -- Name the output `y` and keep its basic properties.
  let y := smoothLastCoreML_exitFromExternal n arcNbr isB x
  have hy_lt : y < 4 * n - 4 := hinvol.1
  have hy_ne : y ≠ x := hinvol.2.1

  -- Unfold the computation for fuel `4`, splitting on the first exit-test. If the first exit-test
  -- fails, we split again; the “never exits” branch contradicts `y ≠ x`.
  let base : Nat := 4 * n - 4
  have hx_base : x < base := by simpa [base] using hx

  -- Some arithmetic helpers.
  have hn1 : 1 ≤ n := Nat.succ_le_iff.mp hn
  have h4le : 4 ≤ 4 * n := by
    simpa using (Nat.mul_le_mul_left 4 hn1)
  have hbase4 : base + 4 = 4 * n := by
    simp [base, Nat.sub_add_cancel h4le]

  -- For any `r'` produced by `smooth`, we can show `r' < 4*n` and hence use `PDGraph.Valid.invol`.
  have hsmooth_lt : ∀ r, smoothLastCoreML_smooth n isB r < 4 * n :=
    fun r => smoothLastCoreML_smooth_lt (n := n) (isB := isB) hn r

  -- Step 0: start from the removed neighbor `r0 := arcNbr[x]!`.
  have hx_m : x < 4 * n := Nat.lt_of_lt_of_le hx_base (Nat.sub_le _ _)
  let r0 : Nat := arcNbr[x]!
  have hr0_lt : r0 < 4 * n := PDGraph.Valid.get_lt hg (i := x) hx_m

  -- Unfold one step, splitting on whether we already exit.
  let s0 : Nat := smoothLastCoreML_smooth n isB r0
  have hs0_lt : s0 < 4 * n := hsmooth_lt r0
  let y1 : Nat := arcNbr[s0]!

  by_cases hy1_base : y1 < base
  · -- We exit immediately with `y = y1`; then `arcNbr[y]! = s0 ≥ base`.
    have hy_eq : y = y1 := by
      -- If we exit at the first step, the recursive definition returns `y1`.
      simp [y, smoothLastCoreML_exitFromExternal, smoothLastCoreML_exitFromExternalAux, base,
        r0, s0, y1, hy1_base]
    have harc_y1 : arcNbr[y1]! = s0 := by
      -- `y1 = arcNbr[s0]!`, so involution at `s0` gives `arcNbr[y1]! = s0`.
      have := PDGraph.Valid.invol hg (i := s0) hs0_lt
      simpa [y1] using this
    have hs0_ge : base ≤ s0 := Nat.le_trans (by rfl) (smoothLastCoreML_smooth_ge_base (n := n) (isB := isB) r0)
    -- Conclude.
    have : base ≤ arcNbr[y]! := by simpa [hy_eq, harc_y1] using hs0_ge
    simpa [base, y] using this
  · -- Otherwise, we take a second step. If we still don't exit, we can take a third, etc.
    -- We iterate at most 4 times; the “never exits” branch forces `y = x`, contradicting `hy_ne`.
    let s1 : Nat := smoothLastCoreML_smooth n isB y1
    have hs1_lt : s1 < 4 * n := hsmooth_lt y1
    let y2 : Nat := arcNbr[s1]!
    by_cases hy2_base : y2 < base
    · have hy_eq : y = y2 := by
        simp [y, smoothLastCoreML_exitFromExternal, smoothLastCoreML_exitFromExternalAux, base,
          r0, s0, y1, s1, y2, hy1_base, hy2_base]
      have harc_y2 : arcNbr[y2]! = s1 := by
        have := PDGraph.Valid.invol hg (i := s1) hs1_lt
        simpa [y2] using this
      have hs1_ge : base ≤ s1 := Nat.le_trans (by rfl) (smoothLastCoreML_smooth_ge_base (n := n) (isB := isB) y1)
      have : base ≤ arcNbr[y]! := by simpa [hy_eq, harc_y2] using hs1_ge
      simpa [base, y] using this
    ·
      let s2 : Nat := smoothLastCoreML_smooth n isB y2
      have hs2_lt : s2 < 4 * n := hsmooth_lt y2
      let y3 : Nat := arcNbr[s2]!
      by_cases hy3_base : y3 < base
      · have hy_eq : y = y3 := by
          simp [y, smoothLastCoreML_exitFromExternal, smoothLastCoreML_exitFromExternalAux, base,
            r0, s0, y1, s1, y2, s2, y3, hy1_base, hy2_base, hy3_base]
        have harc_y3 : arcNbr[y3]! = s2 := by
          have := PDGraph.Valid.invol hg (i := s2) hs2_lt
          simpa [y3] using this
        have hs2_ge : base ≤ s2 := Nat.le_trans (by rfl) (smoothLastCoreML_smooth_ge_base (n := n) (isB := isB) y2)
        have : base ≤ arcNbr[y]! := by simpa [hy_eq, harc_y3] using hs2_ge
        simpa [base, y] using this
      ·
        let s3 : Nat := smoothLastCoreML_smooth n isB y3
        have hs3_lt : s3 < 4 * n := hsmooth_lt y3
        let y4 : Nat := arcNbr[s3]!
        by_cases hy4_base : y4 < base
        · have hy_eq : y = y4 := by
            simp [y, smoothLastCoreML_exitFromExternal, smoothLastCoreML_exitFromExternalAux, base,
              r0, s0, y1, s1, y2, s2, y3, s3, y4, hy1_base, hy2_base, hy3_base, hy4_base]
          have harc_y4 : arcNbr[y4]! = s3 := by
            have := PDGraph.Valid.invol hg (i := s3) hs3_lt
            simpa [y4] using this
          have hs3_ge : base ≤ s3 := Nat.le_trans (by rfl) (smoothLastCoreML_smooth_ge_base (n := n) (isB := isB) y3)
          have : base ≤ arcNbr[y]! := by simpa [hy_eq, harc_y4] using hs3_ge
          simpa [base, y] using this
        ·
          -- Fuel exhaustion: the auxiliary returns `x`, hence `y = x`, contradicting `hy_ne`.
          have hy_eq_x : y = x := by
            simp [y, smoothLastCoreML_exitFromExternal, smoothLastCoreML_exitFromExternalAux, base,
              r0, s0, y1, s1, y2, s2, y3, s3, y4, hy1_base, hy2_base, hy3_base, hy4_base]
          exact (hy_ne hy_eq_x).elim

private theorem getBang_eq_getElem (a : Array Nat) (i : Nat) (hi : i < a.size) :
    a[i]! = a[i]'hi := by
  simp [hi]

theorem smoothLastCoreML_valid
    {n : Nat} {arcNbr : Array Nat} {isB : Bool}
    (hn : 0 < n)
    (hg : PDGraph.Valid {freeLoops := 0, n := n, arcNbr := arcNbr}) :
    PDGraph.Valid {freeLoops := 0, n := n - 1, arcNbr := smoothLastCoreML_rewire n arcNbr isB} := by
  classical
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hn' : 0 < k + 1 := Nat.succ_pos k
  have hsize : arcNbr.size = 4 * (k + 1) := by
    simpa [PDGraph.numHalfEdges] using (PDGraph.Valid.size_eq hg)
  have hbase : 4 * (k + 1) - 4 = 4 * k := by
    simp [Nat.mul_succ]
  let base : Nat := 4 * k
  let newNbr : Array Nat := smoothLastCoreML_rewire (k + 1) arcNbr isB

  have hnewSize : newNbr.size = base := by
    simp [newNbr, smoothLastCoreML_rewire, base, hbase]

  refine ⟨?_, ?_⟩
  · -- size
    simpa [newNbr, PDGraph.numHalfEdges] using hnewSize
  · -- involution/fixed-point-free
    intro i hi
    have hi_old : i < 4 * (k + 1) := by
      have : base ≤ 4 * (k + 1) := by
        simpa [base, Nat.mul_succ, Nat.add_assoc] using (Nat.le_add_right (4 * k) 4)
      exact Nat.lt_of_lt_of_le (by simpa [base] using hi) this
    have hi_base : i < base := by
      simpa [PDGraph.numHalfEdges, base] using hi
    let p : Nat := arcNbr[i]!
    by_cases hp : p < base
    · -- `i` stays paired with `p`.
      have hp_old : p < 4 * (k + 1) := Nat.lt_of_lt_of_le hp (by
        have : base ≤ 4 * (k + 1) := by
          simpa [base, Nat.mul_succ, Nat.add_assoc] using (Nat.le_add_right (4 * k) 4)
        exact this)
      have hp_ne : p ≠ i := PDGraph.Valid.get_ne hg (i := i) hi_old
      have harc_p : arcNbr[p]! = i := by
        simpa [p] using (PDGraph.Valid.invol hg (i := i) hi_old)
      have harc_p_lt : arcNbr[p]! < base := by simpa [harc_p, base] using hi_base
      have hnew_i : newNbr[i]! = p := by
        -- `newNbr` is `ofFn` on the external half-edges `i < base`.
        have hi' : i < newNbr.size := by simpa [hnewSize] using hi
        have : newNbr[i]'hi' = p := by
          -- unfold `newNbr` and `smoothLastCoreML_rewire`, then use the `p < base` branch.
          simp [newNbr, smoothLastCoreML_rewire, base, hbase, p, hp, hi_base]
        simpa [getBang_eq_getElem (a := newNbr) (i := i) hi'] using this
      have hnew_p : newNbr[p]! = i := by
        have hp' : p < newNbr.size := by simpa [hnewSize] using hp
        have : newNbr[p]'hp' = i := by
          simp [newNbr, smoothLastCoreML_rewire, base, hbase, p, hp, harc_p_lt, harc_p, hi_base]
        simpa [getBang_eq_getElem (a := newNbr) (i := p) hp'] using this
      refine ⟨?_, ?_⟩
      · -- `j < numHalfEdges`
        simpa [newNbr, PDGraph.numHalfEdges, hnew_i, base] using hp
      · refine ⟨?_, ?_⟩
        · -- `j ≠ i`
          simpa [newNbr, hnew_i] using hp_ne
        · -- `arcNbr[j]! = i`
          simpa [newNbr, hnew_i] using hnew_p
    · -- incident: use `exitFromExternal` pairing.
      have hp_ge : base ≤ p := Nat.le_of_not_gt hp
      let y : Nat := smoothLastCoreML_exitFromExternal (k + 1) arcNbr isB i
      have hinvol :=
        smoothLastCoreML_exitFromExternal_invol (n := k + 1) (arcNbr := arcNbr) (isB := isB) (x := i)
          hn' hg (by simpa [base, hbase] using hi) (by simpa [p, base, hbase] using hp_ge)
      have hy_lt : y < base := hinvol.1
      have hy_ne : y ≠ i := hinvol.2.1
      have hy_invol : smoothLastCoreML_exitFromExternal (k + 1) arcNbr isB y = i := hinvol.2.2
      have hy_inc : base ≤ arcNbr[y]! := by
        -- The exit endpoint is also incident to the removed region.
        simpa [y, base, hbase] using
          (smoothLastCoreML_exitFromExternal_inc (n := k + 1) (arcNbr := arcNbr) (isB := isB) (x := i)
            hn' hg (by simpa [base, hbase] using hi) (by simpa [p, base, hbase] using hp_ge))
      have hnew_i : newNbr[i]! = y := by
        have hi' : i < newNbr.size := by simpa [hnewSize] using hi
        have : newNbr[i]'hi' = y := by
          simp [newNbr, smoothLastCoreML_rewire, base, hbase, p, hp, hi, y]
        simpa [getBang_eq_getElem (a := newNbr) (i := i) hi'] using this
      have hnew_y : newNbr[y]! = i := by
        have hy' : y < newNbr.size := by simpa [hnewSize] using hy_lt
        have : newNbr[y]'hy' = i := by
          have hy_not_lt : ¬ arcNbr[y]! < base := Nat.not_lt_of_ge hy_inc
          simp [newNbr, smoothLastCoreML_rewire, base, hbase, hy_not_lt, hy_invol, y]
        simpa [getBang_eq_getElem (a := newNbr) (i := y) hy'] using this
      refine ⟨?_, ?_⟩
      · -- `j < numHalfEdges`
        simpa [newNbr, PDGraph.numHalfEdges, hnew_i, base] using hy_lt
      · refine ⟨?_, ?_⟩
        · -- `j ≠ i`
          simpa [newNbr, hnew_i] using hy_ne
        · -- `arcNbr[j]! = i`
          simpa [newNbr, hnew_i] using hnew_y

end

end Kauffman

end Knot
end Topology
end HeytingLean
