import HeytingLean.Topology.Knot.BracketMathlib
import HeytingLean.Topology.Knot.Reidemeister

/-! NOTE: This older Reidemeister-II proof attempt is kept for reference but is too slow to build. -/

/-!
# Knot theory: Reidemeister-II invariance (Mathlib proof layer)

This module proves that the Mathlib-layer Kauffman bracket `bracketGraphML` is invariant under a
Reidemeister-II cancelling pair, using the evaluator’s R2 short-circuit (`r2RemoveLast`).
-/

namespace HeytingLean
namespace Topology
namespace Knot

namespace Kauffman

open scoped LaurentPolynomial
open Reidemeister

noncomputable section

-- NOTE: Avoid giant heartbeat overrides in proof modules; keep proofs lightweight.
set_option maxHeartbeats 2000000

private theorem n_ge_two_of_r2RemoveLast_ok {g g0 : PDGraph} (h : Reidemeister.r2RemoveLast g = .ok g0) :
    2 ≤ g.n := by
  cases hvg : PDGraph.validate g with
  | error e =>
      simp [Reidemeister.r2RemoveLast, hvg] at h
  | ok hv =>
      cases hv
      by_contra hnge
      have hnlt : g.n < 2 := Nat.lt_of_not_ge hnge
      have hcontra := h
      simp [Reidemeister.r2RemoveLast, hvg, hnlt] at hcontra

private theorem arc_base2_0_eq_base1_1_of_r2RemoveLast_ok {g g0 : PDGraph}
    (h : Reidemeister.r2RemoveLast g = .ok g0) :
    let m := g.numHalfEdges
    let base1 := m - 8
    let base2 := m - 4
    g.arcNbr[base2 + 0]! = base1 + 1 := by
  classical
  cases hvg : PDGraph.validate g with
  | error e =>
      simp [Reidemeister.r2RemoveLast, hvg] at h
  | ok hv =>
      cases hv
      have hnlt : ¬ g.n < 2 := by
        intro hnlt
        have hcontra := h
        simp [Reidemeister.r2RemoveLast, hvg, hnlt] at hcontra

      let m := g.numHalfEdges
      let base1 := m - 8
      let base2 := m - 4

      -- The first internal-arc check must be false in the success path.
      set cond1 :=
        (g.arcNbr[base1 + 1]! != base2 + 0 || g.arcNbr[base2 + 0]! != base1 + 1) with hcond1
      have hcond1false : cond1 = false := by
        cases hc : cond1 with
        | true =>
            have hcontra := h
            simp [Reidemeister.r2RemoveLast, hvg, hnlt, m, base1, base2, hcond1, hc] at hcontra
        | false => rfl

      have hparts :
          (g.arcNbr[base1 + 1]! != base2 + 0) = false ∧ (g.arcNbr[base2 + 0]! != base1 + 1) = false := by
        -- unfold `cond1` and split the `|| = false`.
        have h' : (g.arcNbr[base1 + 1]! != base2 + 0 || g.arcNbr[base2 + 0]! != base1 + 1) = false := by
          simpa [hcond1] using hcond1false
        exact Bool.or_eq_false.mp h'

      have hne : ¬ g.arcNbr[base2 + 0]! ≠ base1 + 1 := by
        intro hne
        have hb : (g.arcNbr[base2 + 0]! != base1 + 1) = true := (bne_iff_ne).2 hne
        -- contradiction: RHS is forced to be `false`.
        exact Bool.false_ne_true (hparts.2.trans hb)
      exact (not_ne_iff).1 hne

private theorem arc_base2_1_lt_base1_of_r2RemoveLast_ok {g g0 : PDGraph}
    (h : Reidemeister.r2RemoveLast g = .ok g0) :
    let m := g.numHalfEdges
    let base1 := m - 8
    let base2 := m - 4
    g.arcNbr[base2 + 1]! < base1 := by
  classical
  cases hvg : PDGraph.validate g with
  | error e =>
      simp [Reidemeister.r2RemoveLast, hvg] at h
  | ok hv =>
      cases hv
      have hnlt : ¬ g.n < 2 := by
        intro hnlt
        have hcontra := h
        simp [Reidemeister.r2RemoveLast, hvg, hnlt] at hcontra

      let m := g.numHalfEdges
      let base1 := m - 8
      let base2 := m - 4

      -- Both internal-arc checks must be false in the success path; we only need the fact that we get past them.
      set cond1 :=
        (g.arcNbr[base1 + 1]! != base2 + 0 || g.arcNbr[base2 + 0]! != base1 + 1) with hcond1
      have hcond1false : cond1 = false := by
        cases hc : cond1 with
        | true =>
            have hcontra := h
            simp [Reidemeister.r2RemoveLast, hvg, hnlt, m, base1, base2, hcond1, hc] at hcontra
        | false => rfl

      set cond2 :=
        (g.arcNbr[base1 + 2]! != base2 + 3 || g.arcNbr[base2 + 3]! != base1 + 2) with hcond2
      have hcond2false : cond2 = false := by
        cases hc : cond2 with
        | true =>
            have hcontra := h
            simp [Reidemeister.r2RemoveLast, hvg, hnlt, m, base1, base2, hcond1, hcond1false, hcond2, hc] at hcontra
        | false => rfl

      let y := g.arcNbr[base2 + 1]!
      -- External endpoint check must be false; in particular `y < base1`.
      set condExt := (y >= base1) with hcondExt
      have hylt : y < base1 := by
        -- If `y ≥ base1`, the external-endpoint check triggers and the function errors.
        have hNotGe : ¬ y >= base1 := by
          intro hyGe
          have hcontra := h
          simp [Reidemeister.r2RemoveLast, hvg, hnlt, m, base1, base2, hcond1, hcond1false, hcond2, hcond2false, y, hyGe] at hcontra
        exact Nat.lt_of_not_ge hNotGe
      simpa [y] using hylt

theorem r2RemoveLast_n_eq {g g0 : PDGraph} (h : Reidemeister.r2RemoveLast g = .ok g0) :
    g0.n = g.n - 2 := by
  classical
  cases hvg : PDGraph.validate g with
  | error e =>
      simp [Reidemeister.r2RemoveLast, hvg] at h
  | ok hv =>
      cases hv
      have hnlt : ¬ g.n < 2 := by
        intro hnlt
        have hcontra := h
        simp [Reidemeister.r2RemoveLast, hvg, hnlt] at hcontra
      let m := g.numHalfEdges
      let base1 := m - 8
      let base2 := m - 4

      -- Expose the success path by forcing all checks to be false (otherwise we would contradict `h`).
      set cond1 :=
        (g.arcNbr[base1 + 1]! != base2 + 0 || g.arcNbr[base2 + 0]! != base1 + 1) with hcond1
      have hcond1false : cond1 = false := by
        cases hc : cond1 with
        | true =>
            have hcontra := h
            simp [Reidemeister.r2RemoveLast, hvg, hnlt, m, base1, base2, hcond1, hc] at hcontra
        | false => rfl

      set cond2 :=
        (g.arcNbr[base1 + 2]! != base2 + 3 || g.arcNbr[base2 + 3]! != base1 + 2) with hcond2
      have hcond2false : cond2 = false := by
        cases hc : cond2 with
        | true =>
            have hcontra := h
            simp [Reidemeister.r2RemoveLast, hvg, hnlt, m, base1, base2, hcond1, hcond1false, hcond2, hc] at hcontra
        | false => rfl

      let x := g.arcNbr[base1 + 0]!
      let u := g.arcNbr[base1 + 3]!
      let y := g.arcNbr[base2 + 1]!
      let v := g.arcNbr[base2 + 2]!

      -- External endpoint check.
      set condExt := (x >= base1 || u >= base1 || y >= base1 || v >= base1) with hcondExt
      have hcondExtfalse : condExt = false := by
        cases hc : condExt with
        | true =>
            have hcontra := h
            simp [Reidemeister.r2RemoveLast, hvg, hnlt, m, base1, base2, hcond1, hcond1false, hcond2, hcond2false, x, u, y,
              v, hcondExt, hc] at hcontra
        | false => rfl

      set condBack1 := (g.arcNbr[x]! != base1 + 0 || g.arcNbr[u]! != base1 + 3) with hcondBack1
      have hcondBack1false : condBack1 = false := by
        cases hc : condBack1 with
        | true =>
            have hcontra := h
            simp [Reidemeister.r2RemoveLast, hvg, hnlt, m, base1, base2, hcond1, hcond1false, hcond2, hcond2false, x, u, y,
              v, hcondExt, hcondExtfalse, hcondBack1, hc] at hcontra
        | false => rfl

      set condBack2 := (g.arcNbr[y]! != base2 + 1 || g.arcNbr[v]! != base2 + 2) with hcondBack2
      have hcondBack2false : condBack2 = false := by
        cases hc : condBack2 with
        | true =>
            have hcontra := h
            simp [Reidemeister.r2RemoveLast, hvg, hnlt, m, base1, base2, hcond1, hcond1false, hcond2, hcond2false, x, u, y,
              v, hcondExt, hcondExtfalse, hcondBack1, hcondBack1false, hcondBack2, hc] at hcontra
        | false => rfl

      let nbr := setPair! (setPair! (g.arcNbr.take base1) x y) u v
      let gOut : PDGraph := { freeLoops := g.freeLoops, n := g.n - 2, arcNbr := nbr }

      have h' :
          ((match PDGraph.validate gOut with
              | .error e => .error e
              | .ok () => .ok gOut) : Except String PDGraph) = .ok g0 := by
        simpa [Reidemeister.r2RemoveLast, hvg, hnlt, m, base1, base2, hcond1, hcond1false, hcond2, hcond2false, x, u, y, v,
          hcondExt, hcondExtfalse, hcondBack1, hcondBack1false, hcondBack2, hcondBack2false, gOut] using h

      cases hvgOut : PDGraph.validate gOut with
      | error e =>
          have hcontra := h'
          simp [hvgOut] at hcontra
      | ok hvOut =>
          cases hvOut
          have hgEq : g0 = gOut := by
            have hOk := h'
            simp [hvgOut] at hOk
            exact hOk.symm
          simp [hgEq, gOut]

private theorem r1RemoveLast_pos_err_of_r2RemoveLast_ok {g g0 : PDGraph} (h : Reidemeister.r2RemoveLast g = .ok g0) :
    Reidemeister.r1RemoveLast g .pos = .error "r1RemoveLast: internal loop arc mismatch" := by
  classical
  cases hvg : PDGraph.validate g with
  | error e =>
      simp [Reidemeister.r2RemoveLast, hvg] at h
  | ok hv =>
      cases hv
      have hnge : 2 ≤ g.n := n_ge_two_of_r2RemoveLast_ok (g := g) (g0 := g0) h
      have hn0 : g.n ≠ 0 := by
        exact ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hnge)
      let m := g.numHalfEdges
      let base1 := m - 8
      let base2 := m - 4
      have harc : g.arcNbr[base2 + 0]! = base1 + 1 :=
        arc_base2_0_eq_base1_1_of_r2RemoveLast_ok (g := g) (g0 := g0) h
      have hm8 : 8 ≤ m := by
        -- `m = 4 * g.n` and `g.n ≥ 2`.
        have : 8 ≤ 4 * g.n := Nat.mul_le_mul_left 4 hnge
        simpa [PDGraph.numHalfEdges, m] using this
      have hbase2 : base2 = base1 + 4 := by
        -- `m = (m-8) + 8`, so `(m-4) = (m-8) + 4`.
        have hm' : base1 + 8 = m := by
          -- `base1 = m - 8`.
          simpa [base1] using (Nat.sub_add_cancel hm8)
        calc
          base2 = m - 4 := rfl
          _ = (base1 + 8) - 4 := by simpa [hm']
          _ = base1 + (8 - 4) := by
                simpa using (Nat.add_sub_assoc (a := base1) (b := 4) (c := 8) (by decide : 4 ≤ 8))
          _ = base1 + 4 := by simp
      have hneBase : base1 + 1 ≠ base2 + 1 := by
        intro hEq
        -- Rewrite `base2` as `base1 + 4`, then cancel `base1` on the left.
        have : base1 + 1 = base1 + 5 := by
          simpa [hbase2, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hEq
        have : (1 : Nat) = 5 := Nat.add_left_cancel this
        exact (by decide : (1 : Nat) ≠ 5) this
      have hne : g.arcNbr[base2 + 0]! ≠ base2 + 1 := by
        intro hEq
        exact hneBase (harc.symm.trans hEq)
      have hbne : (g.arcNbr[base2 + 0]! != base2 + 1) = true := (bne_iff_ne).2 hne
      have hbne0 : (g.arcNbr[g.numHalfEdges - 4]! != g.numHalfEdges - 4 + 1) = true := by
        -- `base2 = g.numHalfEdges - 4`.
        simpa [m, base2] using hbne
      -- Reduce `r1RemoveLast` using the forced internal-loop mismatch at the last crossing.
      simp [Reidemeister.r1RemoveLast, hvg, hn0, hbne0]

private theorem r1RemoveLast_neg_err_of_r2RemoveLast_ok {g g0 : PDGraph} (h : Reidemeister.r2RemoveLast g = .ok g0) :
    Reidemeister.r1RemoveLast g .neg = .error "r1RemoveLast: internal loop arc mismatch" := by
  classical
  cases hvg : PDGraph.validate g with
  | error e =>
      simp [Reidemeister.r2RemoveLast, hvg] at h
  | ok hv =>
      cases hv
      have hnge : 2 ≤ g.n := n_ge_two_of_r2RemoveLast_ok (g := g) (g0 := g0) h
      have hn0 : g.n ≠ 0 := by
        exact ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hnge)
      let m := g.numHalfEdges
      let base1 := m - 8
      let base2 := m - 4
      have hylt : g.arcNbr[base2 + 1]! < base1 :=
        arc_base2_1_lt_base1_of_r2RemoveLast_ok (g := g) (g0 := g0) h
      have hm8 : 8 ≤ m := by
        have : 8 ≤ 4 * g.n := Nat.mul_le_mul_left 4 hnge
        simpa [PDGraph.numHalfEdges, m] using this
      have hbase2 : base2 = base1 + 4 := by
        have hm' : base1 + 8 = m := by
          simpa [base1] using (Nat.sub_add_cancel hm8)
        calc
          base2 = m - 4 := rfl
          _ = (base1 + 8) - 4 := by simpa [hm']
          _ = base1 + (8 - 4) := by
                simpa using (Nat.add_sub_assoc (a := base1) (b := 4) (c := 8) (by decide : 4 ≤ 8))
          _ = base1 + 4 := by simp
      have hbase : base1 ≤ base2 + 2 := by
        -- `base2 + 2 = base1 + 6` since `base2 = base1 + 4`.
        have hEq : base2 + 2 = base1 + 6 := by
          calc
            base2 + 2 = (base1 + 4) + 2 := by simpa [hbase2]
            _ = base1 + 6 := by
              simp [Nat.add_assoc]
        -- `base1 ≤ base1 + 6`, then rewrite.
        simpa [hEq] using (Nat.le_add_right base1 6)
      have hne : g.arcNbr[base2 + 1]! ≠ base2 + 2 := by
        intro hEq
        have : base2 + 2 < base1 := by simpa [hEq] using hylt
        exact (Nat.not_lt_of_ge hbase) this
      have hbne : (g.arcNbr[base2 + 1]! != base2 + 2) = true := (bne_iff_ne).2 hne
      have hbne1 : (g.arcNbr[g.numHalfEdges - 4 + 1]! != g.numHalfEdges - 4 + 2) = true := by
        simpa [m, base2, Nat.add_assoc] using hbne
      simp [Reidemeister.r1RemoveLast, hvg, hn0, hbne1]

theorem bracketGraphML_r2Add
    {g g' : PDGraph} {x u : Nat}
    (h : Reidemeister.r2Add g x u = .ok g') :
    bracketGraphML g' = bracketGraphML g := by
  have hrem : Reidemeister.r2RemoveLast g' = .ok g :=
    Reidemeister.r2RemoveLast_of_r2Add_ok (g := g) (g' := g') (x := x) (u := u) h
  cases hvg' : PDGraph.validate g' with
  | error e =>
      simp [Reidemeister.r2RemoveLast, hvg'] at hrem
  | ok hv =>
      cases hv
      have hnge : 2 ≤ g'.n := n_ge_two_of_r2RemoveLast_ok (g := g') (g0 := g) hrem
      have hnSub : g.n = g'.n - 2 := by
        simpa using (r2RemoveLast_n_eq (g := g') (g0 := g) hrem)
      have hnAdd : g'.n = g.n + 2 := by
        -- From `g.n = g'.n - 2` and `2 ≤ g'.n`.
        have h1 : g'.n = (g'.n - 2) + 2 := by
          simpa using (Nat.sub_add_cancel hnge).symm
        -- rewrite `(g'.n - 2)` as `g.n`
        simpa [hnSub.symm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h1
      have hposErr := r1RemoveLast_pos_err_of_r2RemoveLast_ok (g := g') (g0 := g) hrem
      have hnegErr := r1RemoveLast_neg_err_of_r2RemoveLast_ok (g := g') (g0 := g) hrem
      simp [bracketGraphML]
      rw [hnAdd]
      conv_lhs =>
        simp [bracketGraphMLAux, hvg', hnAdd, hposErr, hnegErr, hrem]
      rfl

end

end Kauffman

end Knot
end Topology
end HeytingLean
