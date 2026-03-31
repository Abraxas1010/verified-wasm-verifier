import HeytingLean.Topology.Knot.BracketMathlib
import HeytingLean.Topology.Knot.Reidemeister
import Mathlib.Data.Bool.Basic

/-!
# Knot theory: Reidemeister-II invariance (Mathlib proof layer)

This module proves that the Mathlib-layer Kauffman bracket `bracketGraphML` is invariant under a
Reidemeister-II cancelling pair, using the evaluator’s R2 short-circuit (`r2RemoveLast`).

Implementation note: we keep proofs lightweight (no giant heartbeat overrides) and we avoid
unfolding the executable validator; reasoning proceeds via `validate = .ok ()` handles.
-/

namespace HeytingLean
namespace Topology
namespace Knot

namespace Kauffman

open scoped LaurentPolynomial
open Reidemeister

noncomputable section

attribute [local irreducible] PDGraph.validate

private theorem n_ge_two_of_r2RemoveLast_ok
    {g g0 : PDGraph} (h : Reidemeister.r2RemoveLast g = .ok g0) : 2 ≤ g.n := by
  cases hvg : PDGraph.validate g with
  | error e =>
      simp [Reidemeister.r2RemoveLast, hvg] at h
  | ok hv =>
      cases hv
      by_contra hnge
      have hnlt : g.n < 2 := Nat.lt_of_not_ge hnge
      have hcontra := h
      simp [Reidemeister.r2RemoveLast, hvg, hnlt] at hcontra

set_option maxHeartbeats 2000000 in
private theorem r2RemoveLast_n_eq
    {g g0 : PDGraph} (h : Reidemeister.r2RemoveLast g = .ok g0) : g0.n = g.n - 2 := by
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
      let x := g.arcNbr[base1 + 0]!
      let u := g.arcNbr[base1 + 3]!
      let y := g.arcNbr[base2 + 1]!
      let v := g.arcNbr[base2 + 2]!
      let nbr := setPair! (setPair! (g.arcNbr.take base1) x y) u v
      let gOut : PDGraph := { freeLoops := g.freeLoops, n := g.n - 2, arcNbr := nbr }

      -- Any intermediate failure would produce `Except.error _`, contradicting `h = .ok _`.
      have hcond1Pfalse :
          ¬(¬g.arcNbr[base1 + 1]! = base2 + 0 ∨ ¬g.arcNbr[base2 + 0]! = base1 + 1) := by
        intro hcond1P
        have hcond1P' :
            (¬g.arcNbr[g.numHalfEdges - 8 + 1]! = g.numHalfEdges - 4 ∨
              ¬g.arcNbr[g.numHalfEdges - 4]! = g.numHalfEdges - 8 + 1) := by
          simpa [m, base1, base2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcond1P
        have herr :
            Reidemeister.r2RemoveLast g =
              .error "r2RemoveLast: internal arc (1↔0) mismatch" := by
          simp [Reidemeister.r2RemoveLast, hvg, hnlt, hcond1P']
        have hEq := h
        simp [herr] at hEq
      have hcond2Pfalse :
          ¬(¬g.arcNbr[base1 + 2]! = base2 + 3 ∨ ¬g.arcNbr[base2 + 3]! = base1 + 2) := by
        intro hcond2P
        have hcond1Eq : g.arcNbr[base1 + 1]! = base2 + 0 ∧ g.arcNbr[base2 + 0]! = base1 + 1 := by
          have hnn :
              (¬¬g.arcNbr[base1 + 1]! = base2 + 0) ∧ (¬¬g.arcNbr[base2 + 0]! = base1 + 1) :=
            (not_or).1 hcond1Pfalse
          exact ⟨not_not.mp hnn.1, not_not.mp hnn.2⟩
        have hcond1Eq' :
            g.arcNbr[g.numHalfEdges - 8 + 1]! = g.numHalfEdges - 4 ∧
              g.arcNbr[g.numHalfEdges - 4]! = g.numHalfEdges - 8 + 1 := by
          simpa [m, base1, base2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcond1Eq
        have hcond2P' :
            (¬g.arcNbr[g.numHalfEdges - 8 + 2]! = g.numHalfEdges - 4 + 3 ∨
              ¬g.arcNbr[g.numHalfEdges - 4 + 3]! = g.numHalfEdges - 8 + 2) := by
          simpa [m, base1, base2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcond2P
        have herr :
            Reidemeister.r2RemoveLast g =
              .error "r2RemoveLast: internal arc (2↔3) mismatch" := by
          simp [Reidemeister.r2RemoveLast, hvg, hnlt, hcond1Eq'.1, hcond1Eq'.2, hcond2P']
        have hEq := h
        simp [herr] at hEq
      have hcondExtPfalse : ¬(((m ≤ x + 8 ∨ m ≤ u + 8) ∨ m ≤ y + 8) ∨ m ≤ v + 8) := by
        intro hcondExtP
        have hcond1Eq : g.arcNbr[base1 + 1]! = base2 + 0 ∧ g.arcNbr[base2 + 0]! = base1 + 1 := by
          have hnn :
              (¬¬g.arcNbr[base1 + 1]! = base2 + 0) ∧ (¬¬g.arcNbr[base2 + 0]! = base1 + 1) :=
            (not_or).1 hcond1Pfalse
          exact ⟨not_not.mp hnn.1, not_not.mp hnn.2⟩
        have hcond1Eq' :
            g.arcNbr[g.numHalfEdges - 8 + 1]! = g.numHalfEdges - 4 ∧
              g.arcNbr[g.numHalfEdges - 4]! = g.numHalfEdges - 8 + 1 := by
          simpa [m, base1, base2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcond1Eq
        have hcond2Eq : g.arcNbr[base1 + 2]! = base2 + 3 ∧ g.arcNbr[base2 + 3]! = base1 + 2 := by
          have hnn :
              (¬¬g.arcNbr[base1 + 2]! = base2 + 3) ∧ (¬¬g.arcNbr[base2 + 3]! = base1 + 2) :=
            (not_or).1 hcond2Pfalse
          exact ⟨not_not.mp hnn.1, not_not.mp hnn.2⟩
        have hcond2Eq' :
            g.arcNbr[g.numHalfEdges - 8 + 2]! = g.numHalfEdges - 4 + 3 ∧
              g.arcNbr[g.numHalfEdges - 4 + 3]! = g.numHalfEdges - 8 + 2 := by
          simpa [m, base1, base2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcond2Eq
        have hcondExtP' :
            ((g.numHalfEdges ≤ g.arcNbr[g.numHalfEdges - 8]! + 8 ∨
                  g.numHalfEdges ≤ g.arcNbr[g.numHalfEdges - 8 + 3]! + 8) ∨
                g.numHalfEdges ≤ g.arcNbr[g.numHalfEdges - 4 + 1]! + 8) ∨
              g.numHalfEdges ≤ g.arcNbr[g.numHalfEdges - 4 + 2]! + 8 := by
          simpa [m, base1, base2, x, u, y, v, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcondExtP
        have herr :
            Reidemeister.r2RemoveLast g =
              .error "r2RemoveLast: expected external endpoints for the pair" := by
          simp [Reidemeister.r2RemoveLast, hvg, hnlt, hcond1Eq'.1, hcond1Eq'.2, hcond2Eq'.1, hcond2Eq'.2, hcondExtP']
        have hEq := h
        simp [herr] at hEq
      have hcondBack1Pfalse : ¬(¬g.arcNbr[x]! = base1 + 0 ∨ ¬g.arcNbr[u]! = base1 + 3) := by
        intro hcondBack1P
        have hcond1Eq :
            g.arcNbr[g.numHalfEdges - 8 + 1]! = g.numHalfEdges - 4 ∧
              g.arcNbr[g.numHalfEdges - 4]! = g.numHalfEdges - 8 + 1 := by
          have hnn :
              (¬¬g.arcNbr[base1 + 1]! = base2 + 0) ∧ (¬¬g.arcNbr[base2 + 0]! = base1 + 1) :=
            (not_or).1 hcond1Pfalse
          have hEqBase : g.arcNbr[base1 + 1]! = base2 + 0 ∧ g.arcNbr[base2 + 0]! = base1 + 1 :=
            ⟨not_not.mp hnn.1, not_not.mp hnn.2⟩
          simpa [m, base1, base2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hEqBase
        have hcond2Eq :
            g.arcNbr[g.numHalfEdges - 8 + 2]! = g.numHalfEdges - 4 + 3 ∧
              g.arcNbr[g.numHalfEdges - 4 + 3]! = g.numHalfEdges - 8 + 2 := by
          have hnn :
              (¬¬g.arcNbr[base1 + 2]! = base2 + 3) ∧ (¬¬g.arcNbr[base2 + 3]! = base1 + 2) :=
            (not_or).1 hcond2Pfalse
          have hEqBase : g.arcNbr[base1 + 2]! = base2 + 3 ∧ g.arcNbr[base2 + 3]! = base1 + 2 :=
            ⟨not_not.mp hnn.1, not_not.mp hnn.2⟩
          simpa [m, base1, base2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hEqBase
        have hcondExtPfalse' :
            ¬(((g.numHalfEdges ≤ g.arcNbr[g.numHalfEdges - 8]! + 8 ∨
                    g.numHalfEdges ≤ g.arcNbr[g.numHalfEdges - 8 + 3]! + 8) ∨
                  g.numHalfEdges ≤ g.arcNbr[g.numHalfEdges - 4 + 1]! + 8) ∨
                g.numHalfEdges ≤ g.arcNbr[g.numHalfEdges - 4 + 2]! + 8) := by
          simpa [m, base1, base2, x, u, y, v, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcondExtPfalse
        have hcondBack1P' :
            (¬g.arcNbr[g.arcNbr[g.numHalfEdges - 8]!]! = g.numHalfEdges - 8 ∨
              ¬g.arcNbr[g.arcNbr[g.numHalfEdges - 8 + 3]!]! = g.numHalfEdges - 8 + 3) := by
          simpa [m, base1, base2, x, u, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcondBack1P
        have herr :
            Reidemeister.r2RemoveLast g =
              .error "r2RemoveLast: external endpoints do not point back (left crossing)" := by
          simp [Reidemeister.r2RemoveLast, hvg, hnlt, hcond1Eq.1, hcond1Eq.2, hcond2Eq.1, hcond2Eq.2, hcondExtPfalse',
            hcondBack1P']
        have hEq := h
        simp [herr] at hEq
      have hcondBack2Pfalse : ¬(¬g.arcNbr[y]! = base2 + 1 ∨ ¬g.arcNbr[v]! = base2 + 2) := by
        intro hcondBack2P
        have hcond1Eq :
            g.arcNbr[g.numHalfEdges - 8 + 1]! = g.numHalfEdges - 4 ∧
              g.arcNbr[g.numHalfEdges - 4]! = g.numHalfEdges - 8 + 1 := by
          have hnn :
              (¬¬g.arcNbr[base1 + 1]! = base2 + 0) ∧ (¬¬g.arcNbr[base2 + 0]! = base1 + 1) :=
            (not_or).1 hcond1Pfalse
          have hEqBase : g.arcNbr[base1 + 1]! = base2 + 0 ∧ g.arcNbr[base2 + 0]! = base1 + 1 :=
            ⟨not_not.mp hnn.1, not_not.mp hnn.2⟩
          simpa [m, base1, base2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hEqBase
        have hcond2Eq :
            g.arcNbr[g.numHalfEdges - 8 + 2]! = g.numHalfEdges - 4 + 3 ∧
              g.arcNbr[g.numHalfEdges - 4 + 3]! = g.numHalfEdges - 8 + 2 := by
          have hnn :
              (¬¬g.arcNbr[base1 + 2]! = base2 + 3) ∧ (¬¬g.arcNbr[base2 + 3]! = base1 + 2) :=
            (not_or).1 hcond2Pfalse
          have hEqBase : g.arcNbr[base1 + 2]! = base2 + 3 ∧ g.arcNbr[base2 + 3]! = base1 + 2 :=
            ⟨not_not.mp hnn.1, not_not.mp hnn.2⟩
          simpa [m, base1, base2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hEqBase
        have hcondExtPfalse' :
            ¬(((g.numHalfEdges ≤ g.arcNbr[g.numHalfEdges - 8]! + 8 ∨
                    g.numHalfEdges ≤ g.arcNbr[g.numHalfEdges - 8 + 3]! + 8) ∨
                  g.numHalfEdges ≤ g.arcNbr[g.numHalfEdges - 4 + 1]! + 8) ∨
                g.numHalfEdges ≤ g.arcNbr[g.numHalfEdges - 4 + 2]! + 8) := by
          simpa [m, base1, base2, x, u, y, v, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcondExtPfalse
        have hcondBack2P' :
            (¬g.arcNbr[g.arcNbr[g.numHalfEdges - 4 + 1]!]! = g.numHalfEdges - 4 + 1 ∨
              ¬g.arcNbr[g.arcNbr[g.numHalfEdges - 4 + 2]!]! = g.numHalfEdges - 4 + 2) := by
          simpa [m, base1, base2, y, v, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcondBack2P
        have hcondBack1Pfalse' :
            ¬(¬g.arcNbr[g.arcNbr[g.numHalfEdges - 8]!]! = g.numHalfEdges - 8 ∨
                ¬g.arcNbr[g.arcNbr[g.numHalfEdges - 8 + 3]!]! = g.numHalfEdges - 8 + 3) := by
          simpa [m, base1, base2, x, u, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcondBack1Pfalse
        have herr :
            Reidemeister.r2RemoveLast g =
              .error "r2RemoveLast: external endpoints do not point back (right crossing)" := by
          simp [Reidemeister.r2RemoveLast, hvg, hnlt, hcond1Eq.1, hcond1Eq.2, hcond2Eq.1, hcond2Eq.2, hcondExtPfalse',
            hcondBack1Pfalse', hcondBack2P']
        have hEq := h
        simp [herr] at hEq

      have hcond1Eq :
          g.arcNbr[g.numHalfEdges - 8 + 1]! = g.numHalfEdges - 4 ∧
            g.arcNbr[g.numHalfEdges - 4]! = g.numHalfEdges - 8 + 1 := by
        have hnn :
            (¬¬g.arcNbr[base1 + 1]! = base2 + 0) ∧ (¬¬g.arcNbr[base2 + 0]! = base1 + 1) :=
          (not_or).1 hcond1Pfalse
        have hEqBase : g.arcNbr[base1 + 1]! = base2 + 0 ∧ g.arcNbr[base2 + 0]! = base1 + 1 :=
          ⟨not_not.mp hnn.1, not_not.mp hnn.2⟩
        simpa [m, base1, base2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hEqBase
      have hcond2Eq :
          g.arcNbr[g.numHalfEdges - 8 + 2]! = g.numHalfEdges - 4 + 3 ∧
            g.arcNbr[g.numHalfEdges - 4 + 3]! = g.numHalfEdges - 8 + 2 := by
        have hnn :
            (¬¬g.arcNbr[base1 + 2]! = base2 + 3) ∧ (¬¬g.arcNbr[base2 + 3]! = base1 + 2) :=
          (not_or).1 hcond2Pfalse
        have hEqBase : g.arcNbr[base1 + 2]! = base2 + 3 ∧ g.arcNbr[base2 + 3]! = base1 + 2 :=
          ⟨not_not.mp hnn.1, not_not.mp hnn.2⟩
        simpa [m, base1, base2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hEqBase
      have hcondExtPfalse' :
          ¬(((g.numHalfEdges ≤ g.arcNbr[g.numHalfEdges - 8]! + 8 ∨
                  g.numHalfEdges ≤ g.arcNbr[g.numHalfEdges - 8 + 3]! + 8) ∨
                g.numHalfEdges ≤ g.arcNbr[g.numHalfEdges - 4 + 1]! + 8) ∨
              g.numHalfEdges ≤ g.arcNbr[g.numHalfEdges - 4 + 2]! + 8) := by
        simpa [m, base1, base2, x, u, y, v, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcondExtPfalse
      have hcondBack1Pfalse' :
          ¬(¬g.arcNbr[g.arcNbr[g.numHalfEdges - 8]!]! = g.numHalfEdges - 8 ∨
                ¬g.arcNbr[g.arcNbr[g.numHalfEdges - 8 + 3]!]! = g.numHalfEdges - 8 + 3) := by
        simpa [m, base1, base2, x, u, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcondBack1Pfalse
      have hcondBack2Pfalse' :
          ¬(¬g.arcNbr[g.arcNbr[g.numHalfEdges - 4 + 1]!]! = g.numHalfEdges - 4 + 1 ∨
                ¬g.arcNbr[g.arcNbr[g.numHalfEdges - 4 + 2]!]! = g.numHalfEdges - 4 + 2) := by
        simpa [m, base1, base2, y, v, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcondBack2Pfalse

      have h' :
          ((match PDGraph.validate gOut with
              | .error e => .error e
              | .ok () => .ok gOut) : Except String PDGraph) = .ok g0 := by
        have hcontra := h
        simpa [Reidemeister.r2RemoveLast, hvg, hnlt, hcond1Eq.1, hcond1Eq.2, hcond2Eq.1, hcond2Eq.2, hcondExtPfalse',
          hcondBack1Pfalse', hcondBack2Pfalse', gOut] using hcontra
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

private theorem arc_base2_0_eq_base1_1_of_r2RemoveLast_ok
    {g g0 : PDGraph} (h : Reidemeister.r2RemoveLast g = .ok g0) :
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
      set cond1 :=
        (g.arcNbr[base1 + 1]! != base2 + 0 || g.arcNbr[base2 + 0]! != base1 + 1) with hcond1
      have hcond1false : cond1 = false := by
        cases hc : cond1 with
        | true =>
            have hexpr :
                (g.arcNbr[base1 + 1]! != base2 + 0 || g.arcNbr[base2 + 0]! != base1 + 1) = true := by
              simpa [hcond1] using hc
            have hMismatch :
                (¬g.arcNbr[base1 + 1]! = base2 + 0) ∨ (¬g.arcNbr[base2 + 0]! = base1 + 1) := by
              have hOr :
                  (g.arcNbr[base1 + 1]! != base2 + 0) = true ∨ (g.arcNbr[base2 + 0]! != base1 + 1) = true :=
                Eq.mp
                  (Bool.or_eq_true (g.arcNbr[base1 + 1]! != base2 + 0) (g.arcNbr[base2 + 0]! != base1 + 1))
                  hexpr
              refine hOr.elim (fun h1 => ?_) (fun h2 => ?_)
              · exact Or.inl ((bne_iff_ne).1 h1)
              · exact Or.inr ((bne_iff_ne).1 h2)
            have hMismatch' :
                (¬g.arcNbr[g.numHalfEdges - 8 + 1]! = g.numHalfEdges - 4 ∨
                  ¬g.arcNbr[g.numHalfEdges - 4]! = g.numHalfEdges - 8 + 1) := by
              simpa [m, base1, base2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hMismatch
            have herr :
                Reidemeister.r2RemoveLast g =
                  .error "r2RemoveLast: internal arc (1↔0) mismatch" := by
              simp [Reidemeister.r2RemoveLast, hvg, hnlt, hMismatch']
            have hEq := h
            simp [herr] at hEq
        | false => rfl
      have hparts :
          (g.arcNbr[base1 + 1]! != base2 + 0) = false ∧ (g.arcNbr[base2 + 0]! != base1 + 1) = false := by
        have h' :
            (g.arcNbr[base1 + 1]! != base2 + 0 || g.arcNbr[base2 + 0]! != base1 + 1) = false := by
          simpa [hcond1] using hcond1false
        exact
          Eq.mp
            (Bool.or_eq_false_eq_eq_false_and_eq_false (g.arcNbr[base1 + 1]! != base2 + 0) (g.arcNbr[base2 + 0]! != base1 + 1))
            h'
      have hne : ¬ g.arcNbr[base2 + 0]! ≠ base1 + 1 := by
        intro hne
        have hb : (g.arcNbr[base2 + 0]! != base1 + 1) = true := (bne_iff_ne).2 hne
        exact Bool.false_ne_true (hparts.2.symm.trans hb)
      exact (not_ne_iff).1 hne

set_option maxHeartbeats 2000000 in
private theorem arc_base2_1_lt_base1_of_r2RemoveLast_ok
    {g g0 : PDGraph} (h : Reidemeister.r2RemoveLast g = .ok g0) :
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

      have harc10 : g.arcNbr[base1 + 1]! = base2 + 0 := by
        by_contra hne
        have hMismatch0 :
            (¬g.arcNbr[base1 + 1]! = base2 + 0) ∨ (¬g.arcNbr[base2 + 0]! = base1 + 1) :=
          Or.inl hne
        have hMismatch :
            (¬g.arcNbr[g.numHalfEdges - 8 + 1]! = g.numHalfEdges - 4 ∨
              ¬g.arcNbr[g.numHalfEdges - 4]! = g.numHalfEdges - 8 + 1) := by
          simpa [m, base1, base2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hMismatch0
        have herr :
            Reidemeister.r2RemoveLast g = .error "r2RemoveLast: internal arc (1↔0) mismatch" := by
          simp [Reidemeister.r2RemoveLast, hvg, hnlt, hMismatch]
        have hEq := h
        simp [herr] at hEq
      have harc01 : g.arcNbr[base2 + 0]! = base1 + 1 := by
        by_contra hne
        have hMismatch0 :
            (¬g.arcNbr[base1 + 1]! = base2 + 0) ∨ (¬g.arcNbr[base2 + 0]! = base1 + 1) :=
          Or.inr hne
        have hMismatch :
            (¬g.arcNbr[g.numHalfEdges - 8 + 1]! = g.numHalfEdges - 4 ∨
              ¬g.arcNbr[g.numHalfEdges - 4]! = g.numHalfEdges - 8 + 1) := by
          simpa [m, base1, base2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hMismatch0
        have herr :
            Reidemeister.r2RemoveLast g = .error "r2RemoveLast: internal arc (1↔0) mismatch" := by
          simp [Reidemeister.r2RemoveLast, hvg, hnlt, hMismatch]
        have hEq := h
        simp [herr] at hEq

      have harc23 : g.arcNbr[base1 + 2]! = base2 + 3 := by
        by_contra hne
        have hMismatch0 :
            (¬g.arcNbr[base1 + 2]! = base2 + 3) ∨ (¬g.arcNbr[base2 + 3]! = base1 + 2) :=
          Or.inl hne
        have hMismatch :
            (¬g.arcNbr[g.numHalfEdges - 8 + 2]! = g.numHalfEdges - 4 + 3 ∨
              ¬g.arcNbr[g.numHalfEdges - 4 + 3]! = g.numHalfEdges - 8 + 2) := by
          simpa [m, base1, base2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hMismatch0
        have hcond1Eq :
            g.arcNbr[g.numHalfEdges - 8 + 1]! = g.numHalfEdges - 4 ∧
              g.arcNbr[g.numHalfEdges - 4]! = g.numHalfEdges - 8 + 1 := by
          constructor
          · simpa [m, base1, base2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using harc10
          · simpa [m, base1, base2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using harc01
        have herr :
            Reidemeister.r2RemoveLast g = .error "r2RemoveLast: internal arc (2↔3) mismatch" := by
          simp [Reidemeister.r2RemoveLast, hvg, hnlt, hcond1Eq, hMismatch]
        have hEq := h
        simp [herr] at hEq
      have harc32 : g.arcNbr[base2 + 3]! = base1 + 2 := by
        by_contra hne
        have hMismatch0 :
            (¬g.arcNbr[base1 + 2]! = base2 + 3) ∨ (¬g.arcNbr[base2 + 3]! = base1 + 2) :=
          Or.inr hne
        have hMismatch :
            (¬g.arcNbr[g.numHalfEdges - 8 + 2]! = g.numHalfEdges - 4 + 3 ∨
              ¬g.arcNbr[g.numHalfEdges - 4 + 3]! = g.numHalfEdges - 8 + 2) := by
          simpa [m, base1, base2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hMismatch0
        have hcond1Eq :
            g.arcNbr[g.numHalfEdges - 8 + 1]! = g.numHalfEdges - 4 ∧
              g.arcNbr[g.numHalfEdges - 4]! = g.numHalfEdges - 8 + 1 := by
          constructor
          · simpa [m, base1, base2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using harc10
          · simpa [m, base1, base2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using harc01
        have herr :
            Reidemeister.r2RemoveLast g = .error "r2RemoveLast: internal arc (2↔3) mismatch" := by
          simp [Reidemeister.r2RemoveLast, hvg, hnlt, hcond1Eq, hMismatch]
        have hEq := h
        simp [herr] at hEq

      have harc10' : g.arcNbr[g.numHalfEdges - 8 + 1]! = g.numHalfEdges - 4 := by
        simpa [m, base1, base2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using harc10
      have harc01' : g.arcNbr[g.numHalfEdges - 4]! = g.numHalfEdges - 8 + 1 := by
        simpa [m, base1, base2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using harc01

      let x := g.arcNbr[base1 + 0]!
      let u := g.arcNbr[base1 + 3]!
      let y := g.arcNbr[base2 + 1]!
      let v := g.arcNbr[base2 + 2]!
      have hy_not_ge : ¬ y ≥ base1 := by
        intro hyge
        have hcontra := h
        simp [Reidemeister.r2RemoveLast, hvg, hnlt, m, base1, base2, harc10', harc01', harc23, harc32, y, hyge] at hcontra
      simpa [y] using Nat.lt_of_not_ge hy_not_ge

private theorem r1RemoveLast_pos_err_of_r2RemoveLast_ok
    {g g0 : PDGraph} (h : Reidemeister.r2RemoveLast g = .ok g0) :
    Reidemeister.r1RemoveLast g .pos = .error "r1RemoveLast: internal loop arc mismatch" := by
  classical
  cases hvg : PDGraph.validate g with
  | error e =>
      simp [Reidemeister.r2RemoveLast, hvg] at h
  | ok hv =>
      cases hv
      have hnge : 2 ≤ g.n := n_ge_two_of_r2RemoveLast_ok (g := g) (g0 := g0) h
      have hn0 : g.n ≠ 0 := by exact ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hnge)
      let m := g.numHalfEdges
      let base1 := m - 8
      let base2 := m - 4
      have harc : g.arcNbr[base2 + 0]! = base1 + 1 :=
        arc_base2_0_eq_base1_1_of_r2RemoveLast_ok (g := g) (g0 := g0) h
      have hm8 : 8 ≤ m := by
        have : 8 ≤ 4 * g.n := Nat.mul_le_mul_left 4 hnge
        simpa [PDGraph.numHalfEdges, m] using this
      have hbase2 : base2 = base1 + 4 := by
        have hm' : base1 + 8 = m := by
          simpa [base1] using (Nat.sub_add_cancel hm8)
        have h48 : 4 ≤ 8 := Nat.le_add_right 4 4
        calc
          base2 = m - 4 := rfl
          _ = (base1 + 8) - 4 := by simp [hm']
          _ = base1 + (8 - 4) := by
                exact Nat.add_sub_assoc (m := 8) (k := 4) (n := base1) h48
          _ = base1 + 4 := by simp
      have hneBase : base1 + 1 ≠ base2 + 1 := by
        intro hEq
        have hEq' : base1 + 1 = base1 + 5 := by
          calc
            base1 + 1 = base2 + 1 := hEq
            _ = base1 + 5 := by
              simp [hbase2, Nat.add_assoc]
        have : (1 : Nat) = 5 := Nat.add_left_cancel hEq'
        exact (by decide : (1 : Nat) ≠ 5) this
      have hne : g.arcNbr[base2 + 0]! ≠ base2 + 1 := by
        intro hEq
        have hEq' := hEq
        rw [harc] at hEq'
        exact hneBase hEq'
      have hbne1 : (g.arcNbr[g.numHalfEdges - 4]! != g.numHalfEdges - 4 + 1) = true := by
        have hbne : (g.arcNbr[base2 + 0]! != base2 + 1) = true := (bne_iff_ne).2 hne
        simpa [m, base2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hbne
      have hMismatch :
          (g.arcNbr[g.numHalfEdges - 4]! != g.numHalfEdges - 4 + 1 ||
            g.arcNbr[g.numHalfEdges - 4 + 1]! != g.numHalfEdges - 4) = true := by
        simp [hbne1]
      simp [Reidemeister.r1RemoveLast, hvg, hn0, hMismatch]

private theorem r1RemoveLast_neg_err_of_r2RemoveLast_ok
    {g g0 : PDGraph} (h : Reidemeister.r2RemoveLast g = .ok g0) :
    Reidemeister.r1RemoveLast g .neg = .error "r1RemoveLast: internal loop arc mismatch" := by
  classical
  cases hvg : PDGraph.validate g with
  | error e =>
      simp [Reidemeister.r2RemoveLast, hvg] at h
  | ok hv =>
      cases hv
      have hnge : 2 ≤ g.n := n_ge_two_of_r2RemoveLast_ok (g := g) (g0 := g0) h
      have hn0 : g.n ≠ 0 := by exact ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hnge)
      let m := g.numHalfEdges
      let base1 := m - 8
      let base2 := m - 4
      have hylt : g.arcNbr[base2 + 1]! < base1 :=
        arc_base2_1_lt_base1_of_r2RemoveLast_ok (g := g) (g0 := g0) h
      have hbase : base1 ≤ base2 + 2 := by
        have hm8 : 8 ≤ m := by
          have : 8 ≤ 4 * g.n := Nat.mul_le_mul_left 4 hnge
          simpa [PDGraph.numHalfEdges, m] using this
        have hbase2 : base2 = base1 + 4 := by
          have hm' : base1 + 8 = m := by
            simpa [base1] using (Nat.sub_add_cancel hm8)
          have h48 : 4 ≤ 8 := Nat.le_add_right 4 4
          calc
            base2 = m - 4 := rfl
            _ = (base1 + 8) - 4 := by simp [hm']
            _ = base1 + (8 - 4) := by
                  exact Nat.add_sub_assoc (m := 8) (k := 4) (n := base1) h48
            _ = base1 + 4 := by simp
        have hEq : base2 + 2 = base1 + 6 := by
          calc
            base2 + 2 = (base1 + 4) + 2 := by simp [hbase2]
            _ = base1 + 6 := by simp [Nat.add_assoc]
        have hle : base1 ≤ base1 + 6 := Nat.le_add_right base1 6
        exact le_trans hle (le_of_eq hEq.symm)
      have hne : g.arcNbr[base2 + 1]! ≠ base2 + 2 := by
        intro hEq
        have : base2 + 2 < base1 := by simpa [hEq] using hylt
        exact (Nat.not_lt_of_ge hbase) this
      have hbne1 : (g.arcNbr[g.numHalfEdges - 4 + 1]! != g.numHalfEdges - 4 + 2) = true := by
        have hbne : (g.arcNbr[base2 + 1]! != base2 + 2) = true := (bne_iff_ne).2 hne
        simpa [m, base2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hbne
      have hMismatch :
          (g.arcNbr[g.numHalfEdges - 4 + 1]! != g.numHalfEdges - 4 + 2 ||
            g.arcNbr[g.numHalfEdges - 4 + 2]! != g.numHalfEdges - 4 + 1) = true := by
        simp [hbne1]
      simp [Reidemeister.r1RemoveLast, hvg, hn0, hMismatch]

theorem bracketGraphML_r2Add
    {g g' : PDGraph} {x u : Nat}
    (h : Reidemeister.r2Add g x u = .ok g') :
    bracketGraphML g' = bracketGraphML g := by
  have hrem : Reidemeister.r2RemoveLast g' = .ok g :=
    Reidemeister.r2RemoveLast_of_r2Add_ok (g := g) (g' := g') (x := x) (u := u) h
  cases hvg' : PDGraph.validate g' with
  | error e =>
      -- Contradiction: `r2RemoveLast` cannot succeed if `validate g'` fails.
      simp [Reidemeister.r2RemoveLast, hvg'] at hrem
  | ok hv =>
      cases hv
      have hnSub : g.n = g'.n - 2 := by
        simpa using (r2RemoveLast_n_eq (g := g') (g0 := g) hrem)
      have hnge : 2 ≤ g'.n := n_ge_two_of_r2RemoveLast_ok (g := g') (g0 := g) hrem
      have hnAdd : g'.n = g.n + 2 := by
        have h1 : g'.n = (g'.n - 2) + 2 := by
          simpa using (Nat.sub_add_cancel hnge).symm
        simpa [hnSub.symm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h1
      have hposErr : Reidemeister.r1RemoveLast g' .pos = .error "r1RemoveLast: internal loop arc mismatch" :=
        r1RemoveLast_pos_err_of_r2RemoveLast_ok (g := g') (g0 := g) hrem
      have hnegErr : Reidemeister.r1RemoveLast g' .neg = .error "r1RemoveLast: internal loop arc mismatch" :=
        r1RemoveLast_neg_err_of_r2RemoveLast_ok (g := g') (g0 := g) hrem
      simp [bracketGraphML]
      rw [hnAdd]
      conv_lhs =>
        simp [bracketGraphMLAux, hvg', hnAdd, hposErr, hnegErr, hrem]
      rfl

/--
Direct R2-remove invariance: if the evaluator detects a valid Reidemeister-II
pair at the end and removes it, the bracket is unchanged.
-/
theorem bracketGraphML_r2RemoveLast_ok
    {g g0 : PDGraph}
    (h : Reidemeister.r2RemoveLast g = .ok g0) :
    bracketGraphML g = bracketGraphML g0 := by
  cases hvg : PDGraph.validate g with
  | error e =>
      simp [Reidemeister.r2RemoveLast, hvg] at h
  | ok hv =>
      cases hv
      have hnSub : g0.n = g.n - 2 := r2RemoveLast_n_eq (g := g) (g0 := g0) h
      have hnge : 2 ≤ g.n := n_ge_two_of_r2RemoveLast_ok (g := g) (g0 := g0) h
      have hnAdd : g.n = g0.n + 2 := by
        have h1 : g.n = (g.n - 2) + 2 := by
          simpa using (Nat.sub_add_cancel hnge).symm
        simpa [hnSub.symm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h1
      have hposErr : Reidemeister.r1RemoveLast g .pos = .error "r1RemoveLast: internal loop arc mismatch" :=
        r1RemoveLast_pos_err_of_r2RemoveLast_ok (g := g) (g0 := g0) h
      have hnegErr : Reidemeister.r1RemoveLast g .neg = .error "r1RemoveLast: internal loop arc mismatch" :=
        r1RemoveLast_neg_err_of_r2RemoveLast_ok (g := g) (g0 := g0) h
      simp [bracketGraphML]
      rw [hnAdd]
      conv_lhs =>
        simp [bracketGraphMLAux, hvg, hnAdd, hposErr, hnegErr, h]
      rfl

end

end Kauffman

end Knot
end Topology
end HeytingLean
