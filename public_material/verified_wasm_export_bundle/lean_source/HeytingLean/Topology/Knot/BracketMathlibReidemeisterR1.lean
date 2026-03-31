import HeytingLean.Topology.Knot.BracketMathlib
import HeytingLean.Topology.Knot.Reidemeister

/-!
# Knot theory: Reidemeister-I scaling (Mathlib proof layer)

This module proves the classic Reidemeister-I scaling behavior of the Kauffman bracket in the
Mathlib Laurent polynomial layer:

- adding a positive curl scales by `-(A^3)`,
- adding a negative curl scales by `-(A⁻³)`.

These are the algebraic inputs required for Jones normalization to yield an ambient-isotopy
invariant.
-/

namespace HeytingLean
namespace Topology
namespace Knot

namespace Kauffman

open scoped LaurentPolynomial
open Reidemeister

noncomputable section

theorem r1Add_n_eq
    {g g' : PDGraph} {x : Nat} {kind : CurlKind}
    (h : Reidemeister.r1Add g x kind = .ok g') : g'.n = g.n + 1 := by
  classical
  -- Unfold `r1Add` enough to see the output `n := g.n + 1` in the success branch.
  cases hvg : PDGraph.validate g with
  | error e =>
      simp [Reidemeister.r1Add, hvg] at h
  | ok u =>
      cases u
      let m := g.numHalfEdges
      by_cases hx : x < m
      · have hx_ge : ¬ x >= m := Nat.not_le_of_gt hx
        have hgValid : PDGraph.Valid g := PDGraph.valid_of_validate_eq_ok (g := g) hvg
        let y : Nat := g.arcNbr[x]!
        have hy : y < m := PDGraph.Valid.get_lt hgValid (i := x) (hi := hx)
        have hy_ge : ¬ y >= m := Nat.not_le_of_gt hy
        have hy_invol : g.arcNbr[y]! = x := PDGraph.Valid.invol hgValid (i := x) (hi := hx)
        -- Name the constructed output graph (its `n` field is definitionally `g.n + 1`).
        let base : Nat := m
        let nbr0 : Array Nat := g.arcNbr ++ Array.replicate 4 0
        let nbr :=
          match kind with
          | .pos =>
              let nbr := Reidemeister.setPair! nbr0 (base + 0) (base + 1)
              let nbr := Reidemeister.setPair! nbr x (base + 2)
              Reidemeister.setPair! nbr y (base + 3)
          | .neg =>
              let nbr := Reidemeister.setPair! nbr0 (base + 1) (base + 2)
              let nbr := Reidemeister.setPair! nbr x (base + 0)
              Reidemeister.setPair! nbr y (base + 3)
        let gOut : PDGraph := { freeLoops := g.freeLoops, n := g.n + 1, arcNbr := nbr }
        have h' :
            ((match PDGraph.validate gOut with
                | .error e => .error e
                | .ok () => .ok gOut) : Except String PDGraph) = .ok g' := by
          -- Reduce `r1Add` using the success-branch facts and the named construction.
          have hm : g.numHalfEdges = m := by rfl
          have hxy : g.arcNbr[x]! = y := by rfl
          have hx_ge' : ¬ m ≤ x := by simpa [m] using hx_ge
          have hy_ge' : ¬ m ≤ y := by simpa [m] using hy_ge
          have hnbr0 : g.arcNbr ++ Array.replicate 4 0 = nbr0 := by rfl
          have hgOut : ({ freeLoops := g.freeLoops, n := g.n + 1, arcNbr := nbr } : PDGraph) = gOut := by rfl
          have h0 := h
          -- `simp` reduces the guards and exposes the final `validate gOut` check.
          simpa [Reidemeister.r1Add, hvg, hm, hxy, hx_ge', hy_ge', hy_invol, base, hnbr0, hgOut] using h0
        -- From success, `validate gOut = ok` and thus the returned graph is `gOut`.
        cases hvgOut : PDGraph.validate gOut with
        | error e =>
            have hcontra := h'
            simp [hvgOut] at hcontra
        | ok u =>
            cases u
            have hgEq : g' = gOut := by
              have hOk := h'
              simp [hvgOut] at hOk
              exact hOk.symm
            -- `gOut.n` is definitionally `g.n + 1`.
            simp [hgEq, gOut]
      · -- Contradiction: `r1Add` errors when `x` is out of range.
        have hx_ge : x >= m := Nat.le_of_not_gt hx
        have hx_ge' : x >= g.numHalfEdges := by simpa [m] using hx_ge
        have hcontra := h
        simp [Reidemeister.r1Add, hvg, hx_ge'] at hcontra

theorem bracketGraphML_r1Add_pos
    {g g' : PDGraph} {x : Nat}
    (h : Reidemeister.r1Add g x .pos = .ok g') :
    bracketGraphML g' =
      (do
        let b ← bracketGraphML g
        return (-(AML ^ 3 : PolyML)) * b) := by
  have hrem : Reidemeister.r1RemoveLast g' .pos = .ok g :=
    Reidemeister.r1RemoveLast_of_r1Add_ok (g := g) (g' := g') (x := x) (kind := .pos) h
  cases hvg' : PDGraph.validate g' with
  | error e =>
      -- Contradiction: `r1RemoveLast` cannot succeed if `validate g'` fails.
      simp [Reidemeister.r1RemoveLast, hvg'] at hrem
  | ok u =>
      cases u
      have hnAdd : g'.n = g.n + 1 := r1Add_n_eq (g := g) (g' := g') (x := x) (kind := .pos) h
      -- Expand only the `bracketGraphML` wrapper; keep `bracketGraphMLAux` opaque on the RHS.
      simp [bracketGraphML]
      -- Rewrite the fuel for `g'` using `hnAdd`, then unfold one step of the fuel recursion on the LHS.
      rw [hnAdd]
      conv_lhs =>
        simp [bracketGraphMLAux, hvg', hnAdd, hrem]
      rfl

theorem bracketGraphML_r1Add_neg
    {g g' : PDGraph} {x : Nat}
    (h : Reidemeister.r1Add g x .neg = .ok g') :
    bracketGraphML g' =
      (do
        let b ← bracketGraphML g
        return (-(AinvML ^ 3 : PolyML)) * b) := by
  have hrem : Reidemeister.r1RemoveLast g' .neg = .ok g :=
    Reidemeister.r1RemoveLast_of_r1Add_ok (g := g) (g' := g') (x := x) (kind := .neg) h
  cases hvg' : PDGraph.validate g' with
  | error e =>
      simp [Reidemeister.r1RemoveLast, hvg'] at hrem
  | ok u =>
      cases u
      have hnAdd : g'.n = g.n + 1 := r1Add_n_eq (g := g) (g' := g') (x := x) (kind := .neg) h
      simp [bracketGraphML]
      rw [hnAdd]
      -- The negative curl shape forces the positive `r1RemoveLast` check to fail immediately.
      have hposErr : Reidemeister.r1RemoveLast g' .pos = .error "r1RemoveLast: internal loop arc mismatch" := by
        have hn0 : g'.n ≠ 0 := by
          simp [hnAdd]
        -- Use the fact that the negative removal succeeds to show the `ext1` endpoint is external:
        -- for kind `.neg`, `ext1 = (m-4)+0`, and in the success branch `x := arcNbr[ext1]!` must satisfy `x < m-4`.
        have hExtLt : g'.arcNbr[g'.numHalfEdges - 4]! < g'.numHalfEdges - 4 := by
          -- If `x ≥ base`, `r1RemoveLast` cannot return `.ok _` (regardless of whether the internal-loop check fails).
          have hNotGe : ¬ g'.arcNbr[g'.numHalfEdges - 4]! >= g'.numHalfEdges - 4 := by
            intro hxGe
            by_cases hMismatch :
                (g'.arcNbr[g'.numHalfEdges - 4 + 1]! != g'.numHalfEdges - 4 + 2) ||
                  (g'.arcNbr[g'.numHalfEdges - 4 + 2]! != g'.numHalfEdges - 4 + 1)
            ·
              have hcontra := hrem
              simp [Reidemeister.r1RemoveLast, hvg', hn0, hMismatch] at hcontra
            ·
              have hcontra := hrem
              -- With `hxGe`, the external-endpoint check triggers.
              simp [Reidemeister.r1RemoveLast, hvg', hn0, hMismatch, hxGe] at hcontra
          exact Nat.lt_of_not_ge hNotGe
        have hne : g'.arcNbr[g'.numHalfEdges - 4]! ≠ g'.numHalfEdges - 4 + 1 := by
          intro hEq
          have hlt : g'.numHalfEdges - 4 + 1 < g'.numHalfEdges - 4 := by
            rw [← hEq]
            exact hExtLt
          have hge : g'.numHalfEdges - 4 ≤ g'.numHalfEdges - 4 + 1 := Nat.le_succ _
          exact (Nat.not_lt_of_ge hge) hlt
        have hbne : (g'.arcNbr[g'.numHalfEdges - 4]! != g'.numHalfEdges - 4 + 1) = true :=
          (bne_iff_ne).2 hne
        -- For kind `.pos`, the internal loop requires `arcNbr[base+0] = base+1`; this fails, so we get the mismatch error.
        simp [Reidemeister.r1RemoveLast, hvg', hn0, hbne]
      conv_lhs =>
        simp [bracketGraphMLAux, hvg', hnAdd, hposErr, hrem]
      rfl

end

end Kauffman

end Knot
end Topology
end HeytingLean
