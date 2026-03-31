import HeytingLean.Topology.Knot.BracketMathlibSmoothValid

/-!
# Knot theory: totality of the Mathlib proof-layer evaluator on valid graphs

This module proves that the `Except`-valued evaluator `Kauffman.bracketGraphMLAux` does not fail
with a validation error or fuel exhaustion when called with enough fuel on a `PDGraph.Valid` input.
-/

namespace HeytingLean
namespace Topology
namespace Knot

namespace Kauffman

open scoped LaurentPolynomial
open Reidemeister

noncomputable section

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

attribute [local irreducible] PDGraph.validate

private lemma valid_setFreeLoops {n freeLoops₁ freeLoops₂ : Nat} {arcNbr : Array Nat}
    (hg : PDGraph.Valid { freeLoops := freeLoops₁, n := n, arcNbr := arcNbr }) :
    PDGraph.Valid { freeLoops := freeLoops₂, n := n, arcNbr := arcNbr } := by
  simpa [PDGraph.Valid, PDGraph.numHalfEdges] using hg

private theorem r1RemoveLast_props_of_ok
    {g g0 : PDGraph} {kind : CurlKind}
    (h : Reidemeister.r1RemoveLast g kind = .ok g0) :
    PDGraph.Valid g0 ∧ g0.n = g.n - 1 := by
  classical
  cases hvg : PDGraph.validate g with
  | error e =>
      simp [Reidemeister.r1RemoveLast, hvg] at h
  | ok hv =>
      cases hv
      by_cases hn0 : g.n = 0
      · simp [Reidemeister.r1RemoveLast, hvg, hn0] at h
      ·
        let m := g.numHalfEdges
        let base := m - 4
        cases kind with
        | pos =>
            let x := g.arcNbr[base + 2]!
            let y := g.arcNbr[base + 3]!
            let nbr := setPair! (g.arcNbr.extract 0 base) x y
            let gOut : PDGraph := { freeLoops := g.freeLoops, n := g.n - 1, arcNbr := nbr }

            have h' :
                ((match PDGraph.validate gOut with
                    | .error e => .error e
                    | .ok () => .ok gOut) : Except String PDGraph) = .ok g0 := by
              have h0 := h
              simp [Reidemeister.r1RemoveLast, hvg, hn0, m, base, x, y, nbr, gOut] at h0
              split_ifs at h0; try cases h0
              exact h0

            cases hvgOut : PDGraph.validate gOut with
            | error e =>
                have hcontra := h'
                simp [hvgOut] at hcontra
            | ok hvOut =>
                cases hvOut
                have hOk : (Except.ok gOut : Except String PDGraph) = .ok g0 := by
                  simpa [hvgOut] using h'
                have hgEq : g0 = gOut := by
                  injection hOk with hgEq
                  exact hgEq.symm
                have hValidOut : PDGraph.Valid gOut := PDGraph.valid_of_validate_eq_ok (g := gOut) hvgOut
                refine ⟨?_, ?_⟩
                · simpa [hgEq] using hValidOut
                · simpa [hgEq, gOut]
        | neg =>
            let x := g.arcNbr[base + 0]!
            let y := g.arcNbr[base + 3]!
            let nbr := setPair! (g.arcNbr.extract 0 base) x y
            let gOut : PDGraph := { freeLoops := g.freeLoops, n := g.n - 1, arcNbr := nbr }

            have h' :
                ((match PDGraph.validate gOut with
                    | .error e => .error e
                    | .ok () => .ok gOut) : Except String PDGraph) = .ok g0 := by
              have h0 := h
              simp [Reidemeister.r1RemoveLast, hvg, hn0, m, base, x, y, nbr, gOut] at h0
              split_ifs at h0; try cases h0
              exact h0

            cases hvgOut : PDGraph.validate gOut with
            | error e =>
                have hcontra := h'
                simp [hvgOut] at hcontra
            | ok hvOut =>
                cases hvOut
                have hOk : (Except.ok gOut : Except String PDGraph) = .ok g0 := by
                  simpa [hvgOut] using h'
                have hgEq : g0 = gOut := by
                  injection hOk with hgEq
                  exact hgEq.symm
                have hValidOut : PDGraph.Valid gOut := PDGraph.valid_of_validate_eq_ok (g := gOut) hvgOut
                refine ⟨?_, ?_⟩
                · simpa [hgEq] using hValidOut
                · simpa [hgEq, gOut]

private theorem r2RemoveLast_props_of_ok
    {g g0 : PDGraph}
    (h : Reidemeister.r2RemoveLast g = .ok g0) :
    PDGraph.Valid g0 ∧ g0.n = g.n - 2 ∧ 2 ≤ g.n := by
  classical
  cases hvg : PDGraph.validate g with
  | error e =>
      simp [Reidemeister.r2RemoveLast, hvg] at h
  | ok hv =>
      cases hv
      have hnGe2 : 2 ≤ g.n := by
        by_contra hnGe2
        have hnlt : g.n < 2 := Nat.lt_of_not_ge hnGe2
        have hcontra := h
        simp [Reidemeister.r2RemoveLast, hvg, hnlt] at hcontra

      have hnlt : ¬ g.n < 2 := Nat.not_lt_of_ge hnGe2
      let m := g.numHalfEdges
      let base1 := m - 8
      let base2 := m - 4
      let x := g.arcNbr[base1 + 0]!
      let u := g.arcNbr[base1 + 3]!
      let y := g.arcNbr[base2 + 1]!
      let v := g.arcNbr[base2 + 2]!
      let nbr := setPair! (setPair! (g.arcNbr.extract 0 base1) x y) u v
      let gOut : PDGraph := { freeLoops := g.freeLoops, n := g.n - 2, arcNbr := nbr }

      have h' :
          ((match PDGraph.validate gOut with
              | .error e => .error e
              | .ok () => .ok gOut) : Except String PDGraph) = .ok g0 := by
        have h0 := h
        simp [Reidemeister.r2RemoveLast, hvg, hnlt, m, base1, base2, x, u, y, v, nbr, gOut] at h0
        split_ifs at h0; try cases h0
        exact h0

      cases hvgOut : PDGraph.validate gOut with
      | error e =>
          have hcontra := h'
          simp [hvgOut] at hcontra
      | ok hvOut =>
          cases hvOut
          have hOk : (Except.ok gOut : Except String PDGraph) = .ok g0 := by
            simpa [hvgOut] using h'
          have hgEq : g0 = gOut := by
            injection hOk with hgEq
            exact hgEq.symm
          have hValidOut : PDGraph.Valid gOut := PDGraph.valid_of_validate_eq_ok (g := gOut) hvgOut
          refine ⟨?_, ?_, hnGe2⟩
          · simpa [hgEq] using hValidOut
          · simpa [hgEq, gOut]

/--
If `g` is `PDGraph.Valid` and `fuel` is large enough, then the proof-layer evaluator
`bracketGraphMLAux fuel g` returns `.ok _` (no validation error and no fuel exhaustion).
-/
theorem bracketGraphMLAux_ok_of_valid :
    ∀ fuel g, PDGraph.Valid g → g.n ≤ fuel → ∃ p, bracketGraphMLAux fuel g = .ok p := by
  classical
  intro fuel
  refine Nat.strongRecOn fuel ?_
  intro fuel ih g hg hle
  have hvg : PDGraph.validate g = .ok () := PDGraph.validate_eq_ok_of_valid hg
  cases fuel with
  | zero =>
      have hn0 : g.n = 0 := Nat.eq_zero_of_le_zero hle
      refine ⟨(match bracketGraphMLAux 0 g with | .ok p => p | .error _ => 0), ?_⟩
      simp [bracketGraphMLAux, hvg, hn0, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | succ fuel =>
      by_cases hn0 : g.n = 0
      · refine ⟨(match bracketGraphMLAux (Nat.succ fuel) g with | .ok p => p | .error _ => 0), ?_⟩
        simp [bracketGraphMLAux, hvg, hn0, Bind.bind, Except.bind, Pure.pure, Except.pure]
      ·
        have hnle1 : g.n - 1 ≤ fuel := by
          -- `g.n ≤ fuel+1` implies `g.n-1 ≤ fuel`.
          simpa using (Nat.sub_le_sub_right hle 1)
        cases hpos : Reidemeister.r1RemoveLast g .pos with
        | ok g0 =>
            have hprops := r1RemoveLast_props_of_ok (g := g) (g0 := g0) (kind := .pos) hpos
            have hg0 : PDGraph.Valid g0 := hprops.1
            have hn0' : g0.n = g.n - 1 := hprops.2
            have hnle : g0.n ≤ fuel := by simpa [hn0'] using hnle1
            obtain ⟨b, hb⟩ := ih fuel (Nat.lt_succ_self fuel) g0 hg0 hnle
            refine ⟨(-(AML ^ 3 : PolyML)) * b, ?_⟩
            simp [bracketGraphMLAux, hvg, hn0, hpos, hb, Bind.bind, Except.bind, Pure.pure, Except.pure]
        | error _ =>
            cases hneg : Reidemeister.r1RemoveLast g .neg with
            | ok g0 =>
                have hprops := r1RemoveLast_props_of_ok (g := g) (g0 := g0) (kind := .neg) hneg
                have hg0 : PDGraph.Valid g0 := hprops.1
                have hn0' : g0.n = g.n - 1 := hprops.2
                have hnle : g0.n ≤ fuel := by simpa [hn0'] using hnle1
                obtain ⟨b, hb⟩ := ih fuel (Nat.lt_succ_self fuel) g0 hg0 hnle
                refine ⟨(-(AinvML ^ 3 : PolyML)) * b, ?_⟩
                simp [bracketGraphMLAux, hvg, hn0, hpos, hneg, hb, Bind.bind, Except.bind, Pure.pure, Except.pure]
            | error _ =>
                cases h2 : Reidemeister.r2RemoveLast g with
                | ok g0 =>
                    have hprops := r2RemoveLast_props_of_ok (g := g) (g0 := g0) h2
                    have hg0 : PDGraph.Valid g0 := hprops.1
                    have hn0' : g0.n = g.n - 2 := hprops.2.1
                    have hnGe2 : 2 ≤ g.n := hprops.2.2
                    -- The `r2RemoveLast` branch consumes two units of fuel.
                    cases fuel with
                    | zero =>
                        -- Outer fuel is `1`, but `r2RemoveLast` implies `g.n ≥ 2`.
                        have hle1 : g.n ≤ 1 := by simpa using hle
                        have h21 : (2 : Nat) ≤ 1 := Nat.le_trans hnGe2 hle1
                        exact ((by decide : ¬ (2 : Nat) ≤ 1) h21).elim
                    | succ fuel2 =>
                        have hnle2 : g.n - 2 ≤ fuel2 := by
                          simpa using (Nat.sub_le_sub_right hle 2)
                        have hnle : g0.n ≤ fuel2 := by simpa [hn0'] using hnle2
                        have hlt : fuel2 < Nat.succ (Nat.succ fuel2) := by
                          exact Nat.lt_trans (Nat.lt_succ_self fuel2) (Nat.lt_succ_self (Nat.succ fuel2))
                        obtain ⟨b, hb⟩ := ih fuel2 hlt g0 hg0 hnle
                        refine ⟨b, ?_⟩
                        simp [bracketGraphMLAux, hvg, hn0, hpos, hneg, h2, hb, Bind.bind, Except.bind, Pure.pure, Except.pure]
                | error _ =>
                    -- General skein step.
                    have hg0 : PDGraph.Valid ({ freeLoops := 0, n := g.n, arcNbr := g.arcNbr } : PDGraph) :=
                      valid_setFreeLoops (n := g.n) (arcNbr := g.arcNbr) (freeLoops₁ := g.freeLoops) (freeLoops₂ := 0) hg
                    have hnPos : 0 < g.n := Nat.pos_of_ne_zero hn0
                    have hgA0 :
                        PDGraph.Valid ({ freeLoops := 0, n := g.n - 1, arcNbr := smoothLastCoreML_rewire g.n g.arcNbr false } : PDGraph) :=
                      smoothLastCoreML_valid (n := g.n) (arcNbr := g.arcNbr) (isB := false) hnPos hg0
                    have hgB0 :
                        PDGraph.Valid ({ freeLoops := 0, n := g.n - 1, arcNbr := smoothLastCoreML_rewire g.n g.arcNbr true } : PDGraph) :=
                      smoothLastCoreML_valid (n := g.n) (arcNbr := g.arcNbr) (isB := true) hnPos hg0
                    let n' := g.n - 1
                    let freeA := (smoothLastCoreML g.freeLoops g.n g.arcNbr false).1
                    let nbrA := (smoothLastCoreML g.freeLoops g.n g.arcNbr false).2
                    let freeB := (smoothLastCoreML g.freeLoops g.n g.arcNbr true).1
                    let nbrB := (smoothLastCoreML g.freeLoops g.n g.arcNbr true).2
                    let gA : PDGraph := { freeLoops := freeA, n := n', arcNbr := nbrA }
                    let gB : PDGraph := { freeLoops := freeB, n := n', arcNbr := nbrB }
                    have hgA : PDGraph.Valid gA := by
                      have hgA1 :
                          PDGraph.Valid
                            ({ freeLoops := freeA, n := g.n - 1, arcNbr := smoothLastCoreML_rewire g.n g.arcNbr false } : PDGraph) :=
                        valid_setFreeLoops (n := g.n - 1) (arcNbr := smoothLastCoreML_rewire g.n g.arcNbr false)
                          (freeLoops₁ := 0) (freeLoops₂ := freeA) hgA0
                      have : PDGraph.Valid ({ freeLoops := freeA, n := g.n - 1, arcNbr := nbrA } : PDGraph) := by
                        simpa [nbrA, smoothLastCoreML] using hgA1
                      simpa [gA, n'] using this
                    have hgB : PDGraph.Valid gB := by
                      have hgB1 :
                          PDGraph.Valid
                            ({ freeLoops := freeB, n := g.n - 1, arcNbr := smoothLastCoreML_rewire g.n g.arcNbr true } : PDGraph) :=
                        valid_setFreeLoops (n := g.n - 1) (arcNbr := smoothLastCoreML_rewire g.n g.arcNbr true)
                          (freeLoops₁ := 0) (freeLoops₂ := freeB) hgB0
                      have : PDGraph.Valid ({ freeLoops := freeB, n := g.n - 1, arcNbr := nbrB } : PDGraph) := by
                        simpa [nbrB, smoothLastCoreML] using hgB1
                      simpa [gB, n'] using this
                    have hnle : n' ≤ fuel := by simpa [n'] using hnle1
                    obtain ⟨a, ha⟩ := ih fuel (Nat.lt_succ_self fuel) gA hgA (by simpa [gA] using hnle)
                    obtain ⟨b, hb⟩ := ih fuel (Nat.lt_succ_self fuel) gB hgB (by simpa [gB] using hnle)
                    have ha' :
                        bracketGraphMLAux fuel
                            ({ freeLoops := (smoothLastCoreML g.freeLoops g.n g.arcNbr false).1, n := n', arcNbr := (smoothLastCoreML g.freeLoops g.n g.arcNbr false).2 } : PDGraph) =
                          .ok a := by
                      simpa [gA, freeA, nbrA] using ha
                    have hb' :
                        bracketGraphMLAux fuel
                            ({ freeLoops := (smoothLastCoreML g.freeLoops g.n g.arcNbr true).1, n := n', arcNbr := (smoothLastCoreML g.freeLoops g.n g.arcNbr true).2 } : PDGraph) =
                          .ok b := by
                      simpa [gB, freeB, nbrB] using hb
                    refine ⟨(AML * a) + (AinvML * b), ?_⟩
                    simp [bracketGraphMLAux, hvg, hn0, hpos, hneg, h2, n', ha', hb', Bind.bind, Except.bind, Pure.pure, Except.pure]

end

/-- Totality corollary for the wrapper `bracketGraphML`. -/
theorem bracketGraphML_ok_of_valid {g : PDGraph} (hg : PDGraph.Valid g) :
    ∃ p, bracketGraphML g = .ok p := by
  simpa [bracketGraphML] using bracketGraphMLAux_ok_of_valid (fuel := g.n) (g := g) hg (le_rfl)

end Kauffman

end Knot
end Topology
end HeytingLean
