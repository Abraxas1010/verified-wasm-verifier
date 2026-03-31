import HeytingLean.LoF.Combinators.Category.BranchialMetric

/-!
# Smoke test: `BranchialMetric` (graph distance on branchial slices)

This file checks that the `SimpleGraph.edist` metric induced by `branchialEdgesAtDepth`
behaves as expected on a tiny concrete SKY example with two sibling children.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open scoped Classical

open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.Combinators.Category

namespace Example

open Combinators.Category.Branchial

abbrev t0 : Comb :=
  (Comb.app (Comb.app .K .K) (Comb.app (Comb.app .K .K) .S))

def edRoot : Comb.EventData := { rule := .K, path := [] }
def childRoot : Comb := .K

def edRight : Comb.EventData := { rule := .K, path := [Comb.Dir.R] }
def childRight : Comb := Comb.app (Comb.app .K .K) .K

lemma mem_stepEdges_root : (edRoot, childRoot) ∈ Comb.stepEdges t0 := by
  native_decide

lemma mem_stepEdges_right : (edRight, childRight) ∈ Comb.stepEdges t0 := by
  native_decide

lemma mem_stepStates_childRoot : childRoot ∈ Branchial.stepStates t0 :=
  Branchial.mem_stepStates_of_mem_stepEdges (s := t0) (t := childRoot) (ed := edRoot) mem_stepEdges_root

lemma mem_stepStates_childRight : childRight ∈ Branchial.stepStates t0 :=
  Branchial.mem_stepStates_of_mem_stepEdges (s := t0) (t := childRight) (ed := edRight) mem_stepEdges_right

lemma mem_statesAtDepth1_childRoot : childRoot ∈ Branchial.statesAtDepth t0 1 := by
  -- `statesAtDepth t0 1` is the union of `stepStates` over the singleton `{t0}`.
  simp [Branchial.statesAtDepth, mem_stepStates_childRoot]

lemma mem_statesAtDepth1_childRight : childRight ∈ Branchial.statesAtDepth t0 1 := by
  simp [Branchial.statesAtDepth, mem_stepStates_childRight]

def vRoot : Branchial.Slice t0 1 :=
  ⟨childRoot, mem_statesAtDepth1_childRoot⟩

def vRight : Branchial.Slice t0 1 :=
  ⟨childRight, mem_statesAtDepth1_childRight⟩

-- The siblings are adjacent, so distance is exactly `1`.
example : Branchial.sliceEdist t0 1 vRoot vRight = 1 := by
  -- Reduce to the generic `edist_eq_one_iff_adj` lemma.
  have hadj : (Branchial.sliceGraph t0 1).Adj vRoot vRight := by
    -- membership in `branchialEdgesAtDepth` is established in the `BranchialGraph` sanity file;
    -- we reprove it here directly via `siblingEdges`.
    have hsib : s(childRoot, childRight) ∈ Branchial.siblingEdges t0 := by
      apply (Branchial.mem_siblingEdges_iff (parent := t0) (t := childRoot) (u := childRight)).2
      refine ⟨mem_stepStates_childRoot, mem_stepStates_childRight, ?_⟩
      decide
    have hedges : s(childRoot, childRight) ∈ Branchial.branchialEdgesAtDepth t0 1 := by
      refine (Finset.mem_biUnion).2 ?_
      refine ⟨t0, ?_, hsib⟩
      simp [Branchial.statesAtDepth]
    simpa [Branchial.sliceGraph, vRoot, vRight] using hedges
  -- Now `edist = 1` iff adjacent.
  exact (Branchial.sliceEdist_eq_one_iff_adj t0 0 vRoot vRight).2 hadj

end Example

end LoF
end Tests
end HeytingLean

