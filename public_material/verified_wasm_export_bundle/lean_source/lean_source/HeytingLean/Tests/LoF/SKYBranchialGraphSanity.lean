import HeytingLean.LoF.Combinators.Category.BranchialGraph

/-!
# Smoke test: `BranchialGraph` (siblings share a predecessor)

This file checks that the finite branchial adjacency defined in
`HeytingLean.LoF.Combinators.Category.BranchialGraph` matches the computed SKY multiway edges.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.Combinators.Category
open Combinators.Category.Branchial

namespace Example

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

lemma mem_stepStates_childRoot : childRoot ∈ stepStates t0 :=
  mem_stepStates_of_mem_stepEdges (s := t0) (t := childRoot) (ed := edRoot) mem_stepEdges_root

lemma mem_stepStates_childRight : childRight ∈ stepStates t0 :=
  mem_stepStates_of_mem_stepEdges (s := t0) (t := childRight) (ed := edRight) mem_stepEdges_right

lemma mem_siblingEdges_t0 : s(childRoot, childRight) ∈ siblingEdges t0 := by
  apply (mem_siblingEdges_iff (parent := t0) (t := childRoot) (u := childRight)).2
  refine ⟨mem_stepStates_childRoot, ?_⟩
  refine ⟨mem_stepStates_childRight, ?_⟩
  decide

-- The graph edge induces a depth-1 branchial witness.
example : BranchialAt 1 childRoot childRight :=
  branchialAt_one_of_mem_siblingEdges (parent := t0) (t := childRoot) (u := childRight)
    mem_siblingEdges_t0

-- Depth-1 branchial edges from `t0` are exactly sibling edges of `t0`.
example : s(childRoot, childRight) ∈ branchialEdgesAtDepth t0 1 := by
  -- `branchialEdgesAtDepth t0 1` is the `biUnion` of sibling edges over the singleton slice `{t0}`.
  refine (Finset.mem_biUnion).2 ?_
  refine ⟨t0, ?_, mem_siblingEdges_t0⟩
  simp [statesAtDepth]

end Example

end LoF
end Tests
end HeytingLean
