import Mathlib.Data.Finset.Sym
import HeytingLean.WPP.Wolfram.Multiway

namespace HeytingLean
namespace WPP
namespace Wolfram

/-!
# Branchial graphs + bounded path counting (finite Wolfram systems)

This module adds two “multiway” constructions that are standard in Wolfram Physics / SetReplace
presentations:

1. **Branchial graphs** at a fixed depth: nodes are states at that depth, and edges connect
   states that share a common immediate predecessor (siblings in the multiway graph).
2. **Path counting** at a fixed depth: count distinct *event-data labelled* paths of length `n`
   from the initial state to each reachable state.

The development is intentionally scoped to **finite** `P`/`V` so that exploration is `Finset`-based.
-/

universe u v

namespace System

variable {V : Type u} {P : Type v} (sys : System V P)

section Finite

variable [Fintype P] [DecidableEq P] [Fintype V] [DecidableEq V]

/-! ## Path enumeration (event-data labelled) -/

/-- Finite set of all event-data labelled paths of length `n`, together with their endpoint. -/
def pathsAtDepth : Nat → Finset (List sys.EventData × HGraph V)
  | 0 => {([], sys.init)}
  | n + 1 =>
      (pathsAtDepth n).biUnion (fun p =>
        (sys.stepEdges p.2).image (fun e => (p.1 ++ [e.1], e.2)))

/-- Every element of `pathsAtDepth n` has a path list of length `n`. -/
lemma mem_pathsAtDepth_len {n : Nat} {p : List sys.EventData} {t : HGraph V} :
    (p, t) ∈ sys.pathsAtDepth n → p.length = n := by
  classical
  -- generalize over `(p,t)` so the IH applies to predecessor paths
  revert p t
  induction n with
  | zero =>
      intro p t h
      rcases (by simpa [System.pathsAtDepth] using h) with ⟨rfl, rfl⟩
      simp
  | succ n ih =>
      intro p t h
      -- unpack `biUnion` + `image`
      rcases Finset.mem_biUnion.mp h with ⟨pt, hpt, hp⟩
      rcases Finset.mem_image.mp hp with ⟨e, _he, hEq⟩
      have hpEq : p = pt.1 ++ [e.1] := congrArg Prod.fst hEq.symm
      have hlen : pt.1.length = n := ih (p := pt.1) (t := pt.2) (by simpa using hpt)
      simp [hpEq, List.length_append, hlen]

/-- Projecting `stepEdges` to endpoints lands in `stepStates`. -/
lemma mem_stepStates_of_mem_stepEdges {s t : HGraph V} {ed : sys.EventData} :
    (ed, t) ∈ sys.stepEdges s → t ∈ sys.stepStates s := by
  intro h
  refine Finset.mem_image.mpr ?_
  exact ⟨(ed, t), h, rfl⟩

/-- Endpoints of depth-`n` paths are exactly the depth-`n` reachable states. -/
theorem image_snd_pathsAtDepth_eq_statesAtDepth : ∀ n,
    (sys.pathsAtDepth n).image Prod.snd = sys.statesAtDepth n := by
  classical
  intro n
  induction n with
  | zero =>
      simp [System.pathsAtDepth, System.statesAtDepth]
  | succ n ih =>
      ext t
      constructor
      · intro ht
        rcases Finset.mem_image.mp ht with ⟨pt, hpt, rfl⟩
        -- `pt ∈ pathsAtDepth (n+1)` gives a predecessor path and one step-edge
        rcases Finset.mem_biUnion.mp hpt with ⟨pt0, hpt0, hptStep⟩
        rcases Finset.mem_image.mp hptStep with ⟨e, he, rfl⟩
        have hs0 : pt0.2 ∈ sys.statesAtDepth n := by
          have : pt0.2 ∈ (sys.pathsAtDepth n).image Prod.snd := by
            refine Finset.mem_image.mpr ?_
            exact ⟨pt0, hpt0, rfl⟩
          simpa [ih] using this
        have ht1 : e.2 ∈ sys.stepStates pt0.2 :=
          sys.mem_stepStates_of_mem_stepEdges (s := pt0.2) (ed := e.1) (t := e.2) he
        -- `statesAtDepth (n+1)` is the union of `stepStates` from depth `n`
        exact Finset.mem_biUnion.mpr ⟨pt0.2, hs0, ht1⟩
      · intro ht
        -- `t ∈ statesAtDepth (n+1)` means there is a predecessor `s` in depth `n`
        -- and `t ∈ stepStates s`, so we can extend any depth-`n` path to `s`.
        rcases Finset.mem_biUnion.mp ht with ⟨s, hs, htstep⟩
        -- choose a witness path to `s` from the IH (it exists because `hs` is in the image)
        have hs' : s ∈ (sys.pathsAtDepth n).image Prod.snd := by
          simpa [ih] using hs
        rcases Finset.mem_image.mp hs' with ⟨pt0, hpt0, rfl⟩
        -- choose a witnessing edge-data for `t ∈ stepStates pt0.2`
        rcases (sys.mem_stepStates_iff (s := pt0.2) (t := t)).1 htstep with ⟨ed, hedAll, hedApp, hedApply⟩
        -- build the extended path pair
        refine Finset.mem_image.mpr ?_
        refine ⟨(pt0.1 ++ [ed], t), ?_, rfl⟩
        -- show `(pt0.1 ++ [ed], t) ∈ pathsAtDepth (n+1)`
        refine Finset.mem_biUnion.mpr ?_
        refine ⟨pt0, hpt0, ?_⟩
        refine Finset.mem_image.mpr ?_
        refine ⟨(ed, EventData.apply (sys := sys) ed pt0.2), ?_, ?_⟩
        · -- `(ed, apply ed s)` is indeed a step-edge from `s`
          have : (ed, EventData.apply (sys := sys) ed pt0.2) ∈ sys.stepEdges pt0.2 :=
            (sys.mem_stepEdges_iff (s := pt0.2) (ed := ed) (t := EventData.apply (sys := sys) ed pt0.2)).2
              ⟨hedAll, hedApp, rfl⟩
          simpa [EventData.apply, hedApply] using this
        · simp [hedApply]

/-- Count distinct depth-`n` event-data paths ending at `t`. -/
def pathCountAtDepth (n : Nat) (t : HGraph V) : Nat :=
  ((sys.pathsAtDepth n).filter (fun p => p.2 = t)).card

/-! ## Branchial graphs (siblings share a predecessor) -/

/-- Unordered sibling-pairs among the children of a state (self-pairs removed). -/
def siblingEdges (s : HGraph V) : Finset (Sym2 (HGraph V)) :=
  ((sys.stepStates s).sym2).filter (fun z => ¬ z.IsDiag)

/-- The branchial edges at exact depth `n`. -/
def branchialEdgesAtDepth : Nat → Finset (Sym2 (HGraph V))
  | 0 => ∅
  | n + 1 => (sys.statesAtDepth n).biUnion (fun s => sys.siblingEdges s)

end Finite

end System

end Wolfram
end WPP
end HeytingLean
