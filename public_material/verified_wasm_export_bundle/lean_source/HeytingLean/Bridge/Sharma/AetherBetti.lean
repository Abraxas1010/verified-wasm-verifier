import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

import HeytingLean.Computational.Homology.ChainComplex
import HeytingLean.Compiler.TensorLogic.HomologyFromFacts
import HeytingLean.MirandaDynamics.Topology.BettiComplexity

/-!
# AETHER Betti Approximation Bounds

Phase-4 bridge module:
- Teerth-style 4-window heuristic (`betti1_heuristic`)
- exact F₂ Betti computation via `ChainComplexF2.bettiAt`
- cycle-rank bridge target from `MirandaDynamics.Topology.BettiComplexity`
-/

namespace HeytingLean.Bridge.Sharma.AetherBetti

open HeytingLean.Computational.Homology
open HeytingLean.Compiler.TensorLogic
open HeytingLean.Compiler.TensorLogic.HomologyFromFacts
open HeytingLean.MirandaDynamics.Topology

/-- Byte sequence input. -/
abbrev ByteSeq (n : ℕ) := Fin n → Fin 256

/-- A simple tolerance relation replacing absolute-distance notation. -/
def withinTol (a b tol : Nat) : Prop :=
  a ≤ b + tol ∧ b ≤ a + tol

instance instDecidableWithinTol (a b tol : Nat) : Decidable (withinTol a b tol) := by
  unfold withinTol
  infer_instance

/-- Separation beyond tolerance in either direction. -/
def separated (a b tol : Nat) : Prop :=
  a > b + tol ∨ b > a + tol

instance instDecidableSeparated (a b tol : Nat) : Decidable (separated a b tol) := by
  unfold separated
  infer_instance

/-- ε-neighborhood graph on byte positions. -/
def epsilonGraph {n : ℕ} (data : ByteSeq n) (eps : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ withinTol (data i).1 (data j).1 eps
  symm := by
    intro i j h
    rcases h with ⟨hij, htol⟩
    exact ⟨hij.symm, And.symm htol⟩
  loopless := by
    intro i h
    exact h.1 rfl

/-- Vertex label used by the homology-from-facts bridge. -/
def vertexName {n : ℕ} (i : Fin n) : String :=
  s!"v{i.1}"

/-- TensorLogic fact list encoding of the ε-graph 1-skeleton. -/
def epsilonFacts {n : ℕ} (data : ByteSeq n) (eps : ℕ) : List (Atom × Float) :=
  let verts : List (Atom × Float) :=
    (List.finRange n).map (fun i =>
      ({ pred := "vertex", args := [vertexName i] }, 1.0))
  let edges : List (Atom × Float) :=
    (List.finRange n).foldl
      (fun acc i =>
        acc ++
          (List.finRange n).filterMap (fun j =>
            if _hij : i.1 < j.1 then
              if withinTol (data i).1 (data j).1 eps then
                some ({ pred := "edge", args := [vertexName i, vertexName j] }, 1.0)
              else
                none
            else
              none))
      []
  verts ++ edges

/-- Build an F₂ chain complex from the ε-graph fact encoding. -/
def epsilonChainComplex {n : ℕ} (data : ByteSeq n) (eps : ℕ) : Except String ChainComplexF2 :=
  HomologyFromFacts.chainComplexF2 (epsilonFacts data eps)

/-- Exact β₁ from the existing computational homology pipeline. -/
def betti1_true {n : ℕ} (data : ByteSeq n) (eps : ℕ) : Except String Nat := do
  let C ← epsilonChainComplex data eps
  C.bettiAt 1

/-- Byte accessor with total behavior for index arithmetic. -/
def byteAt {n : ℕ} (data : ByteSeq n) (idx : Nat) : Nat :=
  if h : idx < n then
    (data ⟨idx, h⟩).1
  else
    0

/-- Teerth-style 4-window detection predicate at start index `i`. -/
def isDetectedLoop {n : ℕ} (data : ByteSeq n) (i : Fin n) (tol : ℕ) : Prop :=
  i.1 + 3 < n ∧
  let a := byteAt data i.1
  let b := byteAt data (i.1 + 1)
  let c := byteAt data (i.1 + 2)
  let d := byteAt data (i.1 + 3)
  withinTol a d tol ∧ (separated a b tol ∨ separated a c tol)

instance instDecidableIsDetectedLoop {n : ℕ} (data : ByteSeq n) (i : Fin n) (tol : ℕ) :
    Decidable (isDetectedLoop data i tol) := by
  unfold isDetectedLoop withinTol separated byteAt
  infer_instance

/-- Heuristic β̂₁: count detected windows. -/
def betti1_heuristic {n : ℕ} (data : ByteSeq n) (tol : ℕ) : Nat :=
  (Finset.univ.filter (fun i : Fin n => isDetectedLoop data i tol)).card

/-- Any detected window yields a non-degenerate 4-node window witness list. -/
theorem heuristic_sound {n : ℕ} (data : ByteSeq n) (tol : ℕ) (i : Fin n)
    (h : isDetectedLoop data i tol) :
    ∃ cycle : List (Fin n), cycle.length = 4 ∧ cycle.head? = some i ∧
      ∃ j : Fin n, cycle.getLast? = some j ∧ i ≠ j := by
  have hroom : i.1 + 3 < n := h.1
  let i1 : Fin n := ⟨i.1 + 1, by omega⟩
  let i2 : Fin n := ⟨i.1 + 2, by omega⟩
  let i3 : Fin n := ⟨i.1 + 3, by omega⟩
  refine ⟨[i, i1, i2, i3], by simp [i1, i2, i3], by simp [i1, i2, i3], i3,
    by simp [i1, i2, i3], ?_⟩
  intro hEq
  have hvals : i.1 = i3.1 := congrArg Fin.val hEq
  simp [i3] at hvals

/-- Trivial finite bound on heuristic detections. -/
theorem heuristic_upper_bound {n : ℕ} (data : ByteSeq n) (tol : ℕ) :
    betti1_heuristic data tol ≤ n := by
  unfold betti1_heuristic
  simpa using (Finset.card_filter_le (s := (Finset.univ : Finset (Fin n)))
    (p := fun i : Fin n => isDetectedLoop data i tol))

/-- Tight window-index bound: valid start indices are bounded by `n - 3`. -/
theorem heuristic_window_bound {n : ℕ} (data : ByteSeq n) (tol : ℕ) :
    betti1_heuristic data tol ≤ n - 3 := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => isDetectedLoop data i tol)
  have hsubset : S.map Fin.valEmbedding ⊆ Finset.range (n - 3) := by
    intro m hm
    rcases Finset.mem_map.mp hm with ⟨i, hiS, rfl⟩
    have hroom : i.1 + 3 < n := (Finset.mem_filter.mp hiS).2.1
    have hi_lt : i.1 < n - 3 := by
      exact (Nat.lt_sub_iff_add_lt).2 (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hroom)
    exact Finset.mem_range.mpr hi_lt
  have hmapCard :
      (S.map Fin.valEmbedding).card = S.card := by
    exact Finset.card_map (f := Fin.valEmbedding) (s := S)
  have hcardMap :
      (S.map Fin.valEmbedding).card ≤ (Finset.range (n - 3)).card :=
    Finset.card_le_card hsubset
  have hcard : S.card ≤ n - 3 := by
    simpa [hmapCard] using hcardMap
  simpa [betti1_heuristic, S] using hcard

/-- Connected-tree case from the existing cycle-rank theory. -/
theorem cycleRank_zero_of_connected_tree {n : ℕ}
    (data : ByteSeq n) (eps : ℕ)
    (hTree : (epsilonGraph data eps).IsTree) :
    cycleRank (epsilonGraph data eps) = 0 :=
  cycleRank_eq_zero_of_isTree (G := epsilonGraph data eps) hTree

/--
Phase-4 bridge obligation at the chain-complex layer.

This is intentionally stronger than a direct `betti1_true = ...` passthrough:
it asks for agreement on every successful chain-complex realization.
-/
def ChainBettiBridge {n : ℕ} (data : ByteSeq n) (eps : ℕ) : Prop :=
  ∀ C : ChainComplexF2, epsilonChainComplex data eps = .ok C →
    C.bettiAt 1 = .ok (cycleRank (epsilonGraph data eps))

/--
Totalized β₁ bridge target: if the graph realization has no 1-cells, interpret
β₁ as `0` rather than treating `bettiAt 1` as out-of-range.
-/
def ChainBettiBridgeTotal {n : ℕ} (data : ByteSeq n) (eps : ℕ) : Prop :=
  ∀ C : ChainComplexF2, epsilonChainComplex data eps = .ok C →
    (match C.bettiAt 1 with
    | .ok b => b
    | .error _ => 0) = cycleRank (epsilonGraph data eps)

/-! ## Singleton counterexample and corrected totalized witness -/

private def singletonData : ByteSeq 1 :=
  fun _ => ⟨7, by decide⟩

private theorem singletonGraph_eq_bot :
    epsilonGraph singletonData 0 = (⊥ : SimpleGraph (Fin 1)) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [epsilonGraph, singletonData, withinTol]

private theorem cycleRank_singleton_zero :
    cycleRank (epsilonGraph singletonData 0) = 0 := by
  rw [singletonGraph_eq_bot]
  simp [MirandaDynamics.Topology.cycleRank]

/--
The raw bridge target is false on graphs with no 1-cells: the fact-built chain
complex succeeds, but `bettiAt 1` reports an out-of-range error rather than
returning `0`.
-/
theorem singleton_not_ChainBettiBridge : ¬ ChainBettiBridge singletonData 0 := by
  intro h
  have hOk :
      (match epsilonChainComplex singletonData 0 with
      | .ok _ => true
      | .error _ => false) = true := by
    native_decide
  cases hC : epsilonChainComplex singletonData 0 with
  | error msg =>
      simp [hC] at hOk
  | ok C =>
      have hErr :
          (match C.bettiAt 1 with
          | .error _ => true
          | _ => false) = true := by
        have :
            (match epsilonChainComplex singletonData 0 with
            | .ok C => match C.bettiAt 1 with
              | .error _ => true
              | _ => false
            | .error _ => false) = true := by
          native_decide
        simpa [hC] using this
      have hEq := h C hC
      rw [hEq] at hErr
      simp at hErr

/--
The totalized bridge target has the intended behavior on the singleton graph:
the missing `β₁` slot is interpreted as `0`, matching cycle rank `0`.
-/
theorem singleton_ChainBettiBridgeTotal : ChainBettiBridgeTotal singletonData 0 := by
  intro C hC
  have hErr :
      (match C.bettiAt 1 with
      | .error _ => true
      | _ => false) = true := by
    have :
        (match epsilonChainComplex singletonData 0 with
        | .ok C => match C.bettiAt 1 with
          | .error _ => true
          | _ => false
        | .error _ => false) = true := by
      native_decide
    simpa [hC] using this
  have hBettiZero : (match C.bettiAt 1 with | .ok b => b | .error _ => 0) = 0 := by
    cases hBetti : C.bettiAt 1 with
    | error err =>
        simp
    | ok b =>
        rw [hBetti] at hErr
        simp at hErr
  simpa [cycleRank_singleton_zero] using hBettiZero

/-- Automatic formulation over the actual `betti1_true` pipeline output. -/
theorem betti_error_auto {n : ℕ} (data : ByteSeq n) (tol : ℕ)
    (hn : 4 ≤ n) (eps : ℕ := tol + 1) :
    match betti1_true data eps with
    | .ok b => betti1_heuristic data tol ≤ b + (n - 3)
    | .error _ => True := by
  cases h : betti1_true data eps with
  | ok b =>
      have hn3 : 3 ≤ n := le_trans (by decide : 3 ≤ 4) hn
      have hw : betti1_heuristic data tol ≤ n - 3 := heuristic_window_bound data tol
      have hbound : betti1_heuristic data tol ≤ b + (n - 3) := by
        omega
      simpa [h] using hbound
  | error msg =>
      simp

/-- Unconditional error bound from the window-count theorem. -/
theorem betti_error_bound {n : ℕ} (data : ByteSeq n) (tol : ℕ)
    (hn : 4 ≤ n) (eps : ℕ := tol + 1)
    {b : Nat} (hBetti : betti1_true data eps = .ok b) :
    betti1_heuristic data tol ≤ b + (n - 3) := by
  have hauto := betti_error_auto (data := data) (tol := tol) (hn := hn) (eps := eps)
  simpa [hBetti] using hauto

/-- A monotone no-oscillation sample used by sanity tests. -/
def linearData : ByteSeq 8 :=
  fun i => ⟨i.1, by omega⟩

end HeytingLean.Bridge.Sharma.AetherBetti
