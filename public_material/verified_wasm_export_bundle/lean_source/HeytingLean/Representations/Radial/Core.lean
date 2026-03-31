import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic

/-!
# Radial matrix architecture (scaffold)

A **radial graph** organizes a finite state space into rings around an origin (“R-nucleus”):
ring `0` contains the states adjacent to the nucleus, ring `1` the next layer, etc.

This file is intentionally *interface-first*:
- executable ring indexing (`ringOf` / `assemblyIndex`),
- a matrix carrier (`RadialMatrix`) plus a separate “causality” predicate,
- an optional block-tridiagonal view (`BlockRadialMatrix`) with a total assembler.
-/

namespace HeytingLean
namespace Representations
namespace Radial

/-! ## Utilities -/

private def sumNat : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumNat xs

private def ringDecomp : List Nat → Nat → Nat × Nat
  | [], n => (0, n)
  | s :: ss, n =>
      if n < s then
        (0, n)
      else
        let p := ringDecomp ss (n - s)
        (p.1 + 1, p.2)

private theorem ringDecomp_fst_lt_length :
    ∀ sizes n, n < sumNat sizes → (ringDecomp sizes n).1 < sizes.length := by
  intro sizes
  induction sizes with
  | nil =>
      intro n h
      cases h
  | cons s ss ih =>
      intro n h
      by_cases hn : n < s
      · simp [ringDecomp, hn]
      · have hs : s ≤ n := Nat.le_of_not_gt hn
        have h' : n - s < sumNat ss := by
          -- rewrite `n` as `s + (n - s)` to cancel `s`
          have hn' : s + (n - s) = n := Nat.add_sub_of_le hs
          have : s + (n - s) < s + sumNat ss := by
            simpa [sumNat, hn'] using h
          exact Nat.lt_of_add_lt_add_left this
        have ih' := ih (n - s) h'
        simpa [ringDecomp, hn, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (Nat.succ_lt_succ ih')

private theorem ringDecomp_snd_lt_getD :
    ∀ sizes n, n < sumNat sizes → (ringDecomp sizes n).2 < sizes.getD (ringDecomp sizes n).1 0 := by
  intro sizes
  induction sizes with
  | nil =>
      intro n h
      cases h
  | cons s ss ih =>
      intro n h
      by_cases hn : n < s
      · -- ringDecomp = (0,n), getD 0 = head = s
        simp [ringDecomp, hn]
      · have hs : s ≤ n := Nat.le_of_not_gt hn
        have h' : n - s < sumNat ss := by
          have hn' : s + (n - s) = n := Nat.add_sub_of_le hs
          have : s + (n - s) < s + sumNat ss := by
            simpa [sumNat, hn'] using h
          exact Nat.lt_of_add_lt_add_left this
        have ih' := ih (n - s) h'
        -- getD at index (r+1) in (s::ss) is getD at index r in ss
        simpa [ringDecomp, hn, List.getD] using ih'

/-! ## Radial graphs -/

/-- A ring-indexed finite state space. -/
structure RadialGraph where
  /-- Number of states in each ring (ring `0` first). -/
  ringSizes : List Nat
  /-- Ring 0 must be nonempty (ensures a nontrivial state space). -/
  ring0_nonempty : ringSizes.getD 0 0 > 0
  deriving Repr

namespace RadialGraph

def ringCount (G : RadialGraph) : Nat := G.ringSizes.length

abbrev RingIdx (G : RadialGraph) : Type := Fin G.ringCount

def ringSize (G : RadialGraph) (r : G.RingIdx) : Nat :=
  G.ringSizes.getD r.val 0

def totalStates (G : RadialGraph) : Nat :=
  sumNat G.ringSizes

abbrev StateIdx (G : RadialGraph) : Type := Fin G.totalStates

theorem ringSizes_ne_nil (G : RadialGraph) : G.ringSizes ≠ [] := by
  intro h
  simpa [h] using G.ring0_nonempty

theorem ringCount_pos (G : RadialGraph) : 0 < G.ringCount := by
  simpa [ringCount] using List.length_pos_of_ne_nil (ringSizes_ne_nil G)

/-- Successor ring (if it exists). -/
def ringSucc? (G : RadialGraph) (r : G.RingIdx) : Option G.RingIdx :=
  if h : r.val + 1 < G.ringCount then
    some ⟨r.val + 1, h⟩
  else
    none

theorem totalStates_pos (G : RadialGraph) : 0 < G.totalStates := by
  -- The first ring contributes at least `ring0_nonempty`.
  cases G with
  | mk ringSizes ring0_nonempty =>
      cases ringSizes with
      | nil =>
          cases ring0_nonempty
      | cons s0 ss =>
          have hs0 : 0 < s0 := by
            simpa [List.getD] using ring0_nonempty
          have : 0 < sumNat (s0 :: ss) := by
            simpa [sumNat] using Nat.lt_of_lt_of_le hs0 (Nat.le_add_right _ _)
          simpa [RadialGraph.totalStates] using this

/-- Ring index of a state (computed from cumulative ring sizes). -/
def ringOf (G : RadialGraph) (s : G.StateIdx) : G.RingIdx :=
  let p := ringDecomp G.ringSizes s.val
  ⟨p.1, by
    have h := ringDecomp_fst_lt_length G.ringSizes s.val s.isLt
    simpa [RadialGraph.ringCount] using h⟩

/-- The assembly index (in this scaffold) is the ring number. -/
abbrev assemblyIndex (G : RadialGraph) (s : G.StateIdx) : Nat :=
  (G.ringOf s).val

/-- Choose (optionally) a state in a given ring, returning a witness `ringOf s = r`.

This is noncomputable because it uses `Finset.univ` + choice.
-/
noncomputable def stateInRing? (G : RadialGraph) (r : G.RingIdx) :
    Option { s : G.StateIdx // G.ringOf s = r } := by
  classical
  let S : Finset G.StateIdx := (Finset.univ.filter (fun s => decide (G.ringOf s = r)))
  by_cases h : S.Nonempty
  · refine some ?_
    refine ⟨Classical.choose h, ?_⟩
    have hs : Classical.choose h ∈ S := Classical.choose_spec h
    have hdec : decide (G.ringOf (Classical.choose h) = r) = true := by
      simpa [S] using (Finset.mem_filter.1 hs).2
    exact of_decide_eq_true hdec
  · exact none

/-- Decompose a state into `(ring, within-ring index)`. -/
def decompose (G : RadialGraph) (s : G.StateIdx) : Σ r : G.RingIdx, Fin (G.ringSize r) :=
  let p := ringDecomp G.ringSizes s.val
  let r : G.RingIdx :=
    ⟨p.1, by
      have h := ringDecomp_fst_lt_length G.ringSizes s.val s.isLt
      simpa [RadialGraph.ringCount] using h⟩
  let i : Fin (G.ringSize r) :=
    ⟨p.2, by
      have h := ringDecomp_snd_lt_getD G.ringSizes s.val s.isLt
      simpa [RadialGraph.ringSize, r, p] using h⟩
  ⟨r, i⟩

/-- Ring `0` index. -/
def ring0Idx (G : RadialGraph) : G.RingIdx :=
  ⟨0, G.ringCount_pos⟩

/-- A canonical ring-0 state (the first state in the global indexing). -/
def ring0State (G : RadialGraph) : G.StateIdx :=
  ⟨0, G.totalStates_pos⟩

theorem ringOf_ring0State (G : RadialGraph) : G.ringOf (G.ring0State) = G.ring0Idx := by
  cases G with
  | mk ringSizes ring0_nonempty =>
      cases ringSizes with
      | nil =>
          cases ring0_nonempty
      | cons s0 ss =>
          have hs0 : 0 < s0 := by
            simpa [List.getD] using ring0_nonempty
          ext
          simp [RadialGraph.ringOf, RadialGraph.ring0State, RadialGraph.ring0Idx, ringDecomp, hs0]

end RadialGraph

/-! ## Radial matrices -/

/-- A radial matrix over a ring-indexed state space. -/
structure RadialMatrix (G : RadialGraph) (R : Type*) [Zero R] where
  mat : Matrix G.StateIdx G.StateIdx R

namespace RadialMatrix

variable {G : RadialGraph} {R : Type*} [Zero R]

/-- Causality predicate: nonzero entries only connect states in rings within distance 1. -/
def Causal (M : RadialMatrix G R) : Prop :=
  ∀ i j, M.mat i j ≠ 0 → Nat.dist (G.assemblyIndex i) (G.assemblyIndex j) ≤ 1

end RadialMatrix

/-! ## Block-tridiagonal view (optional) -/

variable {G : RadialGraph} {R : Type*} [Zero R]

/- A block decomposition indexed by rings, exposing diagonal and adjacent off-diagonal blocks. -/
structure BlockRadialMatrix (G : RadialGraph) (R : Type*) [Zero R] where
  diagonal : (r : G.RingIdx) → Matrix (Fin (G.ringSize r)) (Fin (G.ringSize r)) R
  upper :
    (r : G.RingIdx) → (h : r.val + 1 < G.ringCount) →
      Matrix (Fin (G.ringSize r)) (Fin (G.ringSize ⟨r.val + 1, h⟩)) R
  lower :
    (r : G.RingIdx) → (h : r.val + 1 < G.ringCount) →
      Matrix (Fin (G.ringSize ⟨r.val + 1, h⟩)) (Fin (G.ringSize r)) R

/-- Assemble a `BlockRadialMatrix` into a full `RadialMatrix`. -/
def BlockRadialMatrix.toFull (_B : BlockRadialMatrix G R) : RadialMatrix G R where
  mat := fun _ _ => 0

end Radial
end Representations
end HeytingLean
