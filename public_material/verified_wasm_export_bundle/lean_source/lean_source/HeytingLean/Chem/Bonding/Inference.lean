import HeytingLean.Chem.Bonding.BondGraph
import HeytingLean.Chem.PeriodicTable.Valence
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# Bond-graph inference (bounded, heuristic)

This module provides a *computable* (bounded) bond-graph generator intended for:
- small-molecule scaffolding (smoke tests, toy examples);
- early-stage materials tooling that needs a plausible bond graph before an
  energetic model is selected.

It is **not** a chemistry oracle. It encodes simple valence heuristics derived
from our periodic-table model (`PeriodicTable.valenceElectrons`).
-/

namespace HeytingLean
namespace Chem
namespace Bonding

open HeytingLean.Chem.PeriodicTable

/-!
## Valence heuristic

For s/p block elements we use a simple "octet-style" valence bound:
`min(v, 8 - v)` where `v = valenceElectrons`, with special cases.

For d/f block we currently use a permissive bound (12) to avoid prematurely
excluding coordination chemistry. This is intentionally conservative.
-/

def covalentValenceBound (e : Element) : Nat :=
  match block e with
  | .s | .p =>
      let v := valenceElectrons e
      -- Noble gases: treat as closed-shell for covalent bonding heuristics.
      match iupacGroup? e with
      | some 18 => 0
      | _ =>
          if v ≤ 4 then v else (8 - v)
  | .d | .f => 12

def BondGraph.CovalentValenceOk {n : Nat} (g : BondGraph n) : Prop :=
  ∀ v, BondGraph.valenceDegree g v ≤ covalentValenceBound (g.atoms v).element

/-- Avoid fully disconnected "solutions": every atom that *can* bond (bound > 0) must participate. -/
def BondGraph.NoIsolatedCovalent {n : Nat} (g : BondGraph n) : Prop :=
  ∀ v, covalentValenceBound (g.atoms v).element > 0 → BondGraph.valenceDegree g v > 0

/-!
For small-molecule heuristics we usually want *saturation* for s/p-block elements.
We enforce this only for elements whose computed covalent bound is in `{1,2,3,4}`.
(We do not attempt to saturate transition metals / f-block here.)
-/
def BondGraph.CovalentValenceSaturated {n : Nat} (g : BondGraph n) : Prop :=
  ∀ v,
    let b := covalentValenceBound (g.atoms v).element
    b ≤ 4 → b > 0 → BondGraph.valenceDegree g v = b

instance {n : Nat} (g : BondGraph n) : Decidable (BondGraph.CovalentValenceOk g) := by
  unfold BondGraph.CovalentValenceOk
  infer_instance

instance {n : Nat} (g : BondGraph n) : Decidable (BondGraph.NoIsolatedCovalent g) := by
  unfold BondGraph.NoIsolatedCovalent
  infer_instance

instance {n : Nat} (g : BondGraph n) : Decidable (BondGraph.CovalentValenceSaturated g) := by
  unfold BondGraph.CovalentValenceSaturated
  infer_instance

def covalentSingle : BondType :=
  { kind := .covalent, order := some .single }

def covalentDouble : BondType :=
  { kind := .covalent, order := some .double }

def covalentTriple : BondType :=
  { kind := .covalent, order := some .triple }

def covalentOrdersUpTo (maxOrder : Nat) : List BondType :=
  match maxOrder with
  | 0 => []
  | 1 => [covalentSingle]
  | 2 => [covalentSingle, covalentDouble]
  | _ => [covalentSingle, covalentDouble, covalentTriple]

/-!
## Bounded generator

We enumerate undirected pairs `(i,j)` with `i<j` and branch on:
- skip the edge, or
- add the edge with one of the allowed covalent bond orders.

The search is bounded by `maxEdges` (total number of bonds).
-/

def allPairs (n : Nat) : List (Fin n × Fin n) :=
  List.flatMap
    (fun i =>
      (List.finRange n).filterMap (fun j =>
        if i.1 < j.1 then some (i, j) else none))
    (List.finRange n)

def mkEdge {n : Nat} (i j : Fin n) (ty : BondType) : BondEdge n :=
  { i := i, j := j, ty := ty }

private def inferBondSetsAux {n : Nat} (atoms : Fin n → Atom)
    (pairs : List (Fin n × Fin n)) (orders : List BondType)
    (maxEdges : Nat) (acc : Finset (BondEdge n)) : List (Finset (BondEdge n)) :=
  match pairs with
  | [] => [acc]
  | (i, j) :: ps =>
      let skip := inferBondSetsAux atoms ps orders maxEdges acc
      if acc.card = maxEdges then
        skip
      else
        let addOne (ty : BondType) : List (Finset (BondEdge n)) :=
          let acc' := insert (mkEdge i j ty) acc
          let g' : BondGraph n := { atoms := atoms, bonds := acc' }
          if decide (BondGraph.CovalentValenceOk g') then
            inferBondSetsAux atoms ps orders maxEdges acc'
          else
            []
        skip ++ (List.flatMap addOne orders)

def inferBondGraphs {n : Nat} (atoms : Fin n → Atom) (maxEdges maxOrder : Nat) : List (BondGraph n) :=
  let orders := covalentOrdersUpTo maxOrder
  let sets := inferBondSetsAux atoms (allPairs n) orders maxEdges (∅)
  let graphs := sets.map (fun bonds => ({ atoms := atoms, bonds := bonds } : BondGraph n))
  graphs.filter (fun g =>
    decide (BondGraph.CovalentValenceOk g ∧ BondGraph.NoIsolatedCovalent g ∧ BondGraph.CovalentValenceSaturated g))

def inferBondGraph? {n : Nat} (atoms : Fin n → Atom) (maxEdges maxOrder : Nat) : Option (BondGraph n) :=
  (inferBondGraphs atoms maxEdges maxOrder).head?

/-!
## Structural soundness: inferred graphs are loop-free

Our generator enumerates only pairs `(i,j)` with `i < j`, so any produced `BondGraph` is
loop-free (`i ≠ j` for every bond edge).

This matters for downstream “hard-constraint gating”: we can treat `BondGraph.Valid` as a
guaranteed invariant of the inference backend rather than an extra check.
-/

private def AccValid {n : Nat} (acc : Finset (BondEdge n)) : Prop :=
  ∀ e, e ∈ acc → e.i ≠ e.j

private lemma accValid_empty {n : Nat} : AccValid (n := n) (∅ : Finset (BondEdge n)) := by
  intro e he
  cases he

private lemma accValid_insert {n : Nat} {acc : Finset (BondEdge n)} {eNew : BondEdge n}
    (hAcc : AccValid (n := n) acc) (hNew : eNew.i ≠ eNew.j) :
    AccValid (n := n) (insert eNew acc) := by
  intro e he
  have := Finset.mem_insert.mp he
  cases this with
  | inl h =>
      simpa [h] using hNew
  | inr h =>
      exact hAcc e h

private lemma mem_allPairs_lt {n : Nat} {p : Fin n × Fin n} (hp : p ∈ allPairs n) :
    p.1.1 < p.2.1 := by
  -- `allPairs` was defined by `filterMap` with guard `i < j`.
  classical
  unfold allPairs at hp
  rcases List.mem_flatMap.1 hp with ⟨i, hi, hp⟩
  rcases List.mem_filterMap.1 hp with ⟨j, hj, hjp⟩
  -- The only way to produce `some p` is that the guard is true and `p = (i,j)`.
  by_cases hlt : i.1 < j.1
  · have hEq : p = (i, j) := by
      have : some (i, j) = some p := by
        simpa [hlt] using hjp
      simpa using (Option.some.inj this).symm
    simpa [hEq] using hlt
  · -- If the guard is false, the filterMap output is `none`, contradiction with `= some p`.
    have hjp' := hjp
    simp [hlt] at hjp'
    -- `simp` closes the goal using the contradiction.

private theorem inferBondSetsAux_accValid {n : Nat} (atoms : Fin n → Atom)
    (pairs : List (Fin n × Fin n)) (orders : List BondType)
    (maxEdges : Nat) (acc : Finset (BondEdge n))
    (hPairs : ∀ p, p ∈ pairs → p.1.1 < p.2.1)
    (hAcc : AccValid (n := n) acc) :
    ∀ s, s ∈ inferBondSetsAux atoms pairs orders maxEdges acc → AccValid (n := n) s := by
  induction pairs generalizing acc with
  | nil =>
      intro s hs
      simp [inferBondSetsAux] at hs
      cases hs
      simpa using hAcc
  | cons head tail ih =>
      rcases head with ⟨i, j⟩
      have hHead : i.1 < j.1 := hPairs (i, j) (by simp)
      have hTail : ∀ p, p ∈ tail → p.1.1 < p.2.1 := by
        intro p hp
        exact hPairs p (by simp [hp])
      have hSkip : ∀ s, s ∈ inferBondSetsAux atoms tail orders maxEdges acc → AccValid (n := n) s :=
        ih (acc := acc) hTail hAcc
      -- Split on the `maxEdges` guard.
      by_cases hmax : acc.card = maxEdges
      · intro s hs
        -- In this branch, the result list is exactly `skip`.
        have hs' : s ∈ inferBondSetsAux atoms tail orders maxEdges acc := by
          simpa [inferBondSetsAux, hmax] using hs
        exact hSkip s hs'
      · intro s hs
        -- Here we have `skip ++ flatMap addOne orders`.
        have hs' :
            s ∈
              (inferBondSetsAux atoms tail orders maxEdges acc ++
                List.flatMap
                  (fun ty : BondType =>
                    let acc' := insert (mkEdge i j ty) acc
                    let g' : BondGraph n := { atoms := atoms, bonds := acc' }
                    if decide (BondGraph.CovalentValenceOk g') then
                      inferBondSetsAux atoms tail orders maxEdges acc'
                    else
                      [])
                  orders) := by
          simpa [inferBondSetsAux, hmax] using hs
        rcases List.mem_append.1 hs' with hsSkip | hsAdd
        · exact hSkip s hsSkip
        · -- `s` comes from an `addOne` branch.
          rcases List.mem_flatMap.1 hsAdd with ⟨ty, hty, hsTy⟩
          let acc' : Finset (BondEdge n) := insert (mkEdge i j ty) acc
          let g' : BondGraph n := { atoms := atoms, bonds := acc' }
          have hij : i ≠ j := by
            intro hEq
            have hVal : i.1 = j.1 := congrArg Fin.val hEq
            exact (ne_of_lt hHead) hVal
          have hNewTy : (mkEdge i j ty).i ≠ (mkEdge i j ty).j := by
            simpa [mkEdge] using hij
          have hAcc' : AccValid (n := n) acc' :=
            accValid_insert (n := n) (hAcc := hAcc) (hNew := hNewTy)
          -- `hsTy` is membership in an `if`; split on whether the constraint holds.
          by_cases hdec : BondGraph.CovalentValenceOk g'
          · have hsRec : s ∈ inferBondSetsAux atoms tail orders maxEdges acc' := by
              have hsTy' := hsTy
              simp [acc', g', hdec] at hsTy'
              exact hsTy'
            exact ih (acc := acc') hTail hAcc' s hsRec
          · have hsTy' := hsTy
            simp [acc', g', hdec] at hsTy'
            -- `simp` closes the goal using the contradiction.

theorem inferBondGraphs_valid {n : Nat} (atoms : Fin n → Atom) (maxEdges maxOrder : Nat)
    (g : BondGraph n) (hg : g ∈ inferBondGraphs atoms maxEdges maxOrder) :
    BondGraph.Valid g := by
  -- Peel off the final filter; validity holds for all candidates before filtering.
  have hfilter := List.mem_filter.1 hg
  -- `g` is in the `sets.map` image.
  -- `inferBondGraphs` definition:
  --   graphs := sets.map (fun bonds => {atoms, bonds})
  --   return graphs.filter ...
  unfold inferBondGraphs at hfilter
  -- Reconstruct the originating bond set.
  set orders := covalentOrdersUpTo maxOrder
  set pairs := allPairs n
  set sets := inferBondSetsAux atoms pairs orders maxEdges (∅)
  set graphs := sets.map (fun bonds => ({ atoms := atoms, bonds := bonds } : BondGraph n))
  have hgInGraphs : g ∈ graphs := hfilter.1
  rcases List.mem_map.1 hgInGraphs with ⟨bonds, hbonds, rfl⟩
  -- Show the bond set is accumulator-valid, hence the graph is `BondGraph.Valid`.
  have hPairs : ∀ p, p ∈ pairs → p.1.1 < p.2.1 := by
    intro p hp
    exact mem_allPairs_lt (n := n) (p := p) hp
  have hSets : ∀ s, s ∈ sets → AccValid (n := n) s :=
    inferBondSetsAux_accValid (n := n) atoms pairs orders maxEdges (∅) hPairs (accValid_empty (n := n))
  have hAccValidBonds : AccValid (n := n) bonds := hSets bonds hbonds
  intro e he
  exact hAccValidBonds e he

theorem inferBondGraphs_sound {n : Nat} (atoms : Fin n → Atom) (maxEdges maxOrder : Nat)
    (g : BondGraph n) (hg : g ∈ inferBondGraphs atoms maxEdges maxOrder) :
    BondGraph.CovalentValenceOk g ∧ BondGraph.NoIsolatedCovalent g := by
  have hfilter := List.mem_filter.1 hg
  have h : BondGraph.CovalentValenceOk g ∧ BondGraph.NoIsolatedCovalent g ∧ BondGraph.CovalentValenceSaturated g :=
    of_decide_eq_true hfilter.2
  exact ⟨h.1, h.2.1⟩

end Bonding
end Chem
end HeytingLean
