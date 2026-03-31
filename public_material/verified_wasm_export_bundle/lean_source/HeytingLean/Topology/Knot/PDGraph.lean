import Std
import HeytingLean.Topology.Knot.PlanarDiagram

/-!
# Knot theory: PD graph core (executable)

`PlanarDiagram` is a PD-style input encoding using arc labels. For efficient rewriting and
local moves, it's useful to work in an equivalent **label-free** representation:

- `n` crossings, each contributes 4 half-edges (indices `0 .. 4*n-1`),
- an involution `arcNbr` pairing half-edges into arcs.

This module provides that core representation and basic validation and conversions.
-/

namespace HeytingLean
namespace Topology
namespace Knot

open Std

/-- A label-free PD-style diagram: crossings + an arc-neighbor involution on half-edges. -/
structure PDGraph where
  freeLoops : Nat := 0
  n : Nat := 0
  arcNbr : Array Nat := #[]
deriving Repr, Inhabited

namespace PDGraph

def numHalfEdges (g : PDGraph) : Nat :=
  4 * g.n

/-!
## Logical (Prop-level) well-formedness

`PDGraph.validate` is an executable checker used by all IO-facing code.  For theorem-level
reasoning about constructors (e.g. Reidemeister moves), it is useful to have a Prop-level
predicate describing the same invariants.
-/

/-- Prop-level well-formedness: `arcNbr` is a fixed-point-free involution on half-edges. -/
def Valid (g : PDGraph) : Prop :=
  g.arcNbr.size = g.numHalfEdges ∧
    ∀ i < g.numHalfEdges,
      let j := g.arcNbr[i]!
      j < g.numHalfEdges ∧ j ≠ i ∧ g.arcNbr[j]! = i

namespace Valid

theorem size_eq {g : PDGraph} (hg : Valid g) : g.arcNbr.size = g.numHalfEdges :=
  hg.1

theorem get_lt {g : PDGraph} (hg : Valid g) {i : Nat} (hi : i < g.numHalfEdges) :
    g.arcNbr[i]! < g.numHalfEdges :=
  (hg.2 i hi).1

theorem get_ne {g : PDGraph} (hg : Valid g) {i : Nat} (hi : i < g.numHalfEdges) :
    g.arcNbr[i]! ≠ i :=
  (hg.2 i hi).2.1

theorem invol {g : PDGraph} (hg : Valid g) {i : Nat} (hi : i < g.numHalfEdges) :
    g.arcNbr[g.arcNbr[i]!]! = i :=
  (hg.2 i hi).2.2

end Valid

def validate (g : PDGraph) : Except String Unit :=
  let m := g.numHalfEdges
  if g.arcNbr.size != m then
    .error s!"arcNbr length {g.arcNbr.size} (expected {m})"
  else
    match
      forIn (List.range' 0 m) () (fun i _ =>
        if m ≤ g.arcNbr[i]! then
          Except.error s!"arcNbr[{i}]={g.arcNbr[i]!} out of range (m={m})"
        else if g.arcNbr[i]! = i then
          Except.error s!"arcNbr has a fixed point at {i}"
        else if g.arcNbr[g.arcNbr[i]!]! = i then
          Except.ok (ForInStep.yield ())
        else
          Except.error
            s!"arcNbr not an involution at {i} ↦ {g.arcNbr[i]!} ↦ {g.arcNbr[g.arcNbr[i]!]!}") with
    | .error err => .error err
    | .ok _ => .ok ()

theorem size_eq_numHalfEdges_of_validate_eq_ok
    {g : PDGraph} (h : validate g = .ok ()) : g.arcNbr.size = g.numHalfEdges := by
  classical
  unfold validate at h
  by_cases hsize : g.arcNbr.size = g.numHalfEdges
  · exact hsize
  ·
    -- In the failure branch, `validate` returns an error, contradicting `h`.
    have hsize' : (g.arcNbr.size != g.numHalfEdges) = true := by
      -- `!=` is Boolean inequality, so `¬ size = m` means it is `true`.
      simp [hsize]
    have := h
    simp [hsize'] at this

private theorem forIn_ok_of_all_yield
    {l : List Nat}
    {f : Nat → Unit → Except String (ForInStep Unit)}
    (hf : ∀ i, i ∈ l → f i () = .ok (ForInStep.yield ())) :
    forIn l () f = .ok () := by
  classical
  induction l with
  | nil =>
      simp [Pure.pure, Except.pure]
  | cons a as ih =>
      have hfa : f a () = .ok (ForInStep.yield ()) := hf a (by simp)
      have hftail : ∀ i, i ∈ as → f i () = .ok (ForInStep.yield ()) := by
        intro i hi
        exact hf i (by simp [hi])
      simp [List.forIn_cons, hfa, ih hftail, Bind.bind, Except.bind]

private theorem all_yield_of_forIn_ok
    {l : List Nat}
    {f : Nat → Unit → Except String (ForInStep Unit)}
    (hfDone : ∀ i, i ∈ l → f i () ≠ .ok (ForInStep.done ())) :
    forIn l () f = .ok () →
      ∀ i, i ∈ l → f i () = .ok (ForInStep.yield ()) := by
  classical
  intro h
  induction l with
  | nil =>
      intro i hi
      cases hi
  | cons a as ih =>
      intro i hi
      have hfDoneTail : ∀ j, j ∈ as → f j () ≠ .ok (ForInStep.done ()) := by
        intro j hj
        exact hfDone j (by simp [hj])
      have hfa : f a () = .ok (ForInStep.yield ()) := by
        -- Expand `forIn` on `a :: as` and use the fact `f a ()` cannot be `done`.
        cases hfa' : f a () with
        | error e =>
            -- Then `forIn` fails immediately, contradicting `h`.
            have := h
            simp [List.forIn_cons, hfa', Bind.bind, Except.bind] at this
        | ok step =>
            cases step with
            | done r =>
                exfalso
                exact hfDone a (by simp) (by simp [hfa'])
            | yield r =>
                cases r
                rfl
      have htail : forIn as () f = .ok () := by
        cases hfa' : f a () with
        | error e =>
            have := h
            simp [List.forIn_cons, hfa', Bind.bind, Except.bind] at this
        | ok step =>
            cases step with
            | done r =>
                exfalso
                exact hfDone a (by simp) (by simp [hfa'])
            | yield r =>
                have := h
                -- Reduce to the tail.
                simpa [List.forIn_cons, hfa', Bind.bind, Except.bind] using this
      cases hi with
      | head =>
          -- i = a
          simpa using hfa
      | tail _ hiTail =>
          exact ih hfDoneTail htail i hiTail

theorem validate_eq_ok_of_valid {g : PDGraph} (hg : Valid g) : validate g = .ok () := by
  classical
  unfold validate
  have hsize : g.arcNbr.size = g.numHalfEdges := hg.1
  -- Reduce the size guard and rewrite the range loop to a list `forIn`.
  simp [hsize]
  have hloop :
      forIn (List.range' 0 g.numHalfEdges) () (fun i r =>
        if g.numHalfEdges ≤ g.arcNbr[i]! then
          Except.error
            (toString "arcNbr[" ++ toString i ++ toString "]=" ++ toString g.arcNbr[i]! ++
                  toString " out of range (m=" ++
                toString g.numHalfEdges ++
              toString ")")
        else
          if g.arcNbr[i]! = i then Except.error (toString "arcNbr has a fixed point at " ++ toString i)
          else
            if g.arcNbr[g.arcNbr[i]!]! = i then Except.ok (ForInStep.yield ())
            else
              Except.error
                (toString "arcNbr not an involution at " ++ toString i ++ toString " ↦ " ++ toString g.arcNbr[i]! ++
                    toString " ↦ " ++
                  toString g.arcNbr[g.arcNbr[i]!]!)) = .ok () := by
    apply forIn_ok_of_all_yield
    intro i hi
    have hi_lt : i < g.numHalfEdges := by
      rcases (List.mem_range'.1 hi) with ⟨k, hk, hkEq⟩
      -- For `range' 0 m`, `i = k`.
      simpa [hkEq] using hk
    have hj_lt : g.arcNbr[i]! < g.numHalfEdges := Valid.get_lt hg hi_lt
    have hj_ne : g.arcNbr[i]! ≠ i := Valid.get_ne hg hi_lt
    have hj_inv : g.arcNbr[g.arcNbr[i]!]! = i := Valid.invol hg hi_lt
    have hm_not_le : ¬ g.numHalfEdges ≤ g.arcNbr[i]! := Nat.not_le_of_gt hj_lt
    simp [hm_not_le, hj_ne, hj_inv]
  -- Rewrite the loop result and close the remaining `match`.
  simp [hloop]

theorem valid_of_validate_eq_ok {g : PDGraph} (h : validate g = .ok ()) : Valid g := by
  classical
  -- Extract the size invariant from the initial guard.
  have hsize : g.arcNbr.size = g.numHalfEdges := size_eq_numHalfEdges_of_validate_eq_ok (g := g) h
  refine ⟨hsize, ?_⟩
  intro i hi
  -- Unfold `validate` and isolate the range loop.
  unfold validate at h
  let f : Nat → Unit → Except String (ForInStep Unit) :=
    fun i _ =>
      if g.numHalfEdges ≤ g.arcNbr[i]! then
        Except.error
          (toString "arcNbr[" ++ toString i ++ toString "]=" ++ toString g.arcNbr[i]! ++
                toString " out of range (m=" ++
              toString g.numHalfEdges ++
            toString ")")
      else if g.arcNbr[i]! = i then
        Except.error (toString "arcNbr has a fixed point at " ++ toString i)
      else if g.arcNbr[g.arcNbr[i]!]! = i then
        Except.ok (ForInStep.yield ())
      else
        Except.error
          (toString "arcNbr not an involution at " ++ toString i ++ toString " ↦ " ++ toString g.arcNbr[i]! ++
              toString " ↦ " ++
            toString g.arcNbr[g.arcNbr[i]!]!)

  have hloop' :
      (match forIn (List.range' 0 g.numHalfEdges) () f with
        | Except.error err => Except.error err
        | Except.ok _ => Except.ok ()) = .ok () := by
    -- Convert `validate = ok` into a statement about the internal `forIn`.
    have h' := h
    simp [hsize] at h'
    simpa [f] using h'

  have hloop : forIn (List.range' 0 g.numHalfEdges) () f = .ok () := by
    cases hfor : forIn (List.range' 0 g.numHalfEdges) () f with
    | error err =>
        have hcontra := hloop'
        simp [hfor] at hcontra
    | ok r =>
        cases r
        rfl

  -- The loop body never returns `done`, only `yield` or `error`.
  have hfDone :
      ∀ j, j ∈ (List.range' 0 g.numHalfEdges) → f j () ≠ .ok (ForInStep.done ()) := by
    intro j hj
    by_cases h1 : g.numHalfEdges ≤ g.arcNbr[j]!
    · simp [f, h1]
    ·
      by_cases h2 : g.arcNbr[j]! = j
      ·
        have h1' : ¬ g.numHalfEdges ≤ j := by
          simpa [h2] using h1
        simp [f, h1', h2]
      ·
        by_cases h3 : g.arcNbr[g.arcNbr[j]!]! = j
        · simp [f, h1, h2, h3]
        · simp [f, h1, h2, h3]

  have hyield :=
    all_yield_of_forIn_ok (l := List.range' 0 g.numHalfEdges) (f := f) hfDone hloop

  have hi_mem : i ∈ List.range' 0 g.numHalfEdges := by
    apply List.mem_range'.mpr
    refine ⟨i, hi, ?_⟩
    simp
  have hi_step : f i () = .ok (ForInStep.yield ()) := hyield i hi_mem

  -- Analyze the loop body's success at `i`.
  have hj_lt : g.arcNbr[i]! < g.numHalfEdges := by
    by_cases hj_ge' : g.numHalfEdges ≤ g.arcNbr[i]!
    ·
      have hfi : f i () = .error
          (toString "arcNbr[" ++ toString i ++ toString "]=" ++ toString g.arcNbr[i]! ++
                toString " out of range (m=" ++
              toString g.numHalfEdges ++
            toString ")") := by
        simp [f, hj_ge']
      have hi_step' := hi_step
      rw [hfi] at hi_step'
      cases hi_step'
    · exact Nat.lt_of_not_ge hj_ge'
  have hj_ne : g.arcNbr[i]! ≠ i := by
    by_cases hj_eq : g.arcNbr[i]! = i
    ·
      have hm_not_le : ¬ g.numHalfEdges ≤ g.arcNbr[i]! := Nat.not_le_of_gt hj_lt
      have hm_not_le' : ¬ g.numHalfEdges ≤ i := by
        simpa [hj_eq] using hm_not_le
      have hfi : f i () = .error (toString "arcNbr has a fixed point at " ++ toString i) := by
        simp [f, hm_not_le', hj_eq]
      have hi_step' := hi_step
      rw [hfi] at hi_step'
      cases hi_step'
    · exact hj_eq
  have hj_inv : g.arcNbr[g.arcNbr[i]!]! = i := by
    by_cases hj_inv : g.arcNbr[g.arcNbr[i]!]! = i
    · exact hj_inv
    ·
      have hm_not_le : ¬ g.numHalfEdges ≤ g.arcNbr[i]! := Nat.not_le_of_gt hj_lt
      have hfi : f i () = .error
          (toString "arcNbr not an involution at " ++ toString i ++ toString " ↦ " ++ toString g.arcNbr[i]! ++
              toString " ↦ " ++
            toString g.arcNbr[g.arcNbr[i]!]!) := by
        simp [f, hm_not_le, hj_ne, hj_inv]
      have hi_step' := hi_step
      rw [hfi] at hi_step'
      cases hi_step'
  exact ⟨hj_lt, hj_ne, hj_inv⟩

/-- Convert a `PlanarDiagram` (labelled PD encoding) into a `PDGraph` (label-free). -/
def ofPlanarDiagram (d : PlanarDiagram) : Except String PDGraph := do
  let arcNbr ← PlanarDiagram.buildArcNeighbor d
  return { freeLoops := d.freeLoops, n := d.numCrossings, arcNbr }

/-- Convert a `PDGraph` back into a canonical `PlanarDiagram` by assigning fresh labels
to each arc-pair. -/
def toPlanarDiagram (g : PDGraph) : Except String PlanarDiagram := do
  validate g
  let m := g.numHalfEdges
  if m = 0 then
    return { freeLoops := g.freeLoops, crossings := #[] }

  let mut labels : Array (Option Nat) := Array.replicate m none
  let mut nextLbl : Nat := 0
  for i in [0:m] do
    if labels[i]!.isNone then
      let j := g.arcNbr[i]!
      labels := labels.set! i (some nextLbl)
      labels := labels.set! j (some nextLbl)
      nextLbl := nextLbl + 1

  let mut cs : Array Crossing := Array.replicate g.n default
  for k in [0:g.n] do
    let base := 4 * k
    let a := (labels[base + 0]!).getD 0
    let b := (labels[base + 1]!).getD 0
    let c := (labels[base + 2]!).getD 0
    let d := (labels[base + 3]!).getD 0
    cs := cs.set! k { a, b, c, d }
  return { freeLoops := g.freeLoops, crossings := cs }

end PDGraph

end Knot
end Topology
end HeytingLean
