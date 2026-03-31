import HeytingLean.Topology.Knot.Jones

/-!
# Knot theory: Conway-style skein evaluator (executable)

This module adds an oriented-skein layer over `SignedPDGraph`:

- local operators `lPlusAt`, `lMinusAt`, `lZeroLast`,
- an executable polynomial evaluator `conwayWithFuel`,
- theorem-level local step law for the evaluator.

The polynomial target is `LaurentPoly` to keep the evaluator executable.
-/

namespace HeytingLean
namespace Topology
namespace Knot

open Std

namespace Kauffman

abbrev ConwayPoly := LaurentPoly

/-- Skein variable `z`. -/
def z : ConwayPoly := LaurentPoly.mon 1 1

namespace SignedPDGraph

/-- Internal helper: validate and return the same signed graph. -/
private def ensureValid (s : SignedPDGraph) : Except String SignedPDGraph := do
  validate s
  return s

/-- Set the sign kind at crossing index `idx`. -/
def setSignAt (s : SignedPDGraph) (idx : Nat) (kind : Reidemeister.CurlKind) :
    Except String SignedPDGraph := do
  validate s
  if idx < s.sign.size then
    ensureValid { s with sign := s.sign.set! idx kind }
  else
    throw s!"setSignAt: idx={idx} out of bounds (size={s.sign.size})"

/-- Force `L+` at crossing `idx`. -/
def lPlusAt (s : SignedPDGraph) (idx : Nat) : Except String SignedPDGraph :=
  setSignAt s idx .pos

/-- Force `L-` at crossing `idx`. -/
def lMinusAt (s : SignedPDGraph) (idx : Nat) : Except String SignedPDGraph :=
  setSignAt s idx .neg

/-- Last crossing index, if it exists. -/
def lastCrossing? (s : SignedPDGraph) : Option Nat :=
  if s.graph.n = 0 then none else some (s.graph.n - 1)

/-- Force `L+` at the last crossing. -/
def lPlusLast (s : SignedPDGraph) : Except String SignedPDGraph := do
  match s.lastCrossing? with
  | some idx => lPlusAt s idx
  | none => throw "lPlusLast: no crossings"

/-- Force `L-` at the last crossing. -/
def lMinusLast (s : SignedPDGraph) : Except String SignedPDGraph := do
  match s.lastCrossing? with
  | some idx => lMinusAt s idx
  | none => throw "lMinusLast: no crossings"

private def smoothLastCore! (freeLoops : Nat) (n : Nat) (arcNbr : Array Nat) :
    (Nat × Array Nat) := Id.run do
  -- Precondition: `n > 0` and `arcNbr` is a valid involution of length `4*n`.
  let m := 4 * n
  let base := m - 4

  -- Deterministic oriented smoothing proxy: use existing A-smoothing wiring.
  let smooth (idx : Nat) : Nat :=
    let pos := idx % 4
    match pos with
    | 0 => base + 1
    | 1 => base + 0
    | 2 => base + 3
    | _ => base + 2

  let isRemoved (idx : Nat) : Bool :=
    idx >= base

  let exitFromExternal (x : Nat) : Nat := Id.run do
    let mut r := arcNbr[x]!
    for _ in [0:4] do
      let r' := smooth r
      let y := arcNbr[r']!
      if y < base then
        return y
      r := y
    return x

  -- Count new free loops created entirely inside the removed region.
  let mut visited : Array Bool := Array.replicate 4 false
  let mut deltaLoops := 0
  for off in [0:4] do
    if !visited[off]! then
      let start := base + off
      let mut stack : List Nat := [start]
      let mut touchesExternal := false
      while !stack.isEmpty do
        match stack with
        | [] => pure ()
        | v :: rest => do
            stack := rest
            if isRemoved v then
              let vOff := v - base
              if vOff < 4 && !visited[vOff]! then
                visited := visited.set! vOff true
                let a := arcNbr[v]!
                if a < base then
                  touchesExternal := true
                else
                  stack := a :: stack
                let s := smooth v
                stack := s :: stack
            pure ()
      if !touchesExternal then
        deltaLoops := deltaLoops + 1

  -- Rewire external endpoints that used to connect to the removed region.
  let mut newNbr : Array Nat := arcNbr.take base
  for x in [0:base] do
    let p := arcNbr[x]!
    if isRemoved p then
      let y := exitFromExternal x
      newNbr := newNbr.set! x y
      newNbr := newNbr.set! y x

  return (freeLoops + deltaLoops, newNbr)

/-- `L0` at the last crossing (crossing count decreases by one). -/
def lZeroLast (s : SignedPDGraph) : Except String SignedPDGraph := do
  validate s
  if s.graph.n = 0 then
    throw "lZeroLast: no crossings"
  else
    let (free', nbr') := smoothLastCore! s.graph.freeLoops s.graph.n s.graph.arcNbr
    let g' : PDGraph := { freeLoops := free', n := s.graph.n - 1, arcNbr := nbr' }
    let sign' := s.sign.extract 0 (s.sign.size - 1)
    ensureValid { graph := g', sign := sign' }

private def permuteCrossingToLast (s : SignedPDGraph) (idx : Nat) : Except String SignedPDGraph := do
  validate s
  if s.graph.n = 0 then
    throw "permuteCrossingToLast: no crossings"
  if idx >= s.graph.n then
    throw s!"permuteCrossingToLast: idx={idx} out of bounds (n={s.graph.n})"
  let last := s.graph.n - 1
  if idx = last then
    return s
  let swapHalfEdge (x : Nat) : Nat :=
    let b := x / 4
    let off := x % 4
    if b = idx then
      4 * last + off
    else if b = last then
      4 * idx + off
    else
      x
  let m := s.graph.arcNbr.size
  let mut nbr' : Array Nat := Array.replicate m 0
  for x in [0:m] do
    nbr' := nbr'.set! (swapHalfEdge x) (swapHalfEdge (s.graph.arcNbr[x]!))
  let signIdx := s.sign[idx]!
  let signLast := s.sign[last]!
  let sign' := (s.sign.set! idx signLast).set! last signIdx
  ensureValid { graph := { s.graph with arcNbr := nbr' }, sign := sign' }

/-- `L0` at crossing `idx` (implemented by permuting the target crossing to the last-crossing path). -/
def lZeroAt (s : SignedPDGraph) (idx : Nat) : Except String SignedPDGraph := do
  let sp ← permuteCrossingToLast s idx
  lZeroLast sp

/-- Base Conway value on crossing-free states. -/
def conwayBase (s : SignedPDGraph) : ConwayPoly :=
  -- `PDGraph.freeLoops` counts components that are disjoint from crossings.
  -- For braid-closure inputs this can be `0` even when the crossing-free result is a single component.
  if s.graph.freeLoops = 0 || s.graph.freeLoops = 1 then 1 else 0

/--
Fuel-bounded local Conway evaluator.

Branching rule at the last crossing:
- if last sign is `neg`, evaluate the `L0` branch;
- if last sign is `pos`, evaluate `L- + z*L0`.
-/
def conwayWithFuel : Nat → SignedPDGraph → Except String ConwayPoly
  | 0, _ => .error "conwayWithFuel: fuel exhausted"
  | fuel + 1, s => do
      validate s
      if s.graph.n = 0 then
        pure (conwayBase s)
      else
        let last := s.graph.n - 1
        let s0 ← lZeroLast s
        let p0 ← conwayWithFuel fuel s0
        match s.sign[last]! with
        | .neg =>
            pure p0
        | .pos =>
            let sm ← lMinusLast s
            let pm ← conwayWithFuel fuel sm
            pure (pm + z * p0)

/-- Deterministic budget used by `conway`. -/
def conwayBudget (s : SignedPDGraph) : Nat :=
  2 * s.graph.n + 1

/-- Executable Conway evaluator. -/
def conway (s : SignedPDGraph) : Except String ConwayPoly :=
  conwayWithFuel (conwayBudget s) s

/-- Definitional unfold lemma for one fuel step. -/
theorem conwayWithFuel_unfold_succ (fuel : Nat) (sp : SignedPDGraph) :
    conwayWithFuel (fuel + 1) sp =
      (do
        validate sp
        if sp.graph.n = 0 then
          pure (conwayBase sp)
        else
          let last := sp.graph.n - 1
          let s0 ← lZeroLast sp
          let p0 ← conwayWithFuel fuel s0
          match sp.sign[last]! with
          | .neg => pure p0
          | .pos =>
              let sm ← lMinusLast sp
              let pm ← conwayWithFuel fuel sm
              pure (pm + z * p0)) := rfl

/-- If `ensureValid` succeeds, the output graph validates. -/
private theorem ensureValid_validate_ok_of_ok {s t : SignedPDGraph}
    (h : ensureValid s = .ok t) :
    validate t = .ok () := by
  unfold ensureValid at h
  cases hValidate : validate s with
  | error _ =>
      simp [hValidate] at h
      cases h
  | ok u =>
      cases u
      simp [hValidate] at h
      cases h
      simp [hValidate]

/-- If `setSignAt` succeeds, the output is validated. -/
theorem setSignAt_validate_ok_of_ok {s t : SignedPDGraph} {idx : Nat}
    {kind : Reidemeister.CurlKind}
    (h : setSignAt s idx kind = .ok t) :
    validate t = .ok () := by
  unfold setSignAt at h
  cases hValidate : validate s with
  | error _ =>
      simp [hValidate] at h
      cases h
  | ok u =>
      cases u
      simp [hValidate] at h
      by_cases hIdx : idx < s.sign.size
      · simp [hIdx] at h
        exact ensureValid_validate_ok_of_ok h
      · simp [hIdx] at h
        cases h

/-- If `lPlusAt` succeeds, the output is validated. -/
theorem lPlusAt_validate_ok_of_ok {s t : SignedPDGraph} {idx : Nat}
    (h : lPlusAt s idx = .ok t) :
    validate t = .ok () := by
  unfold lPlusAt at h
  exact setSignAt_validate_ok_of_ok h

/-- If `lMinusAt` succeeds, the output is validated. -/
theorem lMinusAt_validate_ok_of_ok {s t : SignedPDGraph} {idx : Nat}
    (h : lMinusAt s idx = .ok t) :
    validate t = .ok () := by
  unfold lMinusAt at h
  exact setSignAt_validate_ok_of_ok h

/-- If `lZeroLast` succeeds, the output is validated. -/
theorem lZeroLast_validate_ok_of_ok {s t : SignedPDGraph}
    (h : lZeroLast s = .ok t) :
    validate t = .ok () := by
  unfold lZeroLast at h
  cases hValidate : validate s with
  | error _ =>
      simp [hValidate] at h
      cases h
  | ok u =>
      cases u
      simp [hValidate] at h
      by_cases hn : s.graph.n = 0
      · simp [hn] at h
        cases h
      · simp [hn] at h
        exact ensureValid_validate_ok_of_ok h

/-- If `lZeroAt` succeeds, the output is validated. -/
theorem lZeroAt_validate_ok_of_ok {s t : SignedPDGraph} {idx : Nat}
    (h : lZeroAt s idx = .ok t) :
    validate t = .ok () := by
  unfold lZeroAt at h
  cases hPerm : permuteCrossingToLast s idx with
  | error _ =>
      simp [hPerm] at h
      cases h
  | ok sp =>
      simp [hPerm] at h
      exact lZeroLast_validate_ok_of_ok h

end SignedPDGraph

end Kauffman

end Knot
end Topology
end HeytingLean
