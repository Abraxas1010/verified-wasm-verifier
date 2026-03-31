import HeytingLean.Physics.SpinGlass.Model

/-
# Phase labelling and EA-plane boundary geometry

This module provides a minimal, spec-level representation of phase
labels on the Edwards–Anderson (EA) plane and simple combinators for
extracting and classifying FM/non-FM boundaries.

It is designed for use by the Chaos & Reentrance lens and the
`verify_chaos` executable: numerical simulators or empirical studies
produce an `EAPlaneGrid`, and Lean predicates here inspect the
resulting boundaries to detect vertical vs reentrant behaviour.
-/

namespace HeytingLean
namespace Physics
namespace SpinGlass

open SpinGlass

/-- Coarse phase labels for EA-plane grids. -/
inductive Phase
  | Para   -- paramagnetic
  | FM     -- ferromagnetic
  | SG     -- spin-glass
  | Mixed  -- mixed / other (catch-all)
  deriving DecidableEq, Repr

/-- A rectangular grid of phase labels over the EA plane.

`betaVals` enumerate the β-axis (temperature),
`betapVals` enumerate the βp-axis (disorder),
and `labels[j][i]` (if present) is the phase at `(βp_j, β_i)`.

The invariants relating sizes are enforced by consumers; this type is
intentionally lightweight to match JSON reports. -/
structure EAPlaneGrid where
  betaVals  : List ℝ
  betapVals : List ℝ
  labels    : Array (Array Phase)

namespace EAPlaneGrid

/-- Number of β samples in the grid. -/
def betaCount (g : EAPlaneGrid) : Nat :=
  g.betaVals.length

/-- Number of βp samples in the grid (rows). -/
def betapCount (g : EAPlaneGrid) : Nat :=
  g.betapVals.length

/-- Safe accessor for the phase at row `j` (βp index) and column `i` (β index). -/
def phaseAt? (g : EAPlaneGrid) (j i : Nat) : Option Phase := do
  let row ← g.labels[j]?
  row[i]?

/-- Phase at row `j` interpreted at the β value `β_i`, if present. -/
def phaseAtBeta? (g : EAPlaneGrid) (j : Nat) (i : Nat) : Option (ℝ × Phase) := do
  let β ← g.betaVals[i]?
  let ph ← g.phaseAt? j i
  pure (β, ph)

end EAPlaneGrid

/-- A 1D sample of a phase boundary as a function of β. -/
structure BoundarySample where
  beta  : ℝ
  phase : Phase

/-- Extract the FM / non-FM boundary for a fixed βp row, returning
the smallest β at which the phase ceases to be ferromagnetic and its
new phase label, if any.

This is a simple left-to-right scan along the β-axis. If the row
contains only FM (or is empty / ill-formed), the result is `none`. -/
def fmBoundaryAt (g : EAPlaneGrid) (betapIndex : Nat) : Option BoundarySample := Id.run do
  let mut idx : Nat := 0
  let n := g.betaVals.length
  while idx < n do
    match g.phaseAtBeta? betapIndex idx with
    | some (β, ph) =>
        if ph ≠ Phase.FM then
          return some { beta := β, phase := ph }
        else
          idx := idx + 1
    | none =>
        -- malformed row; abort
        return none
  return none

/-- Discrete FM / non-FM boundary curve obtained by scanning each βp row
and collecting the first non-FM phase transition (if any). -/
def FMBoundary (g : EAPlaneGrid) : List BoundarySample :=
  let rows := List.range g.betapVals.length
  rows.foldl
    (fun acc j =>
      match fmBoundaryAt g j with
      | some s => acc ++ [s]
      | none   => acc)
    []

/-- A boundary is *approximately vertical* if, up to a given tolerance,
all sampled β-values are equal. This is a coarse, purely geometric
predicate used for qualitative checks; it does not attempt to
quantify finite-size effects. -/
def VerticalBoundary (tol : ℝ) (samples : List BoundarySample) : Prop :=
  match samples with
  | [] => True
  | s₀ :: ss =>
      ∀ s ∈ ss, |s.beta - s₀.beta| ≤ tol

/-- A boundary is *approximately horizontal* if, up to a given tolerance,
all sampled β-values are near the extremal values `β_min` or `β_max`
of the grid. This is a coarse predicate; the concrete thresholds should
be tuned by the caller. -/
def HorizontalBoundary (g : EAPlaneGrid) (tol : ℝ) (samples : List BoundarySample) : Prop :=
  match g.betaVals with
  | [] => True
  | βmin :: _ =>
      let βmax := g.betaVals.foldl (fun acc b => if b > acc then b else acc) βmin
      ∀ s ∈ samples, (|s.beta - βmin| ≤ tol) ∨ (|s.beta - βmax| ≤ tol)

/-- A reentrant EA boundary exhibits an FM → non-FM → FM pattern as β
increases. Given a discrete list of `(β, phase)` samples, we say it is
reentrant if there exist indices `i < j < k` such that:

* at `i` the phase is ferromagnetic,
* at `j` the phase is not ferromagnetic,
* at `k` the phase is ferromagnetic again, and
* `beta_i < beta_j < beta_k`.

This is deliberately coarse: it is designed to detect the qualitative
pattern observed in the EA-plane diagrams. -/
def ReentrantEA (curve : List BoundarySample) : Prop :=
  ∃ (i j k : Nat)
    (hi : i < curve.length) (hj : j < curve.length) (hk : k < curve.length),
    i < j ∧ j < k ∧
    let si := curve.get ⟨i, hi⟩
    let sj := curve.get ⟨j, hj⟩
    let sk := curve.get ⟨k, hk⟩
    si.phase = Phase.FM ∧
    sj.phase ≠ Phase.FM ∧
    sk.phase = Phase.FM ∧
    si.beta < sj.beta ∧ sj.beta < sk.beta

/-- Convenience: treat the FM boundary of a grid as a reentrant EA boundary
exactly when its discrete samples exhibit the reentrant pattern. -/
def GridReentrantEA (g : EAPlaneGrid) : Prop :=
  ReentrantEA (FMBoundary g)

/-! ### Synthetic sanity examples (spec-level only) -/

namespace Examples

/-- A simple vertical boundary with no reentrance: all rows transition
from FM to SG at the same β. -/
def verticalExample : EAPlaneGrid :=
  { betaVals  := [0.5, 1.0, 1.5]
    betapVals := [0.1, 0.2]
    labels    := #[
      #[Phase.FM, Phase.FM, Phase.SG],
      #[Phase.FM, Phase.FM, Phase.SG]
    ] }

/-- Boundary samples for the synthetic vertical example. -/
def verticalBoundarySamples : List BoundarySample :=
  FMBoundary verticalExample

-- In the vertical example, the FM boundary is expected to be approximately
-- vertical with small tolerance; we do not prove this here, since the
-- Chaos lens only relies on the predicates, not on this particular finite instance.


end Examples

end SpinGlass
end Physics
end HeytingLean
