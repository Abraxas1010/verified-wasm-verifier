import Mathlib.Data.Real.Basic
import HeytingLean.Quantum.VacuumOmegaR
import HeytingLean.Quantum.QGIContext

/-!
# Symbolic Diósi–Penrose-style gravitational collapse model

This module encodes a *symbolic* version of the Diósi–Penrose
gravitational collapse picture around the existing `VacuumOmegaRContext`.

Design notes:
- Numeric constants are treated parametrically via a `PhysParams` record;
  no specific numerical values are relied on.
- The predicates here are deliberately simple and do not attempt to give
  a physically complete account of gravitational decoherence.
- No results in this file are used to prove the vacuum ↔ Ωᴿ equivalence
  or any LoF/Epistemic theorem; the dependency flows only outward.
-/

namespace HeytingLean
namespace Quantum
namespace GravitationalCollapse

open HeytingLean
open HeytingLean.Quantum
open HeytingLean.Quantum.QGIContext
open Quantum.OML.QGIInterferometer
open Set

/-- Symbolic physical parameters used in the collapse model. -/
structure PhysParams where
  hbar  : ℝ
  G     : ℝ

/- Symbolic gravitational self-energy of a simple two-branch spatial
    superposition, approximated as `G m² / d` when the separation `d` is
    non-zero, and `0` when `d = 0`. -/
noncomputable def gravitationalSelfEnergy
    (P : PhysParams) (mass separation : ℝ) : ℝ :=
  if separation = 0 then
    0
  else
    P.G * mass^2 / separation

/-- Penrose-style collapse timescale `τ ≈ ħ / ΔE`. We treat the
    `ΔE = 0` case as a degenerate branch with value `0`; for qualitative
    reasoning we separately expose stability predicates that can take
    the zero-energy case into account. -/
noncomputable def penroseCollapseTime (P : PhysParams) (ΔE : ℝ) : ℝ :=
  if ΔE = 0 then 0 else P.hbar / ΔE

/-- A simple predicate that says a superposition with a given mass,
    separation and duration is “stable” if either:
    * the mass is zero (vacuum-like situation), or
    * the duration is at most the collapse time. -/
def SuperpositionStable (P : PhysParams)
    (mass separation duration : ℝ) : Prop :=
  mass = 0 ∨
    duration ≤ penroseCollapseTime P (gravitationalSelfEnergy P mass separation)

/-- A vacuum-stability predicate that specialises `SuperpositionStable`
    to the zero-mass, zero-separation case. -/
def VacuumStable (P : PhysParams) (duration : ℝ) : Prop :=
  SuperpositionStable P 0 0 duration

/-- In the simplified narrative, the vacuum (zero mass, zero separation)
    is stable for all durations, independently of the concrete parameter
    values. -/
lemma vacuum_no_collapse
    {β : Type u} {α : Type v}
    [Quantum.OML.OrthocomplementedLattice β]
    [Quantum.OML.OrthomodularLattice β]
    [LoF.PrimaryAlgebra α]
    (C : VacuumOmegaRContext β α)
    (P : PhysParams) (t : ℝ) :
    VacuumStable P t := by
  let _ := C
  unfold VacuumStable SuperpositionStable
  -- zero-mass branch witnesses stability
  left
  rfl

/-- A purely order-theoretic “collapse step” that, in one application,
    sends any ambient configuration in `α` to something below the Euler
    boundary of a given `VacuumOmegaRContext`.

This is intentionally abstract: it does not prescribe how the step is
computed, only that its image lies inside the Euler-boundary basin.
Downstream models can relate this step to a concrete
`SuperpositionStable`/Penrose-style dynamics. -/
structure CollapseToEuler
    {β : Type u} {α : Type v}
    [Quantum.OML.OrthocomplementedLattice β]
    [Quantum.OML.OrthomodularLattice β]
    [LoF.PrimaryAlgebra α]
    (C : VacuumOmegaRContext β α) where
  /-- One-step collapse map on the ambient carrier. -/
  step : α → α
  /-- Single-step collapse always lands below the Euler boundary. -/
  step_le_euler : ∀ a, step a ≤ C.R.eulerBoundary

namespace CollapseToEuler

variable {β : Type u} {α : Type v}
variable [Quantum.OML.OrthocomplementedLattice β]
variable [Quantum.OML.OrthomodularLattice β]
variable [LoF.PrimaryAlgebra α]
variable {C : VacuumOmegaRContext β α}

/-- Iterate a collapse step `n` times starting from `a`. For `n = 0`
    this returns `a` itself; for `n = n.succ` it applies `step` to the
    result of the previous iterate. -/
def iterate (M : CollapseToEuler (C := C)) : ℕ → α → α
  | 0, a => a
  | Nat.succ n, a => M.step (M.iterate n a)

/-- Any iterate of length at least one lies below the Euler boundary. -/
lemma iterate_succ_le_euler
    (M : CollapseToEuler (C := C)) (n : ℕ) (a : α) :
    M.iterate (Nat.succ n) a ≤ C.R.eulerBoundary := by
  -- For `n = 0`, a single application of `step` suffices.
  cases n with
  | zero =>
      -- `iterate 1 a = step a`.
      simpa [iterate] using M.step_le_euler a
  | succ n' =>
      -- `iterate (n'.succ.succ) a = step (iterate (n'.succ) a)`.
      have h := M.step_le_euler (M.iterate (Nat.succ n') a)
      simpa [iterate] using h

end CollapseToEuler

/-- Generic constructor: build a `CollapseToEuler` step from any predicate
    `p` on the ambient carrier by sending states that satisfy `p` straight
    to the Euler boundary and all others to bottom. This is intentionally
    coarse but convenient for small, explicitly worked examples. -/
noncomputable def collapseIf
    {β : Type u} {α : Type v}
    [Quantum.OML.OrthocomplementedLattice β]
    [Quantum.OML.OrthomodularLattice β]
    [LoF.PrimaryAlgebra α]
    (C : VacuumOmegaRContext β α) (p : α → Prop) :
    CollapseToEuler (C := C) := by
  classical
  refine
    { step := fun a : α =>
        if h : p a then
          C.R.eulerBoundary
        else
          ⊥
      step_le_euler := ?_ }
  intro a
  by_cases h : p a
  · -- `step a` is exactly the Euler boundary.
    simp [h]
  · -- `step a` is bottom, which lies below the Euler boundary.
    simp [h]

/-- A maximally simple `CollapseToEuler` instance for the QGI base context:

In one step it sends every ambient configuration to the Euler boundary
of `qgiBaseContext.R`. This is intentionally extreme (a “one-shot
collapse”), but it witnesses the idea that the Euler boundary plays the
role of an attractor for a collapse-like dynamics. More refined models
can later interpolate between `a` and `eulerBoundary` instead of
jumping directly. -/
noncomputable def qgiCollapseToEuler :
    CollapseToEuler (C := QGIContext.qgiBaseContext) :=
  { step := fun _ => QGIContext.qgiBaseContext.R.eulerBoundary
    step_le_euler := by
      intro a
      -- the constant step is definitionally equal to `eulerBoundary`,
      -- hence ≤ itself.
      simp }

/-- A softer `CollapseToEuler` instance for the QGI base context.

In one step it collapses only those ambient configurations that mention
either QGI arm (`labPath` or `freePath`) onto the Euler boundary; other
sets are sent to bottom. This remains purely order-theoretic (every
step result lies below the Euler boundary) while behaving less
aggressively than `qgiCollapseToEuler`. -/
noncomputable def qgiCollapseToEulerSoft :
    CollapseToEuler (C := QGIContext.qgiBaseContext) :=
  collapseIf (C := QGIContext.qgiBaseContext)
    (p := fun s : Set QGIContext.β =>
      labPath ∈ s ∨ freePath ∈ s)

/-- A more structured collapse dynamics around a given `VacuumOmegaRContext`.

`CollapseFlow` strengthens `CollapseToEuler` with:
* a monotone collapse step,
* compatibility with the reentry nucleus `C.R`,
* a fixed-point condition at the Euler boundary, and
* strict progress toward the boundary for positive, in-support states
  that are not already at the Euler boundary.

This abstraction is used for convergence and attractor theorems; it does
not alter any of the core Ωᴿ or LoF machinery. -/
structure CollapseFlow
    {β : Type u} {α : Type v}
    [Quantum.OML.OrthocomplementedLattice β]
    [Quantum.OML.OrthomodularLattice β]
    [LoF.PrimaryAlgebra α]
    (C : VacuumOmegaRContext β α) where
  /-- One-step collapse map on the ambient carrier. -/
  step : α → α
  /-- Monotonicity of the collapse step. -/
  monotone_step : Monotone step
  /-- Single-step collapse always lands below one application of the
      reentry nucleus. -/
  step_le_nucleus : ∀ a, step a ≤ C.R a
  /-- The Euler boundary is a fixed point of the collapse flow. -/
  euler_fixed :
    step (((C.R.eulerBoundary : C.R.Omega) : α)) =
      (((C.R.eulerBoundary : C.R.Omega) : α))
  /-- Strict progress toward the Euler boundary inside the support
      window: any positive, in-support state that is not already the
      Euler boundary is strictly decreased by a collapse step. -/
  step_strict :
    ∀ {a : α},
      ⊥ < a → a ≤ C.R.support →
        a ≠ (((C.R.eulerBoundary : C.R.Omega) : α)) →
          step a < a

namespace CollapseFlow

variable {β : Type u} {α : Type v}
variable [Quantum.OML.OrthocomplementedLattice β]
variable [Quantum.OML.OrthomodularLattice β]
variable [LoF.PrimaryAlgebra α]
variable {C : VacuumOmegaRContext β α}

open HeytingLean.Epistemic

/-- Iterate a collapse flow `n` times starting from `a`. For `n = 0`
    this returns `a` itself; for `n = n.succ` it applies `step` to the
    result of the previous iterate. -/
def iterate (M : CollapseFlow (C := C)) : ℕ → α → α
  | 0, a => a
  | Nat.succ n, a => M.step (M.iterate n a)

@[simp] lemma iterate_zero (M : CollapseFlow (C := C)) (a : α) :
    M.iterate 0 a = a := rfl

@[simp] lemma iterate_succ (M : CollapseFlow (C := C)) (n : ℕ) (a : α) :
    M.iterate (Nat.succ n) a = M.step (M.iterate n a) := rfl

/-- Semigroup-style composition law for iterates: iterating `m + n`
    times is the same as iterating `n` times and then `m` times. -/
lemma iterate_add (M : CollapseFlow (C := C)) :
    ∀ m n (a : α),
      M.iterate (m + n) a = M.iterate m (M.iterate n a)
  | 0, n, a => by
      simp [iterate]
  | Nat.succ m, n, a => by
      simp [iterate, iterate_add (M := M) m n a, Nat.succ_add]

/-- For each fixed `n`, `M.iterate n` is a monotone map on the ambient
    carrier. -/
lemma iterate_monotone (M : CollapseFlow (C := C)) :
    ∀ n, Monotone (fun a => M.iterate n a)
  | 0 => by
      intro a b h
      simpa [iterate] using h
  | Nat.succ n =>
      fun a b h => by
        have h' := iterate_monotone (M := M) n h
        have hstep := M.monotone_step h'
        simpa [iterate] using hstep

/-- Bounds along the flow: every iterate stays below a single
    reentry–nucleus application of the starting state. -/
lemma iterate_le_nucleus (M : CollapseFlow (C := C))
    (n : ℕ) (a : α) :
    M.iterate n a ≤ C.R a := by
  induction n with
  | zero =>
      -- `iterate 0 a = a`, and every point lies below its reentry image.
      simp [iterate]
  | succ n ih =>
      -- `iterate (n+1) a = step (iterate n a)` stays below `C.R` of the
      -- previous iterate, which in turn lies below `C.R a`.
      have hstep :
          M.iterate (Nat.succ n) a ≤ C.R (M.iterate n a) := by
        simpa [iterate] using
          M.step_le_nucleus (M.iterate n a)
      have hmono :
          C.R (M.iterate n a) ≤ C.R (C.R a) :=
        (LoF.Reentry.monotone (R := C.R)) ih
      have h := le_trans hstep hmono
      -- Use idempotence to simplify the right-hand side.
      simpa [LoF.Reentry.idempotent] using h

/-- The Euler boundary is a fixed point of the entire flow: every
    iterate returns the Euler boundary. -/
lemma iterate_euler_fixed (M : CollapseFlow (C := C)) (n : ℕ) :
    M.iterate n (((C.R.eulerBoundary : C.R.Omega) : α)) =
      (((C.R.eulerBoundary : C.R.Omega) : α)) := by
  induction n with
  | zero =>
      simp [iterate]
  | succ n ih =>
      rw [iterate_succ]
      rw [ih]
      exact M.euler_fixed

/-- Under the strict-progress hypotheses along an orbit, successive
    iterates form a strictly decreasing chain. This lemma factors out
    the orbit-side conditions so that later convergence theorems can
    supply them as needed. -/
lemma iterate_succ_lt_of_strict (M : CollapseFlow (C := C))
    {a : α}
    (h_pos :
      ∀ n, ⊥ < M.iterate n a)
    (h_sup :
      ∀ n, M.iterate n a ≤ C.R.support)
    (h_ne :
      ∀ n, M.iterate n a ≠ (((C.R.eulerBoundary : C.R.Omega) : α))) :
    ∀ n, M.iterate (Nat.succ n) a < M.iterate n a := by
  intro n
  have hpos := h_pos n
  have hsup := h_sup n
  have hneq := h_ne n
  have h := M.step_strict
    (a := M.iterate n a) hpos hsup hneq
  simpa [iterate] using h

/-- A non-strict variant of `iterate_succ_lt_of_strict` giving a
    decreasing (chain) inequality along the flow. -/
lemma iterate_succ_le_of_strict (M : CollapseFlow (C := C))
    {a : α}
    (h_pos :
      ∀ n, ⊥ < M.iterate n a)
    (h_sup :
      ∀ n, M.iterate n a ≤ C.R.support)
    (h_ne :
      ∀ n, M.iterate n a ≠ (((C.R.eulerBoundary : C.R.Omega) : α))) :
    ∀ n, M.iterate (Nat.succ n) a ≤ M.iterate n a := by
  intro n
  have hlt :=
    iterate_succ_lt_of_strict (M := M) (a := a) h_pos h_sup h_ne n
  exact hlt.le

/-! ### Birth-based finite-time convergence -/

/-- Birth-based ranking assumption for a collapse flow: away from the
Euler boundary (but still inside the support window), a single collapse
step strictly decreases the `birth` index for the underlying reentry
nucleus. This is a model-level property and is not derivable from the
order axioms of `CollapseFlow` alone. -/
def BirthRankingProperty
    (C : VacuumOmegaRContext β α)
    (M : CollapseFlow (C := C)) : Prop :=
  ∀ {a : α},
    ⊥ < a → a ≤ C.R.support →
      a ≠ (((C.R.eulerBoundary : C.R.Omega) : α)) →
        birth C.R (M.step a) < birth C.R a

/-- Uniqueness assumption for the Euler boundary with respect to the
`birth` index: any ambient element with birthday zero must in fact be
the Euler boundary. This is intentionally strong and is meant to be
supplied by concrete models rather than proved in the abstract kernel. -/
def EulerBirthZeroUnique
    (C : VacuumOmegaRContext β α) : Prop :=
  ∀ {x : α},
    birth C.R x = 0 →
      x = (((C.R.eulerBoundary : C.R.Omega) : α))

/-- Helper lemma unpacking the birth-based ranking property for a given
collapse flow. -/
lemma birth_strict_decreases
    (C : VacuumOmegaRContext β α)
    (M : CollapseFlow (C := C))
    (hRank : BirthRankingProperty (C := C) (M := M))
    {a : α}
    (ha_pos : ⊥ < a)
    (ha_sup : a ≤ C.R.support)
    (ha_ne_euler :
      a ≠ (((C.R.eulerBoundary : C.R.Omega) : α))) :
    birth C.R (M.step a) < birth C.R a :=
  hRank ha_pos ha_sup ha_ne_euler

/-- Finite-time convergence to the Euler boundary under a birth-based
ranking hypothesis: for any positive, in-support starting state `a`,
either `a` is already at the Euler boundary, or a single collapse step
lands at a birthday-zero state which, by uniqueness, must be the
Euler boundary. In particular, the Euler boundary is reached in at most
one collapse step. -/
theorem collapse_reaches_euler
    (C : VacuumOmegaRContext β α)
    (M : CollapseFlow (C := C))
    (hRank : BirthRankingProperty (C := C) (M := M))
    (hEulerUnique : EulerBirthZeroUnique (C := C))
    (a : α)
    (ha_pos : ⊥ < a)
    (ha_sup : a ≤ C.R.support) :
    ∃ n : ℕ,
      M.iterate n a =
        (((C.R.eulerBoundary : C.R.Omega) : α)) := by
  have h_le_one :
      birth C.R a ≤ 1 :=
    birth_le_one (R := C.R) (a := a)
  -- Case split on the birthday of `a`.
  cases hBA : birth C.R a with
  | zero =>
      -- Birthday zero: `a` is already the Euler boundary by uniqueness.
      have h_eq :
          a = (((C.R.eulerBoundary : C.R.Omega) : α)) :=
        hEulerUnique (x := a) (by simp [hBA])
      refine ⟨0, ?_⟩
      simp [CollapseFlow.iterate, h_eq]
  | succ n =>
      -- `birth C.R a = n.succ`. Use `birth_le_one` to rule out `n.succ ≥ 2`.
      have h_le_one' : Nat.succ n ≤ 1 := by
        simpa [hBA] using h_le_one
      have hn0 : n = 0 := by
        have hn_le0 : n ≤ 0 := by
          apply Nat.le_of_succ_le_succ
          simpa using h_le_one'
        exact Nat.eq_zero_of_le_zero hn_le0
      subst hn0
      -- `birth C.R a = 1`.
      have h_birth_one : birth C.R a = 1 := by
        simp [hBA]
      -- Show that `a` is not already the Euler boundary.
      have ha_ne_euler :
          a ≠ (((C.R.eulerBoundary : C.R.Omega) : α)) := by
        intro h_eq
        -- But the Euler boundary has birthday zero, contradiction.
        have h_birth_euler :
            birth C.R a = 0 := by
          simp [h_eq]
        have : (1 : ℕ) = 0 := h_birth_one.symm.trans h_birth_euler
        exact Nat.succ_ne_zero 0 this
      -- Strict birth decrease from the ranking property.
      have h_dec :
          birth C.R (M.step a) < birth C.R a :=
        birth_strict_decreases (C := C) (M := M) hRank
          ha_pos ha_sup ha_ne_euler
      -- Since `birth C.R a = 1`, we must have `birth C.R (M.step a) = 0`.
      have h_birth_step_zero :
          birth C.R (M.step a) = 0 := by
        have hlt1 : birth C.R (M.step a) < 1 := by
          simpa [h_birth_one] using h_dec
        have hle0 : birth C.R (M.step a) ≤ 0 :=
          Nat.lt_succ_iff.mp (by simpa using hlt1)
        exact Nat.eq_zero_of_le_zero hle0
      -- Uniqueness of birthday zero identifies `M.step a` with the Euler boundary.
      have h_step_eq :
          M.step a =
            (((C.R.eulerBoundary : C.R.Omega) : α)) :=
        hEulerUnique (x := M.step a) h_birth_step_zero
      refine ⟨1, ?_⟩
      simp [CollapseFlow.iterate, h_step_eq]

/-- Ωᴿ-level corollary of `collapse_reaches_euler`: starting from any
Ωᴿ element with the usual positivity/support assumptions, the collapse
flow reaches the distinguished vacuum fixed point in finitely many
steps, provided the birth-based ranking and uniqueness assumptions
hold. -/
theorem collapse_reaches_vacuumOmega
    (C : VacuumOmegaRContext β α)
    (M : CollapseFlow (C := C))
    (hRank : BirthRankingProperty (C := C) (M := M))
    (hEulerUnique : EulerBirthZeroUnique (C := C))
    (ψ : C.R.Omega)
    (hψ_pos : ⊥ < ((ψ : C.R.Omega) : α))
    (hψ_sup : ((ψ : C.R.Omega) : α) ≤ C.R.support) :
    ∃ n : ℕ,
      M.iterate n ((ψ : C.R.Omega) : α) =
        (((C.vacuumOmega : C.R.Omega) : α)) := by
  -- First reach the Euler boundary at the ambient level.
  obtain ⟨n, hn⟩ :=
    collapse_reaches_euler (C := C) (M := M)
      hRank hEulerUnique ((ψ : C.R.Omega) : α) hψ_pos hψ_sup
  refine ⟨n, ?_⟩
  -- Then identify `vacuumOmega` with the Euler boundary.
  have hvac :
      C.vacuumOmega = C.R.eulerBoundary :=
    VacuumOmegaRContext.vacuumOmega_eq_eulerBoundary (C := C)
  -- Rewrite the target using this coincidence.
  simpa [hvac] using hn

/-! ### Limit-based orbit infimum and attractor-style statements -/

/-- Descending orbit of a collapse flow starting from `a`. -/
noncomputable def orbit (M : CollapseFlow (C := C)) (a : α) : ℕ → α :=
  fun n => M.iterate n a

/-- Candidate order-theoretic limit of a collapse orbit: the infimum of
all its iterates. -/
noncomputable def orbitInf (M : CollapseFlow (C := C)) (a : α) : α :=
  sInf (Set.range (orbit (C := C) M a))

/-- The orbit infimum lies below every point on the orbit. -/
lemma orbitInf_le_iterate (M : CollapseFlow (C := C)) (a : α) (n : ℕ) :
    orbitInf (C := C) M a ≤ M.iterate n a := by
  -- `sInf_le` specialised to the `n`-th iterate in the range.
  have hx : M.iterate n a ∈ Set.range (orbit (C := C) M a) := by
    exact ⟨n, rfl⟩
  exact sInf_le hx

/-- Any lower bound of the orbit is bounded above by the orbit infimum. -/
lemma orbit_lower_bound (M : CollapseFlow (C := C)) (a : α) {b : α}
    (hb : ∀ n, b ≤ M.iterate n a) :
    b ≤ orbitInf (C := C) M a := by
  -- `le_sInf` with the lower-bound property along the entire range.
  refine le_sInf ?_
  intro x hx
  rcases hx with ⟨n, rfl⟩
  exact hb n

/-- Assumption: every point on the orbit lies above the Euler boundary
in the ambient carrier. -/
def OrbitBounds
    (C : VacuumOmegaRContext β α)
    (M : CollapseFlow (C := C)) (a : α) : Prop :=
  ∀ n : ℕ,
    (((C.R.eulerBoundary : C.R.Omega) : α)) ≤ M.iterate n a

/-- Assumption: any ambient lower bound of the orbit lies below the
Euler boundary. This packages the attractor-style minimality of the
Euler boundary with respect to the orbit; it is a model-level property
rather than a general theorem of the kernel. -/
def OrbitLowerBoundProperty
    (C : VacuumOmegaRContext β α)
    (M : CollapseFlow (C := C)) (a : α) : Prop :=
  ∀ {b : α},
    (∀ n : ℕ, b ≤ M.iterate n a) →
      b ≤ (((C.R.eulerBoundary : C.R.Omega) : α))

/-- Under the orbit-bounds and lower-bound hypotheses, the infimum of
the collapse orbit coincides with the Euler boundary: the latter is the
greatest lower bound of the orbit in the ambient lattice. -/
theorem orbitInf_eq_eulerBoundary
    (C : VacuumOmegaRContext β α)
    (M : CollapseFlow (C := C))
    (a : α)
    (hBounds : OrbitBounds (C := C) (M := M) a)
    (hLB : OrbitLowerBoundProperty (C := C) (M := M) a) :
    orbitInf (C := C) M a =
      (((C.R.eulerBoundary : C.R.Omega) : α)) := by
  -- First, the Euler boundary is itself a lower bound of the orbit.
  have h1 :
      (((C.R.eulerBoundary : C.R.Omega) : α)) ≤
        orbitInf (C := C) M a := by
    -- Apply `orbit_lower_bound` with the orbit-bounds hypothesis.
    apply orbit_lower_bound (C := C) (M := M) (a := a)
    intro n; exact hBounds n
  -- Second, the orbit infimum is a lower bound of the orbit, hence
  -- lies below the Euler boundary by `hLB`.
  have h2 :
      orbitInf (C := C) M a ≤
        (((C.R.eulerBoundary : C.R.Omega) : α)) := by
    -- `orbitInf` is a lower bound by `orbitInf_le_iterate`.
    have hb :
        ∀ n : ℕ, orbitInf (C := C) M a ≤ M.iterate n a :=
      fun n => orbitInf_le_iterate (C := C) (M := M) (a := a) n
    exact hLB hb
  exact le_antisymm h2 h1

/-- Ωᴿ-level corollary of `orbitInf_eq_eulerBoundary`: the orbit-infimum
of a collapse flow starting from a positive, in-support Ωᴿ element
coincides with the Ωᴿ vacuum, provided the orbit-bounds and
lower-bound hypotheses hold in the ambient carrier. -/
theorem orbitInf_eq_vacuumOmega
    (C : VacuumOmegaRContext β α)
    (M : CollapseFlow (C := C))
    (ψ : C.R.Omega)
    (hBounds :
      OrbitBounds (C := C) (M := M)
        ((ψ : C.R.Omega) : α))
    (hLB :
      OrbitLowerBoundProperty (C := C) (M := M)
        ((ψ : C.R.Omega) : α)) :
    orbitInf (C := C) M ((ψ : C.R.Omega) : α) =
      (((C.vacuumOmega : C.R.Omega) : α)) := by
  -- First identify the ambient orbit infimum with the Euler boundary.
  have h :=
    orbitInf_eq_eulerBoundary (C := C) (M := M)
      ((ψ : C.R.Omega) : α) hBounds hLB
  -- Then rewrite the right-hand side via `vacuumOmega_eq_eulerBoundary`.
  have hvac :
      C.vacuumOmega = C.R.eulerBoundary :=
    VacuumOmegaRContext.vacuumOmega_eq_eulerBoundary (C := C)
  simpa [hvac] using h

end CollapseFlow

/-! ### QGI-specialised collapse flow and convergence statements -/

namespace QGI

/-- A simple QGI collapse step on `Set QGIβ`: intersect any configuration
with the vacuum-support singleton `{labPath}`. This removes any points
outside the designated support window while leaving the vacuum set
fixed. -/
noncomputable def qgiFlowStep (S : Set QGIContext.β) :
    Set QGIContext.β :=
  {b | b ∈ S ∧ b = labPath}

/-- A `CollapseFlow` instance for the QGI base context built from the
intersection-based `qgiFlowStep`. This flow collapses any configuration
onto the vacuum-support singleton in at most one step and never adds
new points outside the support window. -/
noncomputable def qgiCollapseFlow :
    CollapseFlow (C := QGIContext.qgiBaseContext) := by
  classical
  refine
    { step := qgiFlowStep
      monotone_step := ?_
      step_le_nucleus := ?_
      euler_fixed := ?_
      step_strict := ?_ }
  · -- Monotonicity: intersecting with `{labPath}` is monotone.
    intro a b hab x hx
    rcases hx with ⟨hx_a, hx_lab⟩
    exact And.intro (hab hx_a) hx_lab
  · -- The step never adds new points: `step a ⊆ a`, and `C.R` is the
    -- identity nucleus on `Set QGIβ`.
    intro a x hx
    rcases hx with ⟨hx_a, _⟩
    -- rewrite the target through the identity nucleus
    simpa [QGIContext.qgiBaseContext, QGIContext.reentryQGI] using hx_a
  · -- The Euler boundary is the singleton `{labPath}`, which is fixed
    -- by `qgiFlowStep`.
    have hEuler :
        ((QGIContext.qgiBaseContext.R.eulerBoundary
            : QGIContext.qgiBaseContext.R.Omega) :
          Set QGIContext.β) =
          {b : QGIContext.β | b = labPath} := by
      -- First identify the ambient Euler boundary with the primordial
      -- fixed point.
      have h_eq_proc :
          QGIContext.qgiBaseContext.R.eulerBoundary =
            QGIContext.qgiBaseContext.R.process :=
        LoF.Reentry.eulerBoundary_eq_process
          (R := QGIContext.qgiBaseContext.R)
      have h_coe_proc :
          ((QGIContext.qgiBaseContext.R.process
              : QGIContext.qgiBaseContext.R.Omega) :
            Set QGIContext.β) =
            QGIContext.qgiBaseContext.R.primordial :=
        LoF.Reentry.process_coe (R := QGIContext.qgiBaseContext.R)
      have h_prim :
          QGIContext.qgiBaseContext.R.primordial =
            {b : QGIContext.β | b = labPath} := by
        -- By construction of `reentryQGI`.
        simp [QGIContext.qgiBaseContext, QGIContext.reentryQGI]
      calc
        ((QGIContext.qgiBaseContext.R.eulerBoundary
            : QGIContext.qgiBaseContext.R.Omega) :
          Set QGIContext.β)
            = ((QGIContext.qgiBaseContext.R.process
                : QGIContext.qgiBaseContext.R.Omega) :
              Set QGIContext.β) := by
                  simp
        _ = QGIContext.qgiBaseContext.R.primordial := h_coe_proc
        _ = {b : QGIContext.β | b = labPath} := h_prim
    -- Now compute the effect of `qgiFlowStep` on this singleton.
    have hStep :
        qgiFlowStep
          (((QGIContext.qgiBaseContext.R.eulerBoundary
              : QGIContext.qgiBaseContext.R.Omega) :
            Set QGIContext.β)) =
          {b : QGIContext.β | b = labPath} := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨hx_mem, hx_lab⟩
        -- `hx_mem` witnesses membership in the Euler boundary, which
        -- we rewrite as `{labPath}`.
        have hx' :
            x ∈ ({b : QGIContext.β | b = labPath} :
                    Set QGIContext.β) := by
          simpa [hEuler] using hx_mem
        exact hx'
      · intro hx
        -- Unpack membership in the singleton `{labPath}`.
        have hx_lab : x = labPath := by
          simpa using hx
        have hx_mem :
            x ∈ ((QGIContext.qgiBaseContext.R.eulerBoundary
                    : QGIContext.qgiBaseContext.R.Omega) :
                  Set QGIContext.β) := by
          simpa [hEuler] using hx
        exact And.intro hx_mem hx_lab
    -- Conclude by rewriting through the two computations above.
    exact hStep.trans hEuler.symm
  · -- Strict-progress clause: in the QGI base context there is no
    -- ambient `a` with `⊥ < a`, `a ≤ support`, and
    -- `a ≠ eulerBoundary`, because the support singleton
    -- `{labPath}` already is the Euler boundary. Hence this branch is
    -- uninhabited and we can derive a contradiction.
    intro a ha_pos ha_sup ha_ne
    -- `⊥ < a` on sets means `a ≠ ∅`.
    have hne_bot :
        a ≠ (⊥ : Set QGIContext.β) :=
      bot_lt_iff_ne_bot.mp ha_pos
    have hnonempty : a.Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hne_bot
    obtain ⟨w, hw⟩ := hnonempty
    -- Every element of `a` lies in the support window `{labPath}`.
    have hw_sup :
        w ∈ QGIContext.qgiBaseContext.R.support :=
      ha_sup hw
    have hw_eq_lab : w = labPath := by
      -- Unfold the support definition.
      simpa [QGIContext.qgiBaseContext, QGIContext.reentryQGI]
        using hw_sup
    -- Show that `a` must in fact be the singleton `{labPath}`.
    have ha_eq_singleton :
        a = ({b : QGIContext.β | b = labPath} :
          Set QGIContext.β) := by
      ext x
      constructor
      · intro hx
        -- Any `x ∈ a` must equal `labPath` because `a ⊆ support`.
        have hx_sup :
            x ∈ QGIContext.qgiBaseContext.R.support :=
          ha_sup hx
        simpa [QGIContext.qgiBaseContext, QGIContext.reentryQGI]
          using hx_sup
      · intro hx
        -- Conversely, `labPath ∈ a` because `a` is nonempty and
        -- contained in the singleton support.
        have hx_lab : x = labPath := by
          simpa using hx
        subst hx_lab
        have : labPath ∈ a := by
          simpa [hw_eq_lab] using hw
        exact this
    -- Identify the ambient Euler boundary as the same singleton.
    have hEuler :
        ((QGIContext.qgiBaseContext.R.eulerBoundary
            : QGIContext.qgiBaseContext.R.Omega) :
          Set QGIContext.β) =
        ({b : QGIContext.β | b = labPath} :
          Set QGIContext.β) := by
      -- This is the same computation as in `euler_fixed`.
      have h_eq_proc :
          QGIContext.qgiBaseContext.R.eulerBoundary =
            QGIContext.qgiBaseContext.R.process :=
        LoF.Reentry.eulerBoundary_eq_process
          (R := QGIContext.qgiBaseContext.R)
      have h_coe_proc :
          ((QGIContext.qgiBaseContext.R.process
              : QGIContext.qgiBaseContext.R.Omega) :
            Set QGIContext.β) =
            QGIContext.qgiBaseContext.R.primordial :=
        LoF.Reentry.process_coe (R := QGIContext.qgiBaseContext.R)
      have h_prim :
          QGIContext.qgiBaseContext.R.primordial =
            {b : QGIContext.β | b = labPath} := by
        simp [QGIContext.qgiBaseContext, QGIContext.reentryQGI]
      calc
        ((QGIContext.qgiBaseContext.R.eulerBoundary
            : QGIContext.qgiBaseContext.R.Omega) :
          Set QGIContext.β)
            = ((QGIContext.qgiBaseContext.R.process
                : QGIContext.qgiBaseContext.R.Omega) :
              Set QGIContext.β) := by
                  simp
        _ = QGIContext.qgiBaseContext.R.primordial := h_coe_proc
        _ = {b : QGIContext.β | b = labPath} := h_prim
    -- Combining the two equalities contradicts `ha_ne`.
    have : a =
        ((QGIContext.qgiBaseContext.R.eulerBoundary
            : QGIContext.qgiBaseContext.R.Omega) :
          Set QGIContext.β) := by
      simpa [hEuler] using ha_eq_singleton
    exact (ha_ne this).elim

/-- QGI-specialised finite-time convergence: any collapse flow on the
QGI base context that satisfies the birth-ranking and birth-zero
uniqueness hypotheses reaches the Ωᴿ-level vacuum in finitely many
steps, starting from a positive, in-support Ωᴿ element. -/
theorem collapse_reaches_vacuumOmega_qgi
    (M : CollapseFlow (C := QGIContext.qgiBaseContext))
    (hRank :
      CollapseFlow.BirthRankingProperty
        (C := QGIContext.qgiBaseContext) (M := M))
    (hEulerUnique :
      CollapseFlow.EulerBirthZeroUnique
        (C := QGIContext.qgiBaseContext))
    (ψ : QGIContext.qgiBaseContext.R.Omega)
    (hψ_pos :
      ⊥ < ((ψ : QGIContext.qgiBaseContext.R.Omega) : Set QGIContext.β))
    (hψ_sup :
      ((ψ : QGIContext.qgiBaseContext.R.Omega) : Set QGIContext.β) ≤
        QGIContext.qgiBaseContext.R.support) :
    ∃ n : ℕ,
      M.iterate n
        ((ψ : QGIContext.qgiBaseContext.R.Omega) : Set QGIContext.β) =
        (((QGIContext.qgiBaseContext.vacuumOmega
           : QGIContext.qgiBaseContext.R.Omega) : Set QGIContext.β)) := by
  -- This is a direct specialisation of the abstract
  -- `collapse_reaches_vacuumOmega` theorem to the QGI base context.
  simpa using
    CollapseFlow.collapse_reaches_vacuumOmega
      (C := QGIContext.qgiBaseContext)
      (M := M) hRank hEulerUnique ψ hψ_pos hψ_sup

/-- QGI-specialised orbit-infimum attractor statement: under the
orbit-bounds and lower-bound hypotheses, the orbit-infimum of a QGI
collapse flow starting from a positive Ωᴿ element coincides with the
Ωᴿ-level vacuum. -/
theorem orbitInf_eq_vacuumOmega_qgi
    (M : CollapseFlow (C := QGIContext.qgiBaseContext))
    (ψ : QGIContext.qgiBaseContext.R.Omega)
    (hBounds :
      CollapseFlow.OrbitBounds
        (C := QGIContext.qgiBaseContext)
        (M := M)
        ((ψ : QGIContext.qgiBaseContext.R.Omega) : Set QGIContext.β))
    (hLB :
      CollapseFlow.OrbitLowerBoundProperty
        (C := QGIContext.qgiBaseContext)
        (M := M)
        ((ψ : QGIContext.qgiBaseContext.R.Omega) : Set QGIContext.β)) :
    CollapseFlow.orbitInf
        (C := QGIContext.qgiBaseContext) M
        ((ψ : QGIContext.qgiBaseContext.R.Omega) : Set QGIContext.β) =
      (((QGIContext.qgiBaseContext.vacuumOmega
         : QGIContext.qgiBaseContext.R.Omega) : Set QGIContext.β)) := by
  -- This is a direct specialisation of `orbitInf_eq_vacuumOmega`.
  simpa using
    CollapseFlow.orbitInf_eq_vacuumOmega
      (C := QGIContext.qgiBaseContext)
      (M := M) ψ hBounds hLB

end QGI

end GravitationalCollapse
end Quantum
end HeytingLean
