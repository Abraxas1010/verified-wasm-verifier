import Mathlib.Data.Set.Lattice
import HeytingLean.ClosingTheLoop.Semantics.KernelLaws
import HeytingLean.MirandaDynamics.Thermal.Basic
import HeytingLean.MirandaDynamics.Thermal.SafetyPredicates

/-!
# MirandaDynamics.Thermal: observation-window kernel

The thermal integration is intended to be *observation-first*:
we observe only a finite window of temperature readings.

On the semantic side, this is naturally modeled as a **kernel/interior operator** on predicates:

> "`K_n S` holds at a state `x` iff **all** states observationally indistinguishable from `x`
>  (under an `n`-sample window) lie in `S`."

This operator is:
- monotone,
- meet-preserving,
- idempotent,
- contractive (`K_n S ⊆ S`).

So it fits `HeytingLean.ClosingTheLoop.Semantics.Kernel`.

This is a more accurate fit than a closure-style "nucleus" for finite observation.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Thermal

open Set
open HeytingLean.ClosingTheLoop.Semantics

universe u

section

variable {α : Type u}

/-- The `n`-sample observation key for an array of thermal readings.

If `n` exceeds the array length, `take` returns the whole array.
This represents what can be observed in a finite time window.
-/
def thermalObsKey (n : Nat) (x : Array ThermalSample) : Array ThermalSample :=
  x.take n

/-- Observational indistinguishability: same observation key at window size `n`.

Two thermal histories are indistinguishable if their observable windows match.
-/
def ThermalObsEq (n : Nat) (x y : Array ThermalSample) : Prop :=
  thermalObsKey n x = thermalObsKey n y

/-- The observation kernel `K_n` on sets of thermal sample arrays.

`x ∈ K_n S` iff every `y` with the same `n`-prefix observation is also in `S`.
This captures the epistemological limit: we can only verify properties
that are invariant under observation-window equivalence.
-/
def thermalKernelSet (n : Nat) (S : Set (Array ThermalSample)) : Set (Array ThermalSample) :=
  {x | ∀ y, ThermalObsEq n x y → y ∈ S}

theorem thermalKernelSet_subset (n : Nat) (S : Set (Array ThermalSample)) :
    thermalKernelSet n S ⊆ S := by
  intro x hx
  exact hx x rfl

theorem thermalKernelSet_mono (n : Nat) : Monotone (thermalKernelSet n) := by
  intro S T hST x hx y hy
  exact hST (hx y hy)

theorem thermalKernelSet_inf (n : Nat) (S T : Set (Array ThermalSample)) :
    thermalKernelSet n (S ⊓ T) = thermalKernelSet n S ⊓ thermalKernelSet n T := by
  ext x
  constructor
  · intro hx
    refine ⟨?_, ?_⟩ <;> intro y hy
    · exact (hx y hy).1
    · exact (hx y hy).2
  · rintro ⟨hxS, hxT⟩
    intro y hy
    exact ⟨hxS y hy, hxT y hy⟩

theorem thermalKernelSet_idem (n : Nat) (S : Set (Array ThermalSample)) :
    thermalKernelSet n (thermalKernelSet n S) = thermalKernelSet n S := by
  ext x
  constructor
  · intro hx
    exact hx x rfl
  · intro hx y hy z hz
    have : ThermalObsEq n x z := by
      -- Transitivity: hy says key(x) = key(y), hz says key(y) = key(z)
      exact hy.trans hz
    exact hx z this

/-- Bundle `thermalKernelSet` as a `Kernel` on `Set (Array ThermalSample)`. -/
def thermalKernel (n : Nat) : Kernel (α := Set (Array ThermalSample)) where
  toFun := thermalKernelSet n
  monotone' := thermalKernelSet_mono n
  map_inf' := thermalKernelSet_inf n
  idempotent' := thermalKernelSet_idem n
  apply_le' := thermalKernelSet_subset n

/-! ## Temperature-specific kernels -/

/-- Extract temperature values from a sample array for comparison. -/
def tempValues (samples : Array ThermalSample) : Array Float :=
  samples.map (·.tempC)

/-- Observation key based on temperature values only (ignoring zone metadata). -/
def tempObsKey (n : Nat) (x : Array Float) : Array Float :=
  x.take n

/-- Temperature-based observational indistinguishability. -/
def TempObsEq (n : Nat) (x y : Array Float) : Prop :=
  tempObsKey n x = tempObsKey n y

/-- Temperature-only observation kernel. -/
def tempKernelSet (n : Nat) (S : Set (Array Float)) : Set (Array Float) :=
  {x | ∀ y, TempObsEq n x y → y ∈ S}

theorem tempKernelSet_subset (n : Nat) (S : Set (Array Float)) :
    tempKernelSet n S ⊆ S := by
  intro x hx
  exact hx x rfl

theorem tempKernelSet_mono (n : Nat) : Monotone (tempKernelSet n) := by
  intro S T hST x hx y hy
  exact hST (hx y hy)

theorem tempKernelSet_idem (n : Nat) (S : Set (Array Float)) :
    tempKernelSet n (tempKernelSet n S) = tempKernelSet n S := by
  ext x
  constructor
  · intro hx
    exact hx x rfl
  · intro hx y hy z hz
    exact hx z (hy.trans hz)

/-- Bundle temperature kernel. -/
def tempKernel (n : Nat) : Kernel (α := Set (Array Float)) where
  toFun := tempKernelSet n
  monotone' := tempKernelSet_mono n
  map_inf' := by
    intro S T
    ext x
    constructor
    · intro hx
      refine ⟨?_, ?_⟩ <;> intro y hy
      · exact (hx y hy).1
      · exact (hx y hy).2
    · rintro ⟨hxS, hxT⟩
      intro y hy
      exact ⟨hxS y hy, hxT y hy⟩
  idempotent' := tempKernelSet_idem n
  apply_le' := tempKernelSet_subset n

end

/-! ## Safety-preserving observation -/

/-- The set of thermal histories where all samples are safe. -/
def SafeHistories : Set (Array ThermalSample) :=
  {x | x.all isSafeSampleDecide}

/-- Observable safety: safety that can be verified from a finite observation window.

This is the kernel applied to SafeHistories, giving us the strongest
verifiable safety predicate under finite observation.
-/
def ObservableSafeHistories (n : Nat) : Set (Array ThermalSample) :=
  thermalKernelSet n SafeHistories

/-- Observable safety is weaker than full safety. -/
theorem observable_safe_implies_safe (n : Nat) :
    ObservableSafeHistories n ⊆ SafeHistories :=
  thermalKernelSet_subset n SafeHistories

end Thermal
end MirandaDynamics
end HeytingLean
