import Mathlib.Data.Set.Lattice
import HeytingLean.ClosingTheLoop.Semantics.KernelLaws

/-!
# MirandaDynamics.Seismic: observation-window kernel

The seismic integration is intended to be *observation-first*:
we observe only a finite window of a signal.

On the semantic side, this is naturally modeled as a **kernel/interior operator** on predicates:

> “`K_n S` holds at a state `x` iff **all** states observationally indistinguishable from `x`
>  (under an `n`-sample window) lie in `S`.”

This operator is:
- monotone,
- meet-preserving,
- idempotent,
- contractive (`K_n S ⊆ S`).

So it fits `HeytingLean.ClosingTheLoop.Semantics.Kernel`.

This is a more accurate fit than a closure-style “nucleus” for finite observation.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Seismic

open Set
open HeytingLean.ClosingTheLoop.Semantics

universe u

section

variable {α : Type u}

/-- The `n`-sample observation key for an array.

If `n` exceeds the array length, `take` returns the whole array.
-/
def obsKey (n : Nat) (x : Array α) : Array α :=
  x.take n

/-- Observational indistinguishability: same `obsKey` at window size `n`. -/
def ObsEq (n : Nat) (x y : Array α) : Prop :=
  obsKey (α := α) n x = obsKey (α := α) n y

/-- The observation kernel `K_n` on sets of arrays.

`x ∈ K_n S` iff every `y` with the same `n`-prefix observation is also in `S`.
-/
def obsKernelSet (n : Nat) (S : Set (Array α)) : Set (Array α) :=
  {x | ∀ y, ObsEq (α := α) n x y → y ∈ S}

theorem obsKernelSet_subset (n : Nat) (S : Set (Array α)) : obsKernelSet (α := α) n S ⊆ S := by
  intro x hx
  exact hx x rfl

theorem obsKernelSet_mono (n : Nat) : Monotone (obsKernelSet (α := α) n) := by
  intro S T hST x hx y hy
  exact hST (hx y hy)

theorem obsKernelSet_inf (n : Nat) (S T : Set (Array α)) :
    obsKernelSet (α := α) n (S ⊓ T) = obsKernelSet (α := α) n S ⊓ obsKernelSet (α := α) n T := by
  ext x
  constructor
  · intro hx
    refine ⟨?_, ?_⟩ <;> intro y hy
    · exact (hx y hy).1
    · exact (hx y hy).2
  · rintro ⟨hxS, hxT⟩
    intro y hy
    exact ⟨hxS y hy, hxT y hy⟩

theorem obsKernelSet_idem (n : Nat) (S : Set (Array α)) :
    obsKernelSet (α := α) n (obsKernelSet (α := α) n S) = obsKernelSet (α := α) n S := by
  ext x
  constructor
  · intro hx
    -- choose `y=x`
    exact hx x rfl
  · intro hx y hy z hz
    -- `ObsEq x z` holds because keys are equal by transitivity of equality.
    have : ObsEq (α := α) n x z := by
      -- `key x = key y` and `key y = key z`.
      -- `hy : key x = key y`, `hz : key y = key z`.
      exact hy.trans hz
    exact hx z this

/-- Bundle `obsKernelSet` as a `Kernel` on `Set (Array α)`. -/
def obsKernel (n : Nat) : Kernel (α := Set (Array α)) where
  toFun := obsKernelSet (α := α) n
  monotone' := obsKernelSet_mono (α := α) n
  map_inf' := obsKernelSet_inf (α := α) n
  idempotent' := obsKernelSet_idem (α := α) n
  apply_le' := obsKernelSet_subset (α := α) n

end

end Seismic
end MirandaDynamics
end HeytingLean
