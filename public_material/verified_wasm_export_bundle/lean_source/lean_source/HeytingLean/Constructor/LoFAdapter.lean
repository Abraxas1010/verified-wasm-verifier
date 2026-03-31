import HeytingLean.LoF.Nucleus
import HeytingLean.Constructor.Core

/-!
# LoF adapter for Constructor meta-theory

This module provides lightweight adapters from the LoF reentry nucleus
`Reentry` and its fixed-point sublocale `Ω_R` into the abstract Constructor
meta-theory defined in `Constructor.Core`.

It does **not** fix a particular substrate (Surreal, CA, quantum, …) and does
not provide a `Meta` instance yet; instead it packages common constructions
that concrete substrates can reuse when instantiating `Meta`.
-/

open Classical

namespace HeytingLean
namespace Constructor
namespace LoFAdapter

universe u

variable {α : Type u} [LoF.PrimaryAlgebra α]

/-- Fixed-point sublocale `Ω_R` associated to a reentry nucleus `R`. This is
just an alias for `Reentry.Omega` to make the Constructor-facing notation
more explicit. -/
abbrev Omega (R : LoF.Reentry α) : Type u :=
  R.Omega

/-- Underlying ambient element of a point in `Ω_R`. This is simply the
coercion from the sublocale back to the primary algebra. -/
def toAmbient {R : LoF.Reentry α} (x : Omega (α := α) R) : α :=
  (x : α)

/-- Occam candidate built from the Euler boundary: given a reentry nucleus `R`,
return the ambient element corresponding to its Euler boundary in `Ω_R`.

Concrete `Meta` instances may use this as a building block for the `Occam`
operator when the boundary plays the role of a canonical minimal explanation. -/
noncomputable def occamBoundary {R : LoF.Reentry α} : α :=
  ((R.eulerBoundary : R.Omega) : α)

/-- Principle of Sufficient Reason candidate: a task-expression `a` satisfies
`psrFixed` when it is a fixed point of the reentry nucleus `R`. -/
def psrFixed {R : LoF.Reentry α} (a : α) : Prop :=
  R a = a

/-- Dialectic synthesis candidate: given two task-expressions `a` and `b`,
their dialectic combination is taken to be the reentry of their join.

This matches the intuition that dialectic synthesis forms a composite and
then stabilises it via `R`. -/
def dialecticJoin {R : LoF.Reentry α} (a b : α) : α :=
  R (a ⊔ b)

end LoFAdapter
end Constructor
end HeytingLean
