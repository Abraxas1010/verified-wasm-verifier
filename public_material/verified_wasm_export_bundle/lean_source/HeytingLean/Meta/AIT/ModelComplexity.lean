import HeytingLean.Meta.AIT.BirthBridge

/-
# Unified model complexity interface

This module packages together the two primary complexity measures used
in the Occam/birth-index bridge:

* program-length complexity at the AIT layer, and
* birth-index complexity at the Ωᴿ / interior layer.

The `ModelComplexity` structure is intentionally minimal: it simply
records, for a given model index type `M`, how to read off both
complexities.  Concrete instances are provided for:

* `ReentryModelFamily` (using `codeComplexity` and `birthComplexity`), and
* `IntReentryModelFamily` (using the corresponding interior notions).

This keeps the interface honest and assumption-free: no global Occam theorem
is asserted here.  Instead, later phases can state and prove comparison
results for specific instantiated families (logic, physics, assembly)
using this common façade.
-/

namespace HeytingLean.Meta.AIT

open HeytingLean.Epistemic
open HeytingLean.LoF
open HeytingLean.Generative

variable {α M D O : Type} [PrimaryAlgebra α]

/-- A paired complexity profile for a family of models indexed by `M`.

`codeComplexity` typically arises from AIT-style program-length measures,
whereas `birthComplexity` arises from Ωᴿ- or interior-style birth indices.
The fields are abstract so that different concrete families can plug in
their own definitions. -/
structure ModelComplexity (M : Type) where
  /-- Program-based complexity of a model. -/
  codeComplexity  : M → Nat
  /-- Birth-index-based complexity of a model. -/
  birthComplexity : M → Nat

namespace ModelComplexity

variable (C : ModelComplexity M)

/-- A simple dominance relation between two models with respect to a given
complexity profile: `m₁` is no more complex than `m₂` if both its code
and birth complexities are bounded above by those of `m₂`. -/
def dominates (m₁ m₂ : M) : Prop :=
  C.codeComplexity m₁ ≤ C.codeComplexity m₂ ∧
    C.birthComplexity m₁ ≤ C.birthComplexity m₂

end ModelComplexity

/-- Package the existing reentry-based complexity measures for a model
family into a unified `ModelComplexity` profile. -/
noncomputable def ReentryModelFamily.toModelComplexity
    (F : ReentryModelFamily (α := α) (M := M) (D := D) (O := O)) :
    ModelComplexity M :=
  { codeComplexity  := F.codeComplexity
    birthComplexity := F.birthComplexity }

/-- Package the existing interior-reentry-based complexity measures for a
model family into a unified `ModelComplexity` profile. -/
noncomputable def IntReentryModelFamily.toModelComplexity
    (F : IntReentryModelFamily (α := α) (M := M) (D := D) (O := O)) :
    ModelComplexity M :=
  { codeComplexity  := F.codeComplexity
    birthComplexity := F.birthComplexity }

end HeytingLean.Meta.AIT
