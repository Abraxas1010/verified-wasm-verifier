import HeytingLean.LoF.Nucleus
import HeytingLean.LoF.OmegaCategory
import HeytingLean.Logic.Dialectic
import HeytingLean.Logic.PSR
import HeytingLean.Epistemic.Occam
import Mathlib.CategoryTheory.Closed.Cartesian

/-
# Rosetta.Core: Baez–Stay columns over `Ω_R`

This module provides a thin, fully-specified Rosetta-style API on top of the
fixed-point lattice `Ω_R` of a reentry nucleus `R`.  It realises the Baez–Stay
“four columns” view (logic, processes/physics, computation) using a single
underlying Heyting algebra `R.Omega` and its cartesian monoidal structure:

* objects in all columns are just elements of `R.Omega`;
* morphisms are arrows in the preorder category on `R.Omega`;
* tensor is the cartesian tensor (meet) on `R.Omega`;
* internal hom is the Heyting implication, via `OmegaCategory.ihom`.

No marker comments and no partial definitions are introduced here: every alias is a
fully-defined abbreviation of existing, proven structures.
-/

namespace HeytingLean
namespace LoF
namespace Rosetta

open CategoryTheory
open OmegaCategory

universe u

variable {α : Type u} [PrimaryAlgebra α]

/-! ## Rosetta notations (unscoped, Unicode-safe)

These notations are lightweight aliases for existing categorical and Heyting
operations. They are global (not scoped) to avoid parser issues with certain
Unicode-plus-scope combinations under `notation3`, but they introduce no new
semantics:

* `A ⊗ᵣ B` is just the monoidal tensor `A ⊗ B`;
* `Iᵣ[Ω]` is the tensor unit of a monoidal category `Ω`;
* `A ⊸ᵣ B` is just the Heyting implication `A ⇨ B`.

In particular, when `Ω = R.Omega` these specialise to the Baez–Stay tensor,
unit and internal hom on `Ω_R`. -/

notation A "⊗ᵣ" B => MonoidalCategoryStruct.tensorObj A B
notation "Iᵣ[" Ω "]" => MonoidalCategoryStruct.tensorUnit Ω
notation A "⊸ᵣ" B => A ⇨ B

/-! ## Column aliases (Baez–Stay “four columns”) -/

section Columns

variable (R : Reentry α)

/-- Propositions in the Rosetta logic column are just elements of `Ω_R`. -/
abbrev Proposition : Type u := R.Omega

/-- A proof from `A` to `B` is a morphism in the thin category on `Ω_R`. -/
abbrev Proof (A B : Proposition R) : Type _ := A ⟶ B

/-- Systems in the Rosetta process/physics column are also elements of `Ω_R`. -/
abbrev System : Type u := R.Omega

/-- A process from `A` to `B` is the same morphism `A ⟶ B` in the Ω₍R₎ category. -/
abbrev Process (A B : System R) : Type _ := A ⟶ B

/-- Data types in the computation column are again the objects of `Ω_R`. -/
abbrev DataType : Type u := R.Omega

/-- A program from `A` to `B` is a morphism `A ⟶ B` in `Ω_R`. -/
abbrev Program (A B : DataType R) : Type _ := A ⟶ B

end Columns

/-! ## Bridges to PSR, Occam, and dialectic synthesis -/

section Bridges

variable (R : Reentry α)

/-- Rosetta alias for the Principle of Sufficient Reason:
fixed points of the reentry nucleus `R`. -/
abbrev SufficientReason (a : α) : Prop :=
  Logic.PSR.Sufficient (R := R) a

@[simp] lemma sufficientReason_iff (R : Reentry α) (a : α) :
    SufficientReason (R := R) a ↔
      Logic.PSR.Sufficient (R := R) a :=
  Iff.rfl

/-- Rosetta alias for the Occam reduction associated to `R`. -/
noncomputable abbrev OccamReduction (a : α) : α :=
  Epistemic.occam (R := R) a

/-- Rosetta-level synthesis in `Ω_R`, given by dialectic synthesis
specialised to fixed points. -/
abbrev Synthesis (T A : R.Omega) : R.Omega :=
  Logic.Dialectic.synthOmega (R := R) T A

end Bridges

end Rosetta
end LoF
end HeytingLean
