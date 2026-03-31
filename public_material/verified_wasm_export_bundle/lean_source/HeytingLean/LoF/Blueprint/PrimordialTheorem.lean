import HeytingLean.LoF.Nucleus
import HeytingLean.Bridges.Graph
import HeytingLean.Bridges.Tensor
import HeytingLean.LoF.Blueprint.Residuation

/-
# Primordial LoF theorems and nucleus anchors

This module provides:

* `PrimordialTheorem` — nucleus-centric metadata for a LoF theorem living in `Ω_R`;
* `NucleusAnchor` — a small bundle tying a reentry nucleus `R` to graph/tensor models;
* canonical instances for:
  * the Euler-boundary theorem `R.eulerBoundary = R.process`;
  * the residuation law on `Ω_R`.
-/

namespace HeytingLean
namespace LoF
namespace Blueprint

open HeytingLean.LoF
open HeytingLean.LoF.Reentry

universe u

variable {α : Type u} [PrimaryAlgebra α]

/-- Nucleus-centric theorem metadata: pinned to a reentry nucleus `R` and the
fixed-point core `Ω_R`.  This record is intentionally lightweight and
blueprint-oriented: it packages a proposition `P` together with its proof and
optional distinguished elements and tags. -/
structure PrimordialTheorem (α : Type u) [PrimaryAlgebra α] where
  /-- Re-entry nucleus providing the ambient Heyting core. -/
  R : Reentry α
  /-- Core proposition phrased in terms of `Ω_R` or the ambient algebra. -/
  P : Prop
  /-- Proof of the core proposition. -/
  proof : P
  /-- Human-readable label for the theorem. -/
  label : String := ""
  /-- Optional text description. -/
  description : Option String := none
  /-- Optional distinguished left-hand element in `Ω_R` (e.g. Euler boundary). -/
  lhs? : Option (R.Omega) := none
  /-- Optional distinguished right-hand element in `Ω_R` (e.g. primordial). -/
  rhs? : Option (R.Omega) := none
  /-- Free-form tags for lenses, domains, etc. -/
  tags : List String := []

/-- Anchor bundle tying a reentry nucleus to its standard graph and tensor
bridge models.  This serves as the shared "R nucleus" object for visual and
transport layers. -/
structure NucleusAnchor (α : Type u) [PrimaryAlgebra α] where
  /-- Re-entry nucleus. -/
  R : Reentry α
  /-- Graph bridge model sharing the same nucleus. -/
  graphModel : Bridges.Graph.Model α
  /-- Tensor bridge model sharing the same nucleus. -/
  tensorModel : Bridges.Tensor.Model α
  /-- Witness that the graph model uses the same nucleus. -/
  graph_eq : graphModel.R = R
  /-- Witness that the tensor model uses the same nucleus. -/
  tensor_eq : tensorModel.R = R

namespace Instances

/-- Primordial theorem instance for the Euler-boundary theorem
`R.eulerBoundary = R.process`. -/
noncomputable def eulerBoundaryPrimordial (R : Reentry α) :
    PrimordialTheorem α :=
  { R := R
    P := R.eulerBoundary = R.process
    proof := Reentry.eulerBoundary_eq_process (R := R)
    label := "Euler boundary = process"
    description := some "The Euler boundary of Ω_R coincides with the primordial process."
    lhs? := some R.eulerBoundary
    rhs? := some R.process
    tags := ["lof", "nucleus", "euler-boundary"] }

/-- Primordial theorem instance for the residuation law on `Ω_R`:
`a ⊓ b ≤ c ↔ a ≤ b ⇨ c`. -/
def residuationPrimordial (R : Reentry α) (a b c : R.Omega) :
    PrimordialTheorem α :=
  { R := R
    P := a ⊓ b ≤ c ↔ a ≤ b ⇨ c
    proof := residuation_equiv (R := R) a b c
    label := "Heyting residuation on Ω_R"
    description := some "Residuation law in the Heyting core Ω_R: a ⊓ b ≤ c ↔ a ≤ b ⇨ c."
    lhs? := none
    rhs? := none
    tags := ["lof", "heyting", "residuation"] }

end Instances

end Blueprint
end LoF
end HeytingLean
