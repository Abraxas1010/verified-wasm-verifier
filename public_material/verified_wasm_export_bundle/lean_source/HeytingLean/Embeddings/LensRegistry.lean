import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

/-!
# Extensible Lens Registry

This module provides an extensible typeclass-based lens registry system,
replacing closed `LensID` enums with an open architecture that allows:

- Dynamic lens selection per computation
- Domain-specific lens extensions without modifying core code
- Preset configurations for common use cases

## Design

A **lens** is a representational view of the R-nucleus fixed-point algebra Ω_R.
Each lens provides:
- A carrier type for its representation
- Encode/decode functions satisfying the RoundTrip contract
- Optional truncation for approximation

The registry uses typeclasses to allow any conforming type to participate
in the adelic multi-lens architecture.

## Usage

```lean
-- Enable specific lenses
def myConfig := LensConfig.ofList [.tensor, .graph, .surreal]

-- Use domain preset
def quantumConfig := LensPreset.quantum
```
-/

namespace HeytingLean
namespace Embeddings

/-! ## Core Typeclass Infrastructure -/

/-- A lens tag is any type that can identify a lens in the registry.

This is the extension point: define new lens tag types to add domain-specific
lenses without modifying the core system. -/
class LensTag (τ : Type*) where
  /-- Human-readable name for display -/
  name : τ → String
  /-- Unique identifier for serialization/persistence -/
  id : τ → String
  /-- Optional description of what this lens represents -/
  description : τ → String := fun t => s!"Lens: {name t}"

/-- Compute a stable hash for a lens tag (for caching). -/
def LensTag.hash [LensTag τ] (t : τ) : UInt64 :=
  (LensTag.id t).hash

/-! ## Active Lens Configuration -/

/-- An active lens configuration specifies which lenses are enabled
for a particular computation or adelic representation. -/
structure ActiveLenses (τ : Type*) [LensTag τ] where
  /-- Predicate for which lenses are enabled -/
  enabled : τ → Bool
  /-- Proof that only finitely many are enabled (for computability) -/
  finite_enabled : ∃ (s : Finset τ), ∀ t, enabled t → t ∈ s

/-- A lens set is a finite collection of lens tags. -/
structure LensSet (τ : Type*) [LensTag τ] [DecidableEq τ] where
  /-- The underlying finset of lens tags -/
  lenses : Finset τ

namespace LensSet

variable {τ : Type*} [LensTag τ] [DecidableEq τ]

/-- Create a lens set from a list. -/
def ofList (ts : List τ) : LensSet τ :=
  { lenses := ts.toFinset }

/-- Check membership in a lens set. -/
def contains (s : LensSet τ) (t : τ) : Bool :=
  t ∈ s.lenses

/-- Union of lens sets. -/
def union (s₁ s₂ : LensSet τ) : LensSet τ :=
  { lenses := s₁.lenses ∪ s₂.lenses }

/-- Intersection of lens sets. -/
def inter (s₁ s₂ : LensSet τ) : LensSet τ :=
  { lenses := s₁.lenses ∩ s₂.lenses }

/-- Convert lens set to active lens configuration. -/
def toActive (s : LensSet τ) : ActiveLenses τ :=
  { enabled := fun t => t ∈ s.lenses
    finite_enabled := ⟨s.lenses, fun _ h => of_decide_eq_true h⟩ }

/-- Size of the lens set. -/
def size (s : LensSet τ) : ℕ := Finset.card s.lenses

instance instMembershipLensSet : Membership τ (LensSet τ) where
  mem := fun (s : LensSet τ) (t : τ) => t ∈ s.lenses

instance instUnionLensSet : Union (LensSet τ) where
  union := union

instance instInterLensSet : Inter (LensSet τ) where
  inter := inter

end LensSet

/-! ## Lens Priority for Lane-Changing -/

/-- Priority ordering for lens selection in lane-changing ATP. -/
structure LensPriority (τ : Type*) [LensTag τ] where
  /-- Priority score (higher = try first) -/
  priorityOf : τ → ℕ
  /-- Fallback order when priorities are equal -/
  tiebreaker : τ → τ → Bool

namespace LensPriority

variable {τ : Type*} [LensTag τ]

/-- Sort lenses by priority (descending). -/
def sortByPriority [DecidableEq τ] (p : LensPriority τ) (ts : List τ) : List τ :=
  ts.mergeSort (fun a b => p.priorityOf a > p.priorityOf b ||
    (p.priorityOf a == p.priorityOf b && p.tiebreaker a b))

/-- Default priority: all lenses equal. -/
def uniform : LensPriority τ :=
  { priorityOf := fun _ => 0
    tiebreaker := fun _ _ => false }

end LensPriority

/-! ## Lens Configuration -/

/-- Runtime lens configuration for dynamic selection. -/
structure LensConfig (τ : Type*) [LensTag τ] [DecidableEq τ] where
  /-- Enabled lens set -/
  enabled : LensSet τ
  /-- Priority ordering -/
  lensPriority : LensPriority τ := LensPriority.uniform
  /-- Truncation level per lens (None = no truncation) -/
  truncationLevel : τ → Option ℕ := fun _ => none

namespace LensConfig

variable {τ : Type*} [LensTag τ] [DecidableEq τ]

/-- Create config from a list of lenses. -/
def ofList (ts : List τ) : LensConfig τ :=
  { enabled := LensSet.ofList ts }

/-- Check if a lens is enabled. -/
def isEnabled (c : LensConfig τ) (t : τ) : Bool :=
  c.enabled.contains t

/-- Get enabled lenses sorted by priority (noncomputable due to Finset.toList). -/
noncomputable def sortedLenses (c : LensConfig τ) : List τ :=
  c.lensPriority.sortByPriority c.enabled.lenses.toList

end LensConfig

end Embeddings
end HeytingLean
