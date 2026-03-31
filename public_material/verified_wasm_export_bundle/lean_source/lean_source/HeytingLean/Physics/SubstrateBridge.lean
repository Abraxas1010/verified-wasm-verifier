import SubstrateTheory.Core.Types
import SubstrateTheory.Core.Parameters

namespace HeytingLean.Physics.Substrate

open SubstrateTheory

-- Basic aliases so downstream code can refer to SubstrateTheory constructs through
-- the HeytingLean namespace. Adjust these as the integration deepens.

abbrev Entity := SubstrateTheory.Entity
abbrev State := SubstrateTheory.State
abbrev Time := SubstrateTheory.Time
noncomputable def substrateEntity : Entity := SubstrateTheory.Substrate
abbrev groundingConstant : ℝ := SubstrateTheory.c_grounding

/-- Convenience wrapper for the `temporal_slice` helper defined in the core types. -/
noncomputable def temporalSlice (es : List Entity) (t : Time) : List Entity :=
  SubstrateTheory.temporal_slice es t

/-- Re-export the presentation-preservation lemma for temporal slices. -/
theorem temporalSlice_preserves_presentation
    (es : List Entity) (t : Time)
    (h : ∀ e ∈ es, SubstrateTheory.is_presentation e) :
    (∀ e ∈ temporalSlice es t, SubstrateTheory.is_presentation e) :=
  SubstrateTheory.temporal_slice_preserves_presentation es t h

end HeytingLean.Physics.Substrate
