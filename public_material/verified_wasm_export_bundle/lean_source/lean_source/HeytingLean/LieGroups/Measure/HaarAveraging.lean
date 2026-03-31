/-
Copyright (c) 2026 Apoth3osis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/
import HeytingLean.LieGroups.Imports

/-!
# Haar Measure and Averaging

This module provides utilities for Haar measure on locally compact groups
and invariant measures under group actions.

## Main definitions

* `haar` — the Haar measure normalized by a positive compact set

## Main results

* `smul_null` — invariant measure: images of null sets are null
-/

set_option autoImplicit false

namespace HeytingLean
namespace LieGroups
namespace Measure

open MeasureTheory
open scoped Pointwise

section Haar

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- A positive compact set used to normalize `haarMeasure`. -/
abbrev K₀ (G : Type*) [TopologicalSpace G] := TopologicalSpace.PositiveCompacts G

/-- The Haar measure normalized by `K`. -/
noncomputable def haar (K : K₀ G) : MeasureTheory.Measure G :=
  MeasureTheory.Measure.haarMeasure K

/-- `haarMeasure` is a Haar measure. -/
instance isHaarMeasure_haar (K : K₀ G) : MeasureTheory.Measure.IsHaarMeasure (haar K) :=
  MeasureTheory.Measure.isHaarMeasure_haarMeasure K

/-- Left invariance of Haar measure. -/
instance isMulLeftInvariant_haar (K : K₀ G) :
    (haar K).IsMulLeftInvariant :=
  inferInstance

end Haar

section ActionInvariance

open MeasureTheory

variable {G : Type*} [Group G]
variable {α : Type*} [MeasurableSpace α] [MulAction G α]

variable (μ : MeasureTheory.Measure α) [SMulInvariantMeasure G α μ]

/-- Invariance implies images of null sets are null. -/
lemma smul_null (g : G) {s : Set α} (hs : μ s = 0) : μ (g • s) = 0 :=
  MeasureTheory.measure_smul_null (μ := μ) hs g

/-- Invariance implies preimages of null sets are null. -/
lemma smul_inv_null (g : G) {s : Set α} (hs : μ s = 0) : μ (g⁻¹ • s) = 0 :=
  MeasureTheory.measure_smul_null (μ := μ) hs g⁻¹

end ActionInvariance

end Measure
end LieGroups
end HeytingLean
