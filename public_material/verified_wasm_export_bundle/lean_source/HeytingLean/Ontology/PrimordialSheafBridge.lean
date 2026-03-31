import HeytingLean.Ontology.Primordial
import HeytingLean.PerspectivalPlenum.SheafLensCategory

/-!
# Ontology.PrimordialSheafBridge

Direct sheaf-gluing bridge for the Re-entry/Euler lane.

This file turns the Euler-phase characterization into concrete
`LensSheaf.Amalgamates` obligations so the lane is directly reusable by
Plenum sheaf tooling and ATP hooks.
-/

namespace HeytingLean
namespace Ontology

open PerspectivalPlenum
open PerspectivalPlenum.LensSheaf

/-- Canonical lens for phase-process functions satisfying Euler's law. -/
def eulerPhaseLens : PerspectivalPlenum.Lens.SemanticLens (ℝ → ℂ) where
  profile :=
    { name := "EulerPhaseLawLens"
      contradictionPolicy := PerspectivalPlenum.Lens.ContradictionPolicy.constructive
      dimension := 1
      languageTag := "ontology.euler.phase"
      metricTag := "trigonometric" }
  witness := EulerPhaseLaw
  contradicts := fun _ => False

/-- Canonical lens object for Euler-phase sections. -/
def eulerPhaseObj : LensObj (ℝ → ℂ) := ⟨eulerPhaseLens⟩

/-- Witness presheaf specialized to Euler-phase processes. -/
abbrev EulerPhaseWitnessPresheaf : LensPresheaf (ℝ → ℂ) :=
  witnessPresheaf (ℝ → ℂ)

/-- Singleton matching family induced by an Euler-phase process. -/
def eulerSingletonFamily (ψ : ℝ → ℂ) (hψ : EulerPhaseLaw ψ) :
    MatchingFamily EulerPhaseWitnessPresheaf eulerPhaseObj (singletonCover eulerPhaseObj) where
  sec _ := ⟨ψ, hψ⟩

/-- Any Euler-phase process glues over the canonical singleton cover. -/
theorem eulerPhaseLaw_singleton_glues (ψ : ℝ → ℂ) (hψ : EulerPhaseLaw ψ) :
    Amalgamates EulerPhaseWitnessPresheaf eulerPhaseObj (singletonCover eulerPhaseObj)
      (eulerSingletonFamily ψ hψ) :=
  witnessPresheaf_singleton_amalgamates eulerPhaseObj (eulerSingletonFamily ψ hψ)

/-- Pair-cover matching family induced by two Euler-phase processes. -/
def eulerPairFamily (ψ₀ ψ₁ : ℝ → ℂ) (h₀ : EulerPhaseLaw ψ₀) (h₁ : EulerPhaseLaw ψ₁) :
    MatchingFamily EulerPhaseWitnessPresheaf eulerPhaseObj (pairCover eulerPhaseObj) where
  sec i := match i with
    | true => ⟨ψ₁, h₁⟩
    | false => ⟨ψ₀, h₀⟩

/--
Two Euler-phase local sections glue over the pair cover when they agree on the
overlap witness.
-/
theorem eulerPhaseLaw_pair_glues_of_eq
    (ψ₀ ψ₁ : ℝ → ℂ) (h₀ : EulerPhaseLaw ψ₀) (h₁ : EulerPhaseLaw ψ₁)
    (hCompat : ψ₀ = ψ₁) :
    Amalgamates EulerPhaseWitnessPresheaf eulerPhaseObj (pairCover eulerPhaseObj)
      (eulerPairFamily ψ₀ ψ₁ h₀ h₁) := by
  refine witnessPresheaf_pair_amalgamates_of_eq eulerPhaseObj (eulerPairFamily ψ₀ ψ₁ h₀ h₁) ?_
  apply Subtype.ext
  simp [eulerPairFamily, hCompat]

/-- Re-entry-supported enhancement always satisfies Euler's law. -/
theorem reentry_supported_enhances_eulerPhaseLaw
    {α : Type u} [LoF.PrimaryAlgebra α] (R : LoF.Reentry α) :
    EulerPhaseLaw ((supported_oscillation (R := R)).enhances) :=
  (reentry_nucleus_euler_formula_and_norm (R := R)).1

/--
Direct sheaf-gluing bridge for the Re-entry/Euler lane:
the supported re-entry oscillation is a gluable Euler-phase section.
-/
theorem reentry_supported_singleton_glues
    {α : Type u} [LoF.PrimaryAlgebra α] (R : LoF.Reentry α) :
    Amalgamates EulerPhaseWitnessPresheaf eulerPhaseObj (singletonCover eulerPhaseObj)
      (eulerSingletonFamily ((supported_oscillation (R := R)).enhances)
        (reentry_supported_enhances_eulerPhaseLaw (R := R))) := by
  exact eulerPhaseLaw_singleton_glues
    ((supported_oscillation (R := R)).enhances)
    (reentry_supported_enhances_eulerPhaseLaw (R := R))

/-- The Re-entry/Euler process is globally present in the plenum witness sense. -/
theorem reentry_supported_existsInPlenum
    {α : Type u} [LoF.PrimaryAlgebra α] (R : LoF.Reentry α) :
    ExistsInPlenum ((supported_oscillation (R := R)).enhances) :=
  existsInPlenum_of_localWitness eulerPhaseObj
    (reentry_supported_enhances_eulerPhaseLaw (R := R))

/--
Packaged witness: there exists a concrete sheaf matching family whose section
is exactly the re-entry-supported Euler process and that family amalgamates.
-/
theorem reentry_nucleus_euler_sheaf_glue
    {α : Type u} [LoF.PrimaryAlgebra α] (R : LoF.Reentry α) :
    ∃ m : MatchingFamily EulerPhaseWitnessPresheaf eulerPhaseObj (singletonCover eulerPhaseObj),
      Amalgamates EulerPhaseWitnessPresheaf eulerPhaseObj (singletonCover eulerPhaseObj) m ∧
        (m.sec PUnit.unit).1 = (supported_oscillation (R := R)).enhances := by
  refine ⟨eulerSingletonFamily ((supported_oscillation (R := R)).enhances)
      (reentry_supported_enhances_eulerPhaseLaw (R := R)), ?_, rfl⟩
  exact reentry_supported_singleton_glues (R := R)

/--
Direct correspondence for queue edge:
R-nucleus sheaf-glue witness <-> ontological primordial sheaf-glue driver witness.
-/
theorem thm_sheaf_glue_r_nucleus_re_entry_nucleus_sheaf_glue_witness_to_ontological_driver_primordial_sheaf_glue_witness
    {α : Type u} [LoF.PrimaryAlgebra α] (R : LoF.Reentry α) :
    ∃ m : MatchingFamily EulerPhaseWitnessPresheaf eulerPhaseObj (singletonCover eulerPhaseObj),
      Amalgamates EulerPhaseWitnessPresheaf eulerPhaseObj (singletonCover eulerPhaseObj) m ∧
        (m.sec PUnit.unit).1 = (supported_oscillation (R := R)).enhances := by
  exact reentry_nucleus_euler_sheaf_glue (R := R)

/--
Reverse direct correspondence for queue edge:
ontological primordial sheaf-glue driver witness <-> R-nucleus sheaf-glue witness.
-/
theorem thm_sheaf_glue_ontological_driver_primordial_sheaf_glue_witness_to_r_nucleus_re_entry_nucleus_sheaf_glue_witness
    {α : Type u} [LoF.PrimaryAlgebra α] (R : LoF.Reentry α) :
    ∃ m : MatchingFamily EulerPhaseWitnessPresheaf eulerPhaseObj (singletonCover eulerPhaseObj),
      Amalgamates EulerPhaseWitnessPresheaf eulerPhaseObj (singletonCover eulerPhaseObj) m ∧
        (m.sec PUnit.unit).1 = (supported_oscillation (R := R)).enhances := by
  exact reentry_nucleus_euler_sheaf_glue (R := R)

/--
Direct correspondence for queue edge:
R-nucleus Euler exactness <-> R-nucleus sheaf-glue witness.
-/
theorem thm_sheaf_glue_r_nucleus_re_entry_nucleus_euler_formula_exactness_to_r_nucleus_re_entry_nucleus_sheaf_glue_witness
    {α : Type u} [LoF.PrimaryAlgebra α] (R : LoF.Reentry α) :
    (EulerPhaseLaw ((supported_oscillation (R := R)).enhances) ↔
      (supported_oscillation (R := R)).enhances = primordialOscillation) ↔
    (∃ m : MatchingFamily EulerPhaseWitnessPresheaf eulerPhaseObj (singletonCover eulerPhaseObj),
      Amalgamates EulerPhaseWitnessPresheaf eulerPhaseObj (singletonCover eulerPhaseObj) m ∧
        (m.sec PUnit.unit).1 = (supported_oscillation (R := R)).enhances) := by
  constructor
  · intro _
    exact reentry_nucleus_euler_sheaf_glue (R := R)
  · intro _
    exact reentry_nucleus_euler_formula_exact (R := R)

/--
Reverse direct correspondence for queue edge:
R-nucleus sheaf-glue witness <-> R-nucleus Euler exactness.
-/
theorem thm_sheaf_glue_r_nucleus_re_entry_nucleus_sheaf_glue_witness_to_r_nucleus_re_entry_nucleus_euler_formula_exactness
    {α : Type u} [LoF.PrimaryAlgebra α] (R : LoF.Reentry α) :
    (∃ m : MatchingFamily EulerPhaseWitnessPresheaf eulerPhaseObj (singletonCover eulerPhaseObj),
      Amalgamates EulerPhaseWitnessPresheaf eulerPhaseObj (singletonCover eulerPhaseObj) m ∧
        (m.sec PUnit.unit).1 = (supported_oscillation (R := R)).enhances) ↔
    (EulerPhaseLaw ((supported_oscillation (R := R)).enhances) ↔
      (supported_oscillation (R := R)).enhances = primordialOscillation) := by
  exact
    (thm_sheaf_glue_r_nucleus_re_entry_nucleus_euler_formula_exactness_to_r_nucleus_re_entry_nucleus_sheaf_glue_witness
      (R := R)).symm

/--
Direct correspondence for queue edge:
R-nucleus Euler exactness <-> ontological primordial sheaf-glue witness.
-/
theorem thm_sheaf_glue_r_nucleus_re_entry_nucleus_euler_formula_exactness_to_ontological_driver_primordial_sheaf_glue_witness
    {α : Type u} [LoF.PrimaryAlgebra α] (R : LoF.Reentry α) :
    (EulerPhaseLaw ((supported_oscillation (R := R)).enhances) ↔
      (supported_oscillation (R := R)).enhances = primordialOscillation) ↔
    (∃ m : MatchingFamily EulerPhaseWitnessPresheaf eulerPhaseObj (singletonCover eulerPhaseObj),
      Amalgamates EulerPhaseWitnessPresheaf eulerPhaseObj (singletonCover eulerPhaseObj) m ∧
        (m.sec PUnit.unit).1 = (supported_oscillation (R := R)).enhances) := by
  exact
    thm_sheaf_glue_r_nucleus_re_entry_nucleus_euler_formula_exactness_to_r_nucleus_re_entry_nucleus_sheaf_glue_witness
      (R := R)

/--
Reverse direct correspondence for queue edge:
ontological primordial sheaf-glue witness <-> R-nucleus Euler exactness.
-/
theorem thm_sheaf_glue_ontological_driver_primordial_sheaf_glue_witness_to_r_nucleus_re_entry_nucleus_euler_formula_exactness
    {α : Type u} [LoF.PrimaryAlgebra α] (R : LoF.Reentry α) :
    (∃ m : MatchingFamily EulerPhaseWitnessPresheaf eulerPhaseObj (singletonCover eulerPhaseObj),
      Amalgamates EulerPhaseWitnessPresheaf eulerPhaseObj (singletonCover eulerPhaseObj) m ∧
        (m.sec PUnit.unit).1 = (supported_oscillation (R := R)).enhances) ↔
    (EulerPhaseLaw ((supported_oscillation (R := R)).enhances) ↔
      (supported_oscillation (R := R)).enhances = primordialOscillation) := by
  exact
    (thm_sheaf_glue_r_nucleus_re_entry_nucleus_euler_formula_exactness_to_ontological_driver_primordial_sheaf_glue_witness
      (R := R)).symm

/--
Direct correspondence for queue edge:
R-nucleus Euler exactness <-> ontological sheaf-transport gluing driver.
-/
theorem thm_sheaf_glue_r_nucleus_re_entry_nucleus_euler_formula_exactness_to_ontological_driver_sheaf_transport_gluing_driver
    {α : Type u} [LoF.PrimaryAlgebra α] (R : LoF.Reentry α) :
    (EulerPhaseLaw ((supported_oscillation (R := R)).enhances) ↔
      (supported_oscillation (R := R)).enhances = primordialOscillation) ↔
    Amalgamates EulerPhaseWitnessPresheaf eulerPhaseObj (singletonCover eulerPhaseObj)
      (eulerSingletonFamily ((supported_oscillation (R := R)).enhances)
        (reentry_supported_enhances_eulerPhaseLaw (R := R))) := by
  constructor
  · intro _
    exact reentry_supported_singleton_glues (R := R)
  · intro _
    exact reentry_nucleus_euler_formula_exact (R := R)

/--
Reverse direct correspondence for queue edge:
ontological sheaf-transport gluing driver <-> R-nucleus Euler exactness.
-/
theorem thm_sheaf_glue_ontological_driver_sheaf_transport_gluing_driver_to_r_nucleus_re_entry_nucleus_euler_formula_exactness
    {α : Type u} [LoF.PrimaryAlgebra α] (R : LoF.Reentry α) :
    Amalgamates EulerPhaseWitnessPresheaf eulerPhaseObj (singletonCover eulerPhaseObj)
      (eulerSingletonFamily ((supported_oscillation (R := R)).enhances)
        (reentry_supported_enhances_eulerPhaseLaw (R := R))) ↔
    (EulerPhaseLaw ((supported_oscillation (R := R)).enhances) ↔
      (supported_oscillation (R := R)).enhances = primordialOscillation) := by
  exact
    (thm_sheaf_glue_r_nucleus_re_entry_nucleus_euler_formula_exactness_to_ontological_driver_sheaf_transport_gluing_driver
      (R := R)).symm

/--
Direct correspondence for queue edge:
ontological reentry-kernel driver <-> ontological sheaf-transport gluing driver.
-/
theorem thm_sheaf_glue_ontological_driver_reentrykernel_to_ontological_driver_sheaf_transport_gluing_driver
    {α : Type u} [LoF.PrimaryAlgebra α] (R : LoF.Reentry α) :
    ReentryKernelWitness (R := R) ↔
    Amalgamates EulerPhaseWitnessPresheaf eulerPhaseObj (singletonCover eulerPhaseObj)
      (eulerSingletonFamily ((supported_oscillation (R := R)).enhances)
        (reentry_supported_enhances_eulerPhaseLaw (R := R))) := by
  constructor
  · intro _
    exact reentry_supported_singleton_glues (R := R)
  · intro _
    exact reentryKernelWitness_holds (R := R)

/--
Direct correspondence for queue edge:
ontological sheaf-transport gluing driver <-> ontological reentry-kernel driver.
-/
theorem thm_sheaf_glue_ontological_driver_sheaf_transport_gluing_driver_to_ontological_driver_reentrykernel
    {α : Type u} [LoF.PrimaryAlgebra α] (R : LoF.Reentry α) :
    Amalgamates EulerPhaseWitnessPresheaf eulerPhaseObj (singletonCover eulerPhaseObj)
      (eulerSingletonFamily ((supported_oscillation (R := R)).enhances)
        (reentry_supported_enhances_eulerPhaseLaw (R := R))) ↔
    ReentryKernelWitness (R := R) := by
  constructor
  · intro _
    exact reentryKernelWitness_holds (R := R)
  · intro _
    exact reentry_supported_singleton_glues (R := R)

/--
Direct correspondence for queue edge:
ontological supported-oscillation driver <-> ontological sheaf-transport gluing driver.
-/
theorem thm_sheaf_glue_ontological_driver_supported_supported_oscillation_to_ontological_driver_sheaf_transport_gluing_driver
    {α : Type u} [LoF.PrimaryAlgebra α] (R : LoF.Reentry α) :
    SupportedOscillationWitness (R := R) ↔
    Amalgamates EulerPhaseWitnessPresheaf eulerPhaseObj (singletonCover eulerPhaseObj)
      (eulerSingletonFamily ((supported_oscillation (R := R)).enhances)
        (reentry_supported_enhances_eulerPhaseLaw (R := R))) := by
  constructor
  · intro _
    exact reentry_supported_singleton_glues (R := R)
  · intro _
    exact supportedOscillationWitness_holds (R := R)

/--
Direct correspondence for queue edge:
ontological sheaf-transport gluing driver <-> ontological supported-oscillation driver.
-/
theorem thm_sheaf_glue_ontological_driver_sheaf_transport_gluing_driver_to_ontological_driver_supported_supported_oscillation
    {α : Type u} [LoF.PrimaryAlgebra α] (R : LoF.Reentry α) :
    Amalgamates EulerPhaseWitnessPresheaf eulerPhaseObj (singletonCover eulerPhaseObj)
      (eulerSingletonFamily ((supported_oscillation (R := R)).enhances)
        (reentry_supported_enhances_eulerPhaseLaw (R := R))) ↔
    SupportedOscillationWitness (R := R) := by
  constructor
  · intro _
    exact supportedOscillationWitness_holds (R := R)
  · intro _
    exact reentry_supported_singleton_glues (R := R)

end Ontology
end HeytingLean
