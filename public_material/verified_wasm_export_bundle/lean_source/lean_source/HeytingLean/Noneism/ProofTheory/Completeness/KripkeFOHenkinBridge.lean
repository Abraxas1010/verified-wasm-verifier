import HeytingLean.Noneism.ProofTheory.Completeness.KripkeFO
import HeytingLean.Noneism.ProofTheory.Completeness.KripkeFOHenkin
import HeytingLean.Noneism.Semantics.KripkeFOH

namespace HeytingLean
namespace Noneism
namespace KripkeFO
namespace Completeness
namespace InternalFOH

open Formula
open Syntax.Henkin
open HenkinCompleteness

variable {σ κ : Type}

/--
Embed a base-language theory `T` into the Henkin-language theory over `FormulaH`.
-/
def liftTheory (T : Set (Formula σ)) : Set (FormulaH σ κ) :=
  fun ψ => ∃ φ : Formula σ, φ ∈ T ∧ ψ = liftFormula (σ := σ) (κ := κ) φ

lemma liftFormula_mem_liftTheory
    {T : Set (Formula σ)} {φ : Formula σ}
    (hφ : φ ∈ T) :
    liftFormula (σ := σ) (κ := κ) φ ∈ liftTheory (σ := σ) (κ := κ) T := by
  exact ⟨φ, hφ, rfl⟩

/--
Lift a base derivability witness into Henkin-language derivability.

This is the syntactic bridge from `InternalFO.Derivable` to `HenkinCompleteness.DerivableH`.
-/
theorem derivableH_of_derivable_lift
    {T : Set (Formula σ)} {φ : Formula σ} :
    InternalFO.Derivable (σ := σ) T φ →
      DerivableH (σ := σ) (κ := κ)
        (liftTheory (σ := σ) (κ := κ) T)
        (liftFormula (σ := σ) (κ := κ) φ) := by
  rintro ⟨Γ, hΓT, hDer⟩
  refine ⟨NDH.liftContext (σ := σ) (κ := κ) Γ, ?_, ?_⟩
  · intro ψ hψ
    rcases List.mem_map.1 hψ with ⟨θ, hθΓ, rfl⟩
    exact ⟨θ, hΓT θ hθΓ, rfl⟩
  · exact NDH.derives_of_derives_lift (σ := σ) (κ := κ) hDer

/--
In any Henkin theory closed under `DerivableH` and containing the generated Henkin witness schema set,
membership of a lifted sigma-formula yields membership of its chosen witness body.
-/
theorem chosen_witnessBody_mem_of_lifted_sigma
    {TH : Set (FormulaH σ κ)}
    (choose : Var → FormulaH σ κ → κ)
    (hClosed : ∀ θ, DerivableH (σ := σ) (κ := κ) TH θ → θ ∈ TH)
    (hAxioms : henkinAxiomSet (σ := σ) (κ := κ) choose ⊆ TH)
    {x : Var} {φ : Formula σ}
    (hSigma : liftFormula (σ := σ) (κ := κ) (.sigma x φ) ∈ TH) :
    witnessBody x (choose x (liftFormula (σ := σ) (κ := κ) φ))
      (liftFormula (σ := σ) (κ := κ) φ) ∈ TH := by
  exact closed_contains_chosen_witnessBody_of_sigma
    (σ := σ) (κ := κ) choose hClosed hAxioms hSigma

/--
Canonical packaged form used in completeness routes:
`liftTheory T ∪ henkinAxiomSet choose` is the working Henkinized theory.
-/
theorem chosen_witnessBody_mem_of_liftTheory_union_axioms
    (choose : Var → FormulaH σ κ → κ)
    {T : Set (Formula σ)}
    (hClosed :
      ∀ θ,
        DerivableH (σ := σ) (κ := κ)
          (liftTheory (σ := σ) (κ := κ) T ∪
            henkinAxiomSet (σ := σ) (κ := κ) choose) θ →
          θ ∈ (liftTheory (σ := σ) (κ := κ) T ∪
            henkinAxiomSet (σ := σ) (κ := κ) choose))
    {x : Var} {φ : Formula σ}
    (hSigma : (.sigma x φ : Formula σ) ∈ T) :
    witnessBody x (choose x (liftFormula (σ := σ) (κ := κ) φ))
      (liftFormula (σ := σ) (κ := κ) φ) ∈
        (liftTheory (σ := σ) (κ := κ) T ∪
          henkinAxiomSet (σ := σ) (κ := κ) choose) := by
  apply chosen_witnessBody_mem_of_lifted_sigma
    (σ := σ) (κ := κ)
    (choose := choose)
    (hClosed := hClosed)
  · intro ψ hψ
    exact Or.inr hψ
  · exact Or.inl (liftFormula_mem_liftTheory (σ := σ) (κ := κ) hSigma)

/--
Transfer a Henkin-layer countermodel for lifted formulas to a base FO countermodel.
-/
theorem base_countermodel_of_henkin_countermodel
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hCM :
      ∃ (W : Type) (_ : Preorder W) (D : Type)
        (MH : HeytingLean.Noneism.KripkeFOH.Model W σ D)
        (ρ : HeytingLean.Noneism.KripkeFO.Valuation D)
        (η : HeytingLean.Noneism.KripkeFOH.ParamInterp κ D)
        (w : W),
          (∀ ψ ∈ Γ,
            HeytingLean.Noneism.KripkeFOH.Forces MH ρ η w
              (liftFormula (σ := σ) (κ := κ) ψ)) ∧
          ¬ HeytingLean.Noneism.KripkeFOH.Forces MH ρ η w
              (liftFormula (σ := σ) (κ := κ) φ)) :
    ∃ (W : Type) (_ : Preorder W) (D : Type)
      (M : HeytingLean.Noneism.KripkeFO.Model W σ D)
      (ρ : HeytingLean.Noneism.KripkeFO.Valuation D)
      (w : W),
        (∀ ψ ∈ Γ, HeytingLean.Noneism.KripkeFO.Forces M ρ w ψ) ∧
        ¬ HeytingLean.Noneism.KripkeFO.Forces M ρ w φ := by
  rcases hCM with ⟨W, hW, D, MH, ρ, η, w, hΓ, hNotφ⟩
  refine ⟨W, hW, D, HeytingLean.Noneism.KripkeFOH.lowerModel MH, ρ, w, ?_, ?_⟩
  · intro ψ hψ
    exact (HeytingLean.Noneism.KripkeFOH.forces_liftFormula_iff_lowerModel
      (MH := MH) (ρ := ρ) (η := η) (w := w) (φ := ψ)).1 (hΓ ψ hψ)
  · intro hφ
    apply hNotφ
    exact (HeytingLean.Noneism.KripkeFOH.forces_liftFormula_iff_lowerModel
      (MH := MH) (ρ := ρ) (η := η) (w := w) (φ := φ)).2 hφ

/--
Henkin countermodels for lifted formulas refute base derivability directly (via soundness).
-/
theorem not_derives_of_henkin_countermodel
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hCM :
      ∃ (W : Type) (_ : Preorder W) (D : Type)
        (MH : HeytingLean.Noneism.KripkeFOH.Model W σ D)
        (ρ : HeytingLean.Noneism.KripkeFO.Valuation D)
        (η : HeytingLean.Noneism.KripkeFOH.ParamInterp κ D)
        (w : W),
          (∀ ψ ∈ Γ,
            HeytingLean.Noneism.KripkeFOH.Forces MH ρ η w
              (liftFormula (σ := σ) (κ := κ) ψ)) ∧
          ¬ HeytingLean.Noneism.KripkeFOH.Forces MH ρ η w
              (liftFormula (σ := σ) (κ := κ) φ)) :
    ¬ Derives (σ := σ) Γ φ := by
  intro hDer
  rcases base_countermodel_of_henkin_countermodel (σ := σ) hCM with
    ⟨W, _hW, D, M, ρ, w, hΓ, hNotφ⟩
  have hEnt : HeytingLean.Noneism.KripkeFO.Entails (σ := σ) Γ φ :=
    HeytingLean.Noneism.KripkeFO.soundness (σ := σ) hDer
  exact hNotφ (hEnt (W := W) (D := D) (M := M) (ρ := ρ) (w := w) hΓ)

/--
Henkin-layer internal countermodel interface for base formulas.

This is the concrete target for finishing the canonical/Henkin construction:
produce a Henkin countermodel on lifted formulas for every non-derivable base sequent.
-/
class HasHenkinCountermodel (σ : Type) (κ : Type) : Prop where
  countermodel :
    ∀ {Γ : List (Formula σ)} {φ : Formula σ},
      ¬ Derives (σ := σ) Γ φ →
        ∃ (W : Type) (_ : Preorder W) (D : Type)
          (MH : HeytingLean.Noneism.KripkeFOH.Model W σ D)
          (ρ : HeytingLean.Noneism.KripkeFO.Valuation D)
          (η : HeytingLean.Noneism.KripkeFOH.ParamInterp κ D)
          (w : W),
            (∀ ψ ∈ Γ,
              HeytingLean.Noneism.KripkeFOH.Forces MH ρ η w
                (liftFormula (σ := σ) (κ := κ) ψ)) ∧
            ¬ HeytingLean.Noneism.KripkeFOH.Forces MH ρ η w
                (liftFormula (σ := σ) (κ := κ) φ)

instance (priority := 100)
    hasHenkinCountermodel_of_extension_truth
    [InternalFO.HasExtensionConstruction (σ := σ)]
    [InternalFO.HasTruthLemma (σ := σ)] :
    HasHenkinCountermodel σ κ where
  countermodel := by
    intro Γ φ hNotDer
    rcases InternalFO.countermodel_of_extension_and_truth
      (σ := σ)
      (Γ := Γ)
      (φ := φ)
      (InternalFO.HasExtensionConstruction.extend_avoid (σ := σ))
      (InternalFO.HasTruthLemma.truth_iff_mem (σ := σ))
      hNotDer with
      ⟨w, hΓ, hNotφ⟩
    let η : HeytingLean.Noneism.KripkeFOH.ParamInterp κ Var := fun _ => (0 : Var)
    refine ⟨InternalFO.W (σ := σ), inferInstance, Var,
      HeytingLean.Noneism.KripkeFOH.liftModel
        (M := InternalFO.canonicalModel (σ := σ)),
      InternalFO.idVarValuation, η, w, ?_, ?_⟩
    · intro ψ hψ
      exact
        (HeytingLean.Noneism.KripkeFOH.forces_liftFormula_iff
          (M := InternalFO.canonicalModel (σ := σ))
          (ρ := InternalFO.idVarValuation)
          (η := η)
          (w := w) (φ := ψ)).2 (hΓ ψ hψ)
    · intro hφH
      apply hNotφ
      exact
        (HeytingLean.Noneism.KripkeFOH.forces_liftFormula_iff
          (M := InternalFO.canonicalModel (σ := σ))
          (ρ := InternalFO.idVarValuation)
          (η := η)
          (w := w) (φ := φ)).1 hφH

instance (priority := 100)
    hasHenkinCountermodel_of_internal
    [HasInternalCountermodel σ] :
    HasHenkinCountermodel σ κ where
  countermodel := by
    intro Γ φ hNotDer
    rcases HasInternalCountermodel.countermodel (σ := σ) hNotDer with
      ⟨w, hΓ, hNotφ⟩
    let η : HeytingLean.Noneism.KripkeFOH.ParamInterp κ Var := fun _ => (0 : Var)
    refine ⟨InternalFO.W (σ := σ), inferInstance, Var,
      HeytingLean.Noneism.KripkeFOH.liftModel
        (M := InternalFO.canonicalModel (σ := σ)),
      InternalFO.idVarValuation, η, w, ?_, ?_⟩
    · intro ψ hψ
      exact
        (HeytingLean.Noneism.KripkeFOH.forces_liftFormula_iff
          (M := InternalFO.canonicalModel (σ := σ))
          (ρ := InternalFO.idVarValuation)
          (η := η)
          (w := w) (φ := ψ)).2 (hΓ ψ hψ)
    · intro hφH
      apply hNotφ
      exact
        (HeytingLean.Noneism.KripkeFOH.forces_liftFormula_iff
          (M := InternalFO.canonicalModel (σ := σ))
          (ρ := InternalFO.idVarValuation)
          (η := η)
          (w := w) (φ := φ)).1 hφH

/--
Base FO completeness from a Henkin-layer countermodel constructor.
-/
theorem completeness_from_henkin_countermodel
    [HasHenkinCountermodel σ κ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    HeytingLean.Noneism.KripkeFO.Entails (σ := σ) Γ φ →
      Derives (σ := σ) Γ φ := by
  intro hEnt
  by_contra hNotDer
  rcases HasHenkinCountermodel.countermodel (σ := σ) (κ := κ) hNotDer with
    ⟨W, hW, D, MH, ρ, η, w, hΓH, hNotφH⟩
  rcases base_countermodel_of_henkin_countermodel (σ := σ) (κ := κ)
    (hCM := ⟨W, hW, D, MH, ρ, η, w, hΓH, hNotφH⟩) with
    ⟨W', _hW', D', M, ρ', w', hΓ, hNotφ⟩
  exact hNotφ (hEnt (W := W') (D := D') (M := M) (ρ := ρ') (w := w') hΓ)

/-- Soundness + completeness from the Henkin-layer countermodel interface. -/
theorem sound_complete_from_henkin_countermodel
    [HasHenkinCountermodel σ κ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (σ := σ) Γ φ ↔ HeytingLean.Noneism.KripkeFO.Entails (σ := σ) Γ φ := by
  constructor
  · intro hDer
    exact HeytingLean.Noneism.KripkeFO.soundness (σ := σ) hDer
  · intro hEnt
    exact completeness_from_henkin_countermodel (σ := σ) (κ := κ) hEnt

/--
Completeness via the Henkin bridge from explicit internal canonical artifacts.
-/
theorem completeness_from_extension_truth_via_henkin
    {κ : Type}
    [InternalFO.HasExtensionConstruction (σ := σ)]
    [InternalFO.HasTruthLemma (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    HeytingLean.Noneism.KripkeFO.Entails (σ := σ) Γ φ →
      Derives (σ := σ) Γ φ := by
  intro hEnt
  exact completeness_from_henkin_countermodel (σ := σ) (κ := κ) hEnt

/--
Soundness + completeness via the Henkin bridge from explicit internal canonical artifacts.
-/
theorem sound_complete_from_extension_truth_via_henkin
    {κ : Type}
    [InternalFO.HasExtensionConstruction (σ := σ)]
    [InternalFO.HasTruthLemma (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (σ := σ) Γ φ ↔ HeytingLean.Noneism.KripkeFO.Entails (σ := σ) Γ φ := by
  constructor
  · intro hDer
    exact HeytingLean.Noneism.KripkeFO.soundness (σ := σ) hDer
  · intro hEnt
    exact completeness_from_extension_truth_via_henkin (σ := σ) (κ := κ) hEnt

/--
Compatibility endpoint: current internal countermodel artifacts can be consumed
through the Henkin bridge API without changing downstream theorem statements.
-/
theorem completeness_from_internal_via_henkin
    {κ : Type}
    [HasInternalCountermodel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    HeytingLean.Noneism.KripkeFO.Entails (σ := σ) Γ φ →
      Derives (σ := σ) Γ φ := by
  intro hEnt
  exact completeness_from_henkin_countermodel (σ := σ) (κ := κ) hEnt

/--
Soundness + completeness via the Henkin bridge, sourced from the current internal
countermodel artifact.
-/
theorem sound_complete_from_internal_via_henkin
    {κ : Type}
    [HasInternalCountermodel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (σ := σ) Γ φ ↔ HeytingLean.Noneism.KripkeFO.Entails (σ := σ) Γ φ := by
  constructor
  · intro hDer
    exact HeytingLean.Noneism.KripkeFO.soundness (σ := σ) hDer
  · intro hEnt
    exact completeness_from_internal_via_henkin (σ := σ) (κ := κ) hEnt

end InternalFOH
end Completeness
end KripkeFO
end Noneism
end HeytingLean
