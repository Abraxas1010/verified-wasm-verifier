import HeytingLean.PerspectivalPlenum.SheafLensCategory
import HeytingLean.Quantum.Contextuality.Triangle
import HeytingLean.Crypto.ConstructiveHardness.ContextualityPhysical

namespace HeytingLean
namespace PerspectivalPlenum
namespace ContextualityEngine

open HeytingLean.Crypto.ConstructiveHardness

abbrev Ctx := HeytingLean.LoF.CryptoSheaf.Quantum.Context
abbrev GlobalSectionTask := HeytingLean.Crypto.ConstructiveHardness.GlobalSectionTask

/-- Every context in the cover admits at least one local section in the empirical support. -/
def LocallyAdmissibleOnCover
    {cover : Finset Ctx}
    (e : HeytingLean.LoF.CryptoSheaf.Quantum.EmpiricalModel cover) : Prop :=
  ∀ {C : Ctx}, (hC : C ∈ cover) → (e.support hC).Nonempty

/-- Global section existence (explicit alias for the bridge layer). -/
abbrev GloballyAdmissible
    (X : Ctx) (cover : Finset Ctx)
    (e : HeytingLean.LoF.CryptoSheaf.Quantum.EmpiricalModel cover)
    (coverSubX : ∀ {C}, C ∈ cover → C ⊆ X) : Prop :=
  HeytingLean.LoF.CryptoSheaf.Quantum.HasGlobalSection X cover e coverSubX

/-- Global obstruction: no global section exists. -/
abbrev GloballyObstructed
    (X : Ctx) (cover : Finset Ctx)
    (e : HeytingLean.LoF.CryptoSheaf.Quantum.EmpiricalModel cover)
    (coverSubX : ∀ {C}, C ∈ cover → C ⊆ X) : Prop :=
  HeytingLean.LoF.CryptoSheaf.Quantum.NoGlobalSection X cover e coverSubX

@[simp] theorem globallyAdmissible_iff_globalSectionTask
    (X : Ctx) (cover : Finset Ctx)
    (e : HeytingLean.LoF.CryptoSheaf.Quantum.EmpiricalModel cover)
    (coverSubX : ∀ {C}, C ∈ cover → C ⊆ X) :
    GloballyAdmissible X cover e coverSubX ↔
      GlobalSectionTask X cover e coverSubX :=
  Iff.rfl

@[simp] theorem globallyObstructed_iff_noGlobalSection
    (X : Ctx) (cover : Finset Ctx)
    (e : HeytingLean.LoF.CryptoSheaf.Quantum.EmpiricalModel cover)
    (coverSubX : ∀ {C}, C ∈ cover → C ⊆ X) :
    GloballyObstructed X cover e coverSubX ↔
      HeytingLean.LoF.CryptoSheaf.Quantum.NoGlobalSection X cover e coverSubX :=
  Iff.rfl

/-- Any empirical model is locally admissible by construction (`nonempty` support condition). -/
theorem locallyAdmissible_of_empirical
    {cover : Finset Ctx}
    (e : HeytingLean.LoF.CryptoSheaf.Quantum.EmpiricalModel cover) :
    LocallyAdmissibleOnCover e := by
  intro C hC
  exact e.nonempty hC

@[simp] theorem globallyObstructed_iff_not_globallyAdmissible
    (X : Ctx) (cover : Finset Ctx)
    (e : HeytingLean.LoF.CryptoSheaf.Quantum.EmpiricalModel cover)
    (coverSubX : ∀ {C}, C ∈ cover → C ⊆ X) :
    GloballyObstructed X cover e coverSubX ↔
      ¬ GloballyAdmissible X cover e coverSubX :=
  Iff.rfl

/-- Contextual obstruction keeps all local witnesses while blocking global glue. -/
theorem local_admissibility_and_global_obstruction
    (X : Ctx) (cover : Finset Ctx)
    (e : HeytingLean.LoF.CryptoSheaf.Quantum.EmpiricalModel cover)
    (coverSubX : ∀ {C}, C ∈ cover → C ⊆ X)
    (hNo : GloballyObstructed X cover e coverSubX) :
    LocallyAdmissibleOnCover e ∧ GloballyObstructed X cover e coverSubX := by
  exact ⟨locallyAdmissible_of_empirical e, hNo⟩

/--
Canonical bridge re-export: contextual global obstruction implies physical impossibility
of the global-section task.
-/
theorem canonical_contextuality_implies_physImpossible
    (Φ : PhysicalModality)
    (X : Ctx) (cover : Finset Ctx)
    (e : HeytingLean.LoF.CryptoSheaf.Quantum.EmpiricalModel cover)
    (coverSubX : ∀ {C}, C ∈ cover → C ⊆ X) :
    GloballyObstructed X cover e coverSubX →
      ¬ Φ.toFun (GlobalSectionTask X cover e coverSubX) := by
  intro hObs
  exact HeytingLean.Crypto.ConstructiveHardness.contextuality_implies_physImpossible
    (Φ := Φ) (X := X) (cover := cover) (e := e) (coverSubX := coverSubX) hObs

/-- Triangle witness: locally admissible in every context, globally obstructed. -/
theorem triangle_local_and_global_obstruction :
    LocallyAdmissibleOnCover HeytingLean.Quantum.Contextuality.Triangle.model ∧
      GloballyObstructed
        HeytingLean.Quantum.Contextuality.Triangle.X
        HeytingLean.Quantum.Contextuality.Triangle.cover
        HeytingLean.Quantum.Contextuality.Triangle.model
        (fun {C} hC => HeytingLean.Quantum.Contextuality.Triangle.coverSubX (C := C) hC) := by
  refine local_admissibility_and_global_obstruction
    (X := HeytingLean.Quantum.Contextuality.Triangle.X)
    (cover := HeytingLean.Quantum.Contextuality.Triangle.cover)
    (e := HeytingLean.Quantum.Contextuality.Triangle.model)
    (coverSubX := fun {C} hC => HeytingLean.Quantum.Contextuality.Triangle.coverSubX (C := C) hC) ?_
  exact HeytingLean.Quantum.Contextuality.Triangle.noGlobal

/-- Global obstruction feeds directly into physical impossibility under any sound modality. -/
theorem globallyObstructed_implies_physImpossible
    (Φ : PhysicalModality)
    (X : Ctx) (cover : Finset Ctx)
    (e : HeytingLean.LoF.CryptoSheaf.Quantum.EmpiricalModel cover)
    (coverSubX : ∀ {C}, C ∈ cover → C ⊆ X) :
    GloballyObstructed X cover e coverSubX →
      ¬ Φ.toFun (GlobalSectionTask X cover e coverSubX) := by
  exact canonical_contextuality_implies_physImpossible
    (Φ := Φ) (X := X) (cover := cover) (e := e) (coverSubX := coverSubX)

/-- Triangle specialization of the physical-impossibility bridge. -/
theorem triangle_physImpossible (Φ : PhysicalModality) :
    ¬ Φ.toFun
      (GlobalSectionTask
        HeytingLean.Quantum.Contextuality.Triangle.X
        HeytingLean.Quantum.Contextuality.Triangle.cover
        HeytingLean.Quantum.Contextuality.Triangle.model
        (fun {C} hC => HeytingLean.Quantum.Contextuality.Triangle.coverSubX (C := C) hC)) := by
  exact HeytingLean.Crypto.ConstructiveHardness.triangle_physImpossible Φ

@[simp] theorem triangle_physImpossible_iff_constructiveHardness (Φ : PhysicalModality) :
    (¬ Φ.toFun
        (GlobalSectionTask
          HeytingLean.Quantum.Contextuality.Triangle.X
          HeytingLean.Quantum.Contextuality.Triangle.cover
          HeytingLean.Quantum.Contextuality.Triangle.model
          (fun {C} hC => HeytingLean.Quantum.Contextuality.Triangle.coverSubX (C := C) hC))) ↔
      (¬ Φ.toFun
        (HeytingLean.Crypto.ConstructiveHardness.GlobalSectionTask
          HeytingLean.Quantum.Contextuality.Triangle.X
          HeytingLean.Quantum.Contextuality.Triangle.cover
          HeytingLean.Quantum.Contextuality.Triangle.model
          (fun {C} hC => HeytingLean.Quantum.Contextuality.Triangle.coverSubX (C := C) hC))) :=
  Iff.rfl

end ContextualityEngine
end PerspectivalPlenum
end HeytingLean
