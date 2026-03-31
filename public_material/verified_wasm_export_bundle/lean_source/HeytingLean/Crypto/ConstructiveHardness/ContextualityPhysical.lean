import HeytingLean.Crypto.ConstructiveHardness.PhysicalModality
import HeytingLean.LoF.CryptoSheaf.Quantum.EmpiricalModel

/-!
# Contextuality ⇒ physical impossibility (CT polarity)

This file is the “pure” bridge layer intended for extraction:
it does **not** mention `Nucleus` or `Constructor.impossible`.

Content:
* `NoGlobalSection` is the KS-style obstruction (`¬ HasGlobalSection`).
* For any *physical* modality `Φ` with soundness `Φ P → P`, we get
  `¬P → ¬Φ P` and thus contextuality implies *physical impossibility* of the
  corresponding global-assignment task.
-/

namespace HeytingLean
namespace Crypto
namespace ConstructiveHardness

open HeytingLean.LoF.CryptoSheaf.Quantum

/-- The “global assignment exists” task for an empirical model, as a proposition. -/
abbrev GlobalSectionTask
    (X : Context) (cover : Finset Context)
    (e : EmpiricalModel cover)
    (coverSubX : ∀ {C}, C ∈ cover → C ⊆ X) : Prop :=
  HasGlobalSection X cover e coverSubX

/-- Fully constructive core: contextuality is the negation of existence of a global section. -/
theorem contextuality_implies_not_globalSectionTask
    (X : Context) (cover : Finset Context)
    (e : EmpiricalModel cover)
    (coverSubX : ∀ {C}, C ∈ cover → C ⊆ X) :
    NoGlobalSection X cover e coverSubX → ¬ GlobalSectionTask X cover e coverSubX := by
  intro hNo
  simpa [GlobalSectionTask, NoGlobalSection] using hNo

/-- (A) If `Φ` is a physical-possibility modality (sound: `Φ P → P`), then contextuality implies
`¬ Φ (HasGlobalSection ...)`. -/
theorem contextuality_implies_physImpossible
    (Φ : PhysicalModality)
    (X : Context) (cover : Finset Context)
    (e : EmpiricalModel cover)
    (coverSubX : ∀ {C}, C ∈ cover → C ⊆ X) :
    NoGlobalSection X cover e coverSubX →
      ¬ Φ.toFun (GlobalSectionTask X cover e coverSubX) := by
  intro hNo
  have hNot : ¬ GlobalSectionTask X cover e coverSubX :=
    contextuality_implies_not_globalSectionTask
      (X := X) (cover := cover) (e := e) (coverSubX := coverSubX) hNo
  exact (PhysicalModality.not_toFun_of_not (Φ := Φ) hNot)

/-- Concrete witness: the triangle empirical model has no global section, hence any sound physical
modality `Φ` makes the global-section task physically impossible. -/
theorem triangle_physImpossible (Φ : PhysicalModality) :
    ¬ Φ.toFun
        (GlobalSectionTask X_abc triangleCover triangleModel (fun {_} h => triangle_cover_subset_X h)) := by
  exact
    contextuality_implies_physImpossible
      (Φ := Φ)
      (X := X_abc) (cover := triangleCover) (e := triangleModel)
      (coverSubX := fun {_} h => triangle_cover_subset_X h)
      triangle_no_global

end ConstructiveHardness
end Crypto
end HeytingLean
