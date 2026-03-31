import HeytingLean.PerspectivalPlenum.Lens.Profile

namespace HeytingLean
namespace PerspectivalPlenum
namespace Lens

universe u

/-- A semantic lens provides local witnessing and contradiction detection for objects. -/
structure SemanticLens (α : Type u) where
  profile : LensProfile
  witness : α → Prop
  contradicts : α → Prop

/-- Local satisfiability in a lens: witness plus policy-compatible contradiction behavior. -/
def LocallySatisfiable {α : Type u} (L : SemanticLens α) (x : α) : Prop :=
  L.witness x ∧ (allowsContradictions L.profile ∨ ¬ L.contradicts x)

/-- Local collapse to bottom in a lens. -/
def CollapseToBottom {α : Type u} (L : SemanticLens α) (x : α) : Prop :=
  ¬ LocallySatisfiable L x

@[simp] theorem collapse_iff_not_satisfiable {α : Type u} (L : SemanticLens α) (x : α) :
    CollapseToBottom L x ↔ ¬ LocallySatisfiable L x := Iff.rfl

/-- If a lens disallows contradictions and the object is contradictory there, it collapses. -/
theorem collapse_of_strict_contradiction {α : Type u} (L : SemanticLens α) (x : α)
    (hStrict : ¬ allowsContradictions L.profile)
    (_hWitness : L.witness x)
    (hContra : L.contradicts x) :
    CollapseToBottom L x := by
  intro hSat
  rcases hSat with ⟨_, hPolicy⟩
  cases hPolicy with
  | inl hAllow => exact hStrict hAllow
  | inr hNotContra => exact hNotContra hContra

/-- If a lens allows contradictions and has a witness, the object is locally satisfiable. -/
theorem satisfiable_of_allowed_contradiction {α : Type u} (L : SemanticLens α) (x : α)
    (hWitness : L.witness x)
    (hAllow : allowsContradictions L.profile) :
    LocallySatisfiable L x :=
  ⟨hWitness, Or.inl hAllow⟩

/-- A single object can collapse in one lens and remain satisfiable in another. -/
theorem lens_relative_collapse_and_survival {α : Type u}
    (A B : SemanticLens α) (x : α)
    (hAstrict : ¬ allowsContradictions A.profile)
    (hAwitness : A.witness x)
    (hAcontra : A.contradicts x)
    (hBwitness : B.witness x)
    (hBallow : allowsContradictions B.profile) :
    CollapseToBottom A x ∧ LocallySatisfiable B x := by
  refine ⟨?_, ?_⟩
  · exact collapse_of_strict_contradiction A x hAstrict hAwitness hAcontra
  · exact satisfiable_of_allowed_contradiction B x hBwitness hBallow

end Lens
end PerspectivalPlenum
end HeytingLean
