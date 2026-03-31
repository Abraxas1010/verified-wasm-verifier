import Mathlib.Data.Fintype.Basic
import HeytingLean.ModalCategorySets.Propositional.Substitution

namespace HeytingLean.ModalCategorySets.Validities

open HeytingLean.ModalCategorySets.Propositional
open scoped Classical

universe u v w z

noncomputable section

/-- Substitute each propositional atom by the disjunction of labels of worlds where that
atom is true. -/
def labelSubst {W : Type u} {α : Type v} {β : Type w}
    [Fintype W] [DecidableEq W]
    (labels : W → Formula β) (val : W → α → Prop) :
    α → Formula β := by
  classical
  intro p
  exact Formula.disjList (((Finset.univ : Finset W).filter fun w => val w p).toList.map labels)

theorem satisfies_labelSubst_iff_of_exactLabels
    {V : Type u} {W : Type v} {α : Type w} {β : Type z}
    [Fintype W] [DecidableEq W]
    (M : Model V β) (decode : V → W) (labels : W → Formula β) (val : W → α → Prop)
    (hExact : ∀ x w, satisfies M x (labels w) ↔ decode x = w)
    (x : V) (p : α) :
    satisfies M x (labelSubst (W := W) labels val p) ↔ val (decode x) p := by
  unfold labelSubst
  rw [satisfies_disjList_iff]
  constructor
  · rintro ⟨φ, hφ, hSat⟩
    rcases List.mem_map.mp hφ with ⟨w, hw, rfl⟩
    have hw' : w ∈ (Finset.univ : Finset W).filter (fun u => val u p) := by
      simpa using hw
    have hwVal : val w p := (Finset.mem_filter.mp hw').2
    have hDecode : decode x = w := (hExact x w).mp hSat
    simpa [hDecode] using hwVal
  · intro hVal
    refine Exists.intro (labels (decode x)) ?_
    refine And.intro ?_ ((hExact x (decode x)).2 rfl)
    apply List.mem_map.mpr
    refine Exists.intro (decode x) ?_
    refine And.intro ?_ rfl
    simp [hVal]

/-- A finite exact labeling plus successor back/forth transports propositional truth from
an ambient model to the decoded pointed frame. -/
theorem satisfies_subst_iff_of_pointedLabeling
    {V : Type u} {W : Type v} {α : Type w} {β : Type z}
    [Fintype W] [DecidableEq W]
    {F : Frame W}
    (M : Model V β) (decode : V → W) (labels : W → Formula β) (val : W → α → Prop)
    (hExact : ∀ x w, satisfies M x (labels w) ↔ decode x = w)
    (hForward : ∀ x y, M.rel x y → F.rel (decode x) (decode y))
    (hBack : ∀ x w, F.rel (decode x) w → ∃ y, M.rel x y ∧ decode y = w)
    (x : V) (φ : Formula α) :
    satisfies M x (Formula.subst (labelSubst (W := W) labels val) φ) ↔
      satisfies (mkModel F val) (decode x) φ := by
  induction φ generalizing x with
  | var p =>
      simpa [Formula.subst] using
        satisfies_labelSubst_iff_of_exactLabels M decode labels val hExact x p
  | bot =>
      rfl
  | imp φ ψ ihφ ihψ =>
      constructor
      · intro h hφ'
        exact (ihψ _).1 (h ((ihφ _).2 hφ'))
      · intro h hφ'
        exact (ihψ _).2 (h ((ihφ _).1 hφ'))
  | conj φ ψ ihφ ihψ =>
      constructor
      · rintro ⟨hφ, hψ⟩
        exact And.intro ((ihφ _).1 hφ) ((ihψ _).1 hψ)
      · rintro ⟨hφ, hψ⟩
        exact And.intro ((ihφ _).2 hφ) ((ihψ _).2 hψ)
  | disj φ ψ ihφ ihψ =>
      constructor
      · intro h
        rcases h with hφ | hψ
        · exact Or.inl ((ihφ _).1 hφ)
        · exact Or.inr ((ihψ _).1 hψ)
      · intro h
        rcases h with hφ | hψ
        · exact Or.inl ((ihφ _).2 hφ)
        · exact Or.inr ((ihψ _).2 hψ)
  | box φ ih =>
      constructor
      · intro h u hu
        rcases hBack x u hu with ⟨y, hxy, hyu⟩
        have hStep : satisfies M y (Formula.subst (labelSubst (W := W) labels val) φ) := h y hxy
        simpa [hyu] using (ih y).1 hStep
      · intro h y hxy
        exact (ih y).2 (h (decode y) (hForward x y hxy))
  | dia φ ih =>
      constructor
      · rintro ⟨y, hxy, hy⟩
        refine Exists.intro (decode y) ?_
        exact And.intro (hForward x y hxy) ((ih y).1 hy)
      · rintro ⟨u, hu, huSat⟩
        rcases hBack x u hu with ⟨y, hxy, hyu⟩
        have huSat' : satisfies (mkModel F val) (decode y) φ := by
          simpa [hyu] using huSat
        refine Exists.intro y ?_
        refine And.intro hxy ?_
        exact (ih y).2 huSat'

end

end HeytingLean.ModalCategorySets.Validities
