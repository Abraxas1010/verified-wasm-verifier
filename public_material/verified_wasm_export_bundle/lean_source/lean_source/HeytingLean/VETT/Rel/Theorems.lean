import HeytingLean.VETT.Rel.Basic

/-!
# VETT.Rel.Theorems

Sanity theorems in the strict relation model:

- Yoneda / Co-Yoneda collapse to tautologies about equality (as emphasized in New–Licata).
- Tensor associativity and unit laws are witnessed by explicit pointwise equivalences.
- “Adjunction by hom-iso ↔ unit/counit” holds in the discrete-category setting (graphs of functions).
-/

namespace HeytingLean.VETT.Rel

universe u v w

open RelOps

/-- Pointwise isomorphism of relations (a “profunctor isomorphism” in this strict model). -/
structure RelIso {α : Type u} {β : Type v} (P Q : HRel α β) : Prop where
  iff' : ∀ a b, P a b ↔ Q a b

namespace RelIso

theorem refl {α : Type u} {β : Type v} (P : HRel α β) : RelIso P P :=
  ⟨fun _ _ => Iff.rfl⟩

theorem symm {α : Type u} {β : Type v} {P Q : HRel α β} (i : RelIso P Q) : RelIso Q P :=
  ⟨fun a b => (i.iff' a b).symm⟩

theorem trans {α : Type u} {β : Type v} {P Q R : HRel α β} (i₁ : RelIso P Q) (i₂ : RelIso Q R) :
    RelIso P R :=
  ⟨fun a b => (i₁.iff' a b).trans (i₂.iff' a b)⟩

end RelIso

/-!
## Yoneda / Co-Yoneda as equality tautologies
-/

theorem yoneda_tautology {C : Type u} (P : C → Prop) (x : C) :
    (∀ y, y = x → P y) ↔ P x := by
  constructor
  · intro h
    exact h x rfl
  · intro px y hyx
    simpa [hyx] using px

theorem coYoneda_tautology {C : Type u} (P : C → Prop) (x : C) :
    (∃ y, P y ∧ x = y) ↔ P x := by
  constructor
  · rintro ⟨y, py, hxy⟩
    simpa [hxy] using py
  · intro px
    exact ⟨x, px, rfl⟩

/-!
## Tensor associativity + unit laws (pointwise)
-/

theorem tensor_assoc {A : Type u} {B : Type v} {C : Type w} {D : Type u}
    (P : HRel A B) (Q : HRel B C) (R : HRel C D) :
    RelIso (RelOps.tensor P (RelOps.tensor Q R)) (RelOps.tensor (RelOps.tensor P Q) R) := by
  refine ⟨fun a d => ?_⟩
  constructor
  · rintro ⟨b, pab, ⟨c, qbc, rcd⟩⟩
    exact ⟨c, ⟨b, pab, qbc⟩, rcd⟩
  · rintro ⟨c, ⟨b, pab, qbc⟩, rcd⟩
    exact ⟨b, pab, ⟨c, qbc, rcd⟩⟩

theorem tensor_unit_left {A : Type u} {B : Type v} (P : HRel A B) :
    RelIso (RelOps.tensor (RelOps.unit A) P) P := by
  refine ⟨fun a b => ?_⟩
  constructor
  · rintro ⟨a', haa', pa'b⟩
    simpa [RelOps.unit] using (haa'.symm ▸ pa'b)
  · intro pab
    exact ⟨a, rfl, pab⟩

theorem tensor_unit_right {A : Type u} {B : Type v} (P : HRel A B) :
    RelIso (RelOps.tensor P (RelOps.unit B)) P := by
  refine ⟨fun a b => ?_⟩
  constructor
  · rintro ⟨b', pab', hb'b⟩
    simpa [RelOps.unit] using (hb'b ▸ pab')
  · intro pab
    exact ⟨b, pab, rfl⟩

/-!
## Adjunction equivalence (discrete-category / graph setting)

In discrete categories, homs are equalities. The adjunction condition

  Hom_D (L c) d ≃ Hom_C c (R d)

specializes to: `(L c = d) ↔ (c = R d)`.
This is equivalent to giving a unit `η : c = R (L c)` and counit `ε : L (R d) = d`
with triangle identities (provable by rewriting).
-/

structure AdjunctionIsoGraph {C : Type u} {D : Type v} (L : C → D) (R : D → C) : Prop where
  iso : ∀ c d, (L c = d) ↔ (c = R d)

structure AdjunctionUnitCounit {C : Type u} {D : Type v} (L : C → D) (R : D → C) : Prop where
  η : ∀ c, c = R (L c)
  ε : ∀ d, L (R d) = d
  triangle_L : ∀ c, Eq.trans (congrArg L (η c)) (ε (L c)) = rfl
  triangle_R : ∀ d, Eq.trans (congrArg R (ε d)) (η (R d)) = rfl

namespace AdjunctionUnitCounit

theorem mk_of_eta_eps {C : Type u} {D : Type v} {L : C → D} {R : D → C}
    (η : ∀ c, c = R (L c)) (ε : ∀ d, L (R d) = d) :
    AdjunctionUnitCounit L R := by
  refine ⟨η, ε, ?_, ?_⟩
  · intro _; exact Subsingleton.elim _ _
  · intro _; exact Subsingleton.elim _ _

end AdjunctionUnitCounit

theorem adjunction_equiv {C : Type u} {D : Type v} (L : C → D) (R : D → C) :
    AdjunctionIsoGraph L R ↔ AdjunctionUnitCounit L R := by
  constructor
  · intro h
    have η : ∀ c, c = R (L c) := by
      intro c
      have := (h.iso c (L c)).1 rfl
      simpa using this
    have ε : ∀ d, L (R d) = d := by
      intro d
      have := (h.iso (R d) d).2 rfl
      simpa using this
    exact AdjunctionUnitCounit.mk_of_eta_eps η ε
  · intro h
    refine ⟨fun c d => ?_⟩
    constructor
    · intro hLc
      -- `c = R (L c) = R d`
      calc
        c = R (L c) := h.η c
        _ = R d := by simp [hLc]
    · intro hRc
      -- `L c = L (R d) = d`
      calc
        L c = L (R d) := by simp [hRc]
        _ = d := h.ε d

end HeytingLean.VETT.Rel
