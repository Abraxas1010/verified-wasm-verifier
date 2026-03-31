import HeytingLean.LeanCP.Core.HProp

/-!
# LeanCP Separation Logic

Core separation logic entailment and structural rules.
-/

namespace HeytingLean.LeanCP

/-- Separation logic entailment: P entails Q if Q holds on every heap where P holds. -/
def entails (P Q : HProp) : Prop := ∀ h, P h → Q h

infixl:25 " ⊢ₛ " => entails

namespace SepLog

-- Structural rules for separating conjunction

theorem sep_comm (P Q : HProp) : (P ∗ Q) ⊢ₛ (Q ∗ P) := by
  intro h ⟨h1, h2, hdis, hun, hp, hq⟩
  exact ⟨h2, h1, Heap.disjoint_comm.mpr hdis,
    (Heap.union_comm_of_disjoint hdis ▸ hun), hq, hp⟩

theorem sep_assoc (P Q R : HProp) : ((P ∗ Q) ∗ R) ⊢ₛ (P ∗ (Q ∗ R)) := by
  intro h ⟨h12, h3, hdis123, hun123, ⟨h1, h2, hdis12, hun12, hp, hq⟩, hr⟩
  -- h12 = h1 ∪ h2, h = h12 ∪ h3 = (h1 ∪ h2) ∪ h3
  subst hun12
  -- Disjointness: (h1 ∪ h2) disjoint from h3
  -- Need: h2 disjoint from h3, h1 disjoint from (h2 ∪ h3)
  have hdis_parts := (Finmap.disjoint_union_left h1 h2 h3).mp hdis123
  -- hdis_parts : Disjoint h1 h3 ∧ Disjoint h2 h3
  have hdis_right : Finmap.Disjoint h2 h3 := hdis_parts.2
  have hdis1_23 : Finmap.Disjoint h1 (h2 ∪ h3) := by
    rw [Finmap.disjoint_union_right]
    exact ⟨hdis12, hdis_parts.1⟩
  refine ⟨h1, h2 ∪ h3, hdis1_23, ?_, hp, h2, h3, hdis_right, rfl, hq, hr⟩
  rw [hun123, Heap.union, Heap.union, Heap.union, Finmap.union_assoc]

theorem sep_emp_left (P : HProp) : (HProp.emp ∗ P) ⊢ₛ P := by
  intro h ⟨h1, h2, _, hun, hemp, hp⟩
  rw [HProp.emp] at hemp
  subst hemp
  simp [Heap.union, Heap.empty] at hun
  rw [hun]
  exact hp

theorem sep_emp_right (P : HProp) : (P ∗ HProp.emp) ⊢ₛ P := by
  intro h hpq
  exact sep_emp_left P h (sep_comm P HProp.emp h hpq)

theorem emp_sep_left (P : HProp) : P ⊢ₛ (HProp.emp ∗ P) := by
  intro h hp
  exact ⟨Heap.empty, h, Heap.disjoint_empty_left h,
    by simp [Heap.union, Heap.empty], rfl, hp⟩

theorem sep_mono (P P' Q Q' : HProp) (hp : P ⊢ₛ P') (hq : Q ⊢ₛ Q') :
    (P ∗ Q) ⊢ₛ (P' ∗ Q') := by
  intro h ⟨h1, h2, hdis, hun, hph1, hqh2⟩
  exact ⟨h1, h2, hdis, hun, hp h1 hph1, hq h2 hqh2⟩

-- Frame rule: the key modularity principle of separation logic
theorem frame_rule (P Q R : HProp) (h : P ⊢ₛ Q) : (P ∗ R) ⊢ₛ (Q ∗ R) :=
  sep_mono P Q R R h (fun _ hr => hr)

-- Magic wand adjunction
theorem wand_intro (P Q R : HProp) (h : (P ∗ Q) ⊢ₛ R) : P ⊢ₛ (Q -∗ R) := by
  intro hp hph q hdis hq
  exact h (Heap.union hp q) ⟨hp, q, hdis, rfl, hph, hq⟩

theorem wand_elim (P Q : HProp) : (P ∗ (P -∗ Q)) ⊢ₛ Q := by
  intro h ⟨h1, h2, hdis, hun, hp, hwand⟩
  rw [hun, Heap.union_comm_of_disjoint hdis]
  exact hwand h1 (Heap.disjoint_comm.mpr hdis) hp

-- Entailment is reflexive and transitive
theorem entails_refl (P : HProp) : P ⊢ₛ P := fun _ hp => hp

theorem entails_trans (P Q R : HProp) (hpq : P ⊢ₛ Q) (hqr : Q ⊢ₛ R) : P ⊢ₛ R :=
  fun h hp => hqr h (hpq h hp)

end SepLog
end HeytingLean.LeanCP
