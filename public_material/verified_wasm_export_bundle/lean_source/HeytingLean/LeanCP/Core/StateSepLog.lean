import HeytingLean.LeanCP.Core.SProp

/-!
# LeanCP State-Sensitive Separation Logic

Minimal structural rules for the state-sensitive `SProp` layer.
-/

namespace HeytingLean.LeanCP

/-- State-sensitive entailment. -/
def sentails (P Q : SProp) : Prop := ∀ st, P st → Q st

infixl:25 " ⊢ₛₛ " => sentails

namespace StateSepLog

theorem setHeap_self (st : CState) : { st with heap := st.heap } = st := by
  cases st
  rfl

theorem ssep_comm (P Q : SProp) : (P ∗ₛ Q) ⊢ₛₛ (Q ∗ₛ P) := by
  intro st ⟨h1, h2, hdis, hun, hp, hq⟩
  exact ⟨h2, h1, Heap.disjoint_comm.mpr hdis,
    Heap.union_comm_of_disjoint hdis ▸ hun, hq, hp⟩

theorem ssep_assoc (P Q R : SProp) : ((P ∗ₛ Q) ∗ₛ R) ⊢ₛₛ (P ∗ₛ (Q ∗ₛ R)) := by
  intro st ⟨h12, h3, hdis123, hun123, h12pq, hr⟩
  rcases h12pq with ⟨h1, h2, hdis12, hun12, hp, hq⟩
  subst hun12
  have hdis_parts := (Finmap.disjoint_union_left h1 h2 h3).mp hdis123
  have hdis23 : Finmap.Disjoint h2 h3 := hdis_parts.2
  have hdis1_23 : Finmap.Disjoint h1 (h2 ∪ h3) := by
    rw [Finmap.disjoint_union_right]
    exact ⟨hdis12, hdis_parts.1⟩
  refine ⟨h1, h2 ∪ h3, hdis1_23, ?_, hp, h2, h3, hdis23, rfl, hq, hr⟩
  rw [hun123, Heap.union, Heap.union, Heap.union, Finmap.union_assoc]

theorem ssep_emp_left (P : SProp) : (SProp.emp ∗ₛ P) ⊢ₛₛ P := by
  intro st ⟨h1, h2, _hdis, hun, hemp, hp⟩
  have hh1 : h1 = Heap.empty := by
    simpa [SProp.emp] using hemp
  subst h1
  simp [Heap.union, Heap.empty] at hun
  have hst : { st with heap := h2 } = st := by
    cases st
    cases hun
    rfl
  simpa [hst] using hp

theorem ssep_emp_right (P : SProp) : (P ∗ₛ SProp.emp) ⊢ₛₛ P := by
  intro st hpq
  exact ssep_emp_left P st (ssep_comm P SProp.emp st hpq)

theorem emp_ssep_left (P : SProp) : P ⊢ₛₛ (SProp.emp ∗ₛ P) := by
  intro st hp
  refine ⟨Heap.empty, st.heap, Heap.disjoint_empty_left st.heap, ?_, ?_, ?_⟩
  · simp [Heap.union, Heap.empty]
  · rfl
  · simpa using hp

theorem ssep_mono (P P' Q Q' : SProp) (hp : P ⊢ₛₛ P') (hq : Q ⊢ₛₛ Q') :
    (P ∗ₛ Q) ⊢ₛₛ (P' ∗ₛ Q') := by
  intro st ⟨h1, h2, hdis, hun, hph1, hqh2⟩
  exact ⟨h1, h2, hdis, hun, hp _ hph1, hq _ hqh2⟩

theorem sframe_rule (P Q R : SProp) (h : P ⊢ₛₛ Q) : (P ∗ₛ R) ⊢ₛₛ (Q ∗ₛ R) :=
  ssep_mono P Q R R h (fun _ hr => hr)

theorem sentails_refl (P : SProp) : P ⊢ₛₛ P := fun _ hp => hp

theorem sentails_trans (P Q R : SProp) (hpq : P ⊢ₛₛ Q) (hqr : Q ⊢ₛₛ R) : P ⊢ₛₛ R :=
  fun st hp => hqr st (hpq st hp)

end StateSepLog
end HeytingLean.LeanCP
