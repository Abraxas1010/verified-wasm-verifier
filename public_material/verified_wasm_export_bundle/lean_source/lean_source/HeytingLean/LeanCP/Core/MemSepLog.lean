import HeytingLean.LeanCP.Core.MemHProp

/-!
# LeanCP Memory Separation Logic

Structural rules for the block-based `MemHProp` layer.
-/

namespace HeytingLean.LeanCP

/-- Entailment over block-memory propositions. -/
def mentails (P Q : MemHProp) : Prop := ∀ m, P m → Q m

infixl:25 " ⊢ₘ " => mentails

namespace MemSepLog

theorem setBlocks_self (m : Mem) : { m with blocks := m.blocks } = m := by
  cases m
  rfl

theorem sep_comm (P Q : MemHProp) : (P ∗ₘ Q) ⊢ₘ (Q ∗ₘ P) := by
  intro m ⟨b1, b2, hdis, hun, hP, hQ⟩
  have hdis' : Finmap.Disjoint b2 b1 := (Finmap.Disjoint.symm_iff b2 b1).mpr hdis
  refine ⟨b2, b1, hdis', ?_, hQ, hP⟩
  rw [hun, Finmap.union_comm_of_disjoint hdis]

theorem sep_emp_left (P : MemHProp) : (MemHProp.emp ∗ₘ P) ⊢ₘ P := by
  intro m ⟨b1, b2, _hdis, hun, hemp, hP⟩
  have hb1 : b1 = ∅ := by simpa [MemHProp.emp] using hemp
  subst hb1
  simp at hun
  have hm : { m with blocks := b2 } = m := by
    cases m
    cases hun
    rfl
  rw [hm] at hP
  exact hP

theorem emp_sep_left (P : MemHProp) : P ⊢ₘ (MemHProp.emp ∗ₘ P) := by
  intro m hP
  refine ⟨∅, m.blocks, Finmap.disjoint_empty m.blocks, ?_, ?_, ?_⟩
  · simp
  · simp [MemHProp.emp]
  simpa [setBlocks_self m] using hP

theorem sep_mono (P P' Q Q' : MemHProp) (hP : P ⊢ₘ P') (hQ : Q ⊢ₘ Q') :
    (P ∗ₘ Q) ⊢ₘ (P' ∗ₘ Q') := by
  intro m ⟨b1, b2, hdis, hun, hp, hq⟩
  exact ⟨b1, b2, hdis, hun, hP _ hp, hQ _ hq⟩

theorem frame_rule (P Q R : MemHProp) (h : P ⊢ₘ Q) : (P ∗ₘ R) ⊢ₘ (Q ∗ₘ R) :=
  sep_mono P Q R R h (fun _ hR => hR)

theorem mentails_refl (P : MemHProp) : P ⊢ₘ P := by
  intro _ hP
  exact hP

theorem mentails_trans (P Q R : MemHProp) (hPQ : P ⊢ₘ Q) (hQR : Q ⊢ₘ R) : P ⊢ₘ R := by
  intro m hP
  exact hQR _ (hPQ _ hP)

end MemSepLog
end HeytingLean.LeanCP
