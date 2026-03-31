import HeytingLean.LeanCP.Core.SepLog
import HeytingLean.LeanCP.Core.StateSepLog

/-!
# LeanCP Structural Entailment

Phase 4's entailment layer is intentionally narrow. It exposes only structural
heap/state entailment rules already proved in `SepLog` and `StateSepLog`, plus
an exact-match classifier for cheaply closable obligations. It is not a second
verification semantics and it does not discharge operational/stateful proof
obligations on its own.
-/

namespace HeytingLean.LeanCP

inductive EntailmentDisposition where
  | closed
  | manual
  deriving DecidableEq, Repr, Inhabited

noncomputable def classifyHeapExact (lhs rhs : HProp) : EntailmentDisposition := by
  classical
  exact if lhs = rhs then .closed else .manual

noncomputable def classifyStateExact (lhs rhs : SProp) : EntailmentDisposition := by
  classical
  exact if lhs = rhs then .closed else .manual

theorem heap_entails_refl (P : HProp) : P ⊢ₛ P :=
  SepLog.entails_refl P

theorem heap_entails_emp_left (P : HProp) : (HProp.emp ∗ P) ⊢ₛ P :=
  SepLog.sep_emp_left P

theorem heap_entails_emp_right (P : HProp) : (P ∗ HProp.emp) ⊢ₛ P :=
  SepLog.sep_emp_right P

theorem heap_entails_frame (P Q R : HProp) (h : P ⊢ₛ Q) :
    (P ∗ R) ⊢ₛ (Q ∗ R) :=
  SepLog.frame_rule P Q R h

theorem state_entails_refl (P : SProp) : P ⊢ₛₛ P :=
  StateSepLog.sentails_refl P

theorem state_entails_emp_left (P : SProp) : (SProp.emp ∗ₛ P) ⊢ₛₛ P :=
  StateSepLog.ssep_emp_left P

theorem state_entails_emp_right (P : SProp) : (P ∗ₛ SProp.emp) ⊢ₛₛ P :=
  StateSepLog.ssep_emp_right P

theorem state_entails_frame (P Q R : SProp) (h : P ⊢ₛₛ Q) :
    (P ∗ₛ R) ⊢ₛₛ (Q ∗ₛ R) :=
  StateSepLog.sframe_rule P Q R h

theorem state_entails_of_heap (P Q : HProp) (h : P ⊢ₛ Q) :
    SProp.ofHProp P ⊢ₛₛ SProp.ofHProp Q := by
  intro st hP
  exact h _ hP

theorem state_entails_of_heap_refl (P : HProp) :
    SProp.ofHProp P ⊢ₛₛ SProp.ofHProp P :=
  state_entails_of_heap P P (heap_entails_refl P)

end HeytingLean.LeanCP
