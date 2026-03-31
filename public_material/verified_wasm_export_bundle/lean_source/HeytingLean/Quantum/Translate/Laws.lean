import HeytingLean.Quantum.Translate.Core
import HeytingLean.Quantum.Translate.Omega

open scoped Classical

namespace HeytingLean.Quantum.Translate

open HeytingLean.Quantum.OML

variable {β α : Type _}
variable [OrthocomplementedLattice β] [OrthomodularLattice β]
variable [CompleteLattice α]

/-- Quantum-flavoured Occam reduction: translate and apply the modality once. -/
def qOccam (T : QLMap β α) (a : β) : α :=
  T.M.J (T.tr a)

/-- Quantum-flavoured PSR predicate: the translation is already a fixed point of the modality. -/
def qPSR (T : QLMap β α) (a : β) : Prop :=
  T.M.J (T.tr a) = T.tr a

/-- Dialectic-style synthesis: close the join of a thesis and antithesis under the modality. -/
def qDialectic (T : QLMap β α) (t a : β) : α :=
  T.M.J (T.tr t ⊔ T.tr a)

@[simp] lemma qPSR_iff (T : QLMap β α) (a : β) :
    qPSR T a ↔ T.M.J (T.tr a) = T.tr a := Iff.rfl

@[simp] lemma qDialectic_comm (T : QLMap β α) (t a : β) :
    qDialectic T t a = qDialectic T a t := by
  simp [qDialectic, sup_comm]

end HeytingLean.Quantum.Translate
