import HeytingLean.Probability.Step

/-!
Kernel-style safety operator on distribution properties:
  Kprob(S)(d) := ∀ d', d ↦* d' → S d'
Monotone, idempotent, meet-preserving (intersection) as in other kernels.
-/

namespace HeytingLean
namespace Probability

open Set

universe u

variable {α : Type u}
variable [Inhabited α]

abbrev DProp (α : Type u) := Dist α → Prop

def Kprob (S : DProp α) : DProp α := fun d => ∀ d', (d ↦* d') → S d'

lemma Kprob_monotone : Monotone (Kprob (α:=α)) := by
  intro S T hST d h; exact fun d' hdd' => hST d' (h d' hdd')

lemma Kprob_idem (S : DProp α) : Kprob (Kprob S) = Kprob S := by
  funext d; apply propext; constructor
  · intro h; intro d' hdd'; have h' := h d' hdd'; exact h' d' (StepStar.refl d')
  · intro h; intro d' hdd'; intro e hde; exact h e (StepStar.trans hdd' hde)

lemma Kprob_meet (S T : DProp α) : Kprob (fun d => S d ∧ T d) = fun d => Kprob S d ∧ Kprob T d := by
  funext d; apply propext; constructor
  · intro h; exact And.intro (fun d' hdd' => (h d' hdd').1) (fun d' hdd' => (h d' hdd').2)
  · intro h d' hdd'; exact And.intro (h.1 d' hdd') (h.2 d' hdd')

end Probability
end HeytingLean
