import HeytingLean.ATP.PremiseNucleus

/-!
# PremiseNucleus Sanity Tests

Concrete instantiations verifying that the PremiseNucleus construction
is well-formed and that the key theorems (trivial gap, universal soundness,
commutativity) compute correctly.
-/

namespace HeytingLean.Tests.ATP.PremiseNucleusSanity

open HeytingLean.ATP

/-- Sanity: a trivial premise nucleus (focus = ∅) has empty gap. -/
example : RetrievalSound (PremiseNucleus.trivial Nat) (fun n => n > 0) :=
  trivial_gap_empty Nat _

/-- Sanity: a universal premise nucleus is sound for a total target. -/
example : RetrievalSound (PremiseNucleus.universal Nat) (fun _ => True) :=
  universal_sound_of_total _ (fun _ => trivial)

/-- Sanity: two premise nuclei built from closureByFocus commute. -/
example : (PremiseNucleus.mk "ring" (fun n : Nat => n > 5)).independent
    (PremiseNucleus.mk "group" (fun n : Nat => n % 2 = 0)) :=
  closureByFocus_premise_nuclei_commute _ _

/-- Sanity: the nucleus operator is extensive (P ≤ R P). -/
example (g : Nat) (P : GoalProp Nat) (hP : P g) :
    (PremiseNucleus.mk "test" (fun _ => False)).toNucleus.R P g :=
  Or.inl hP

/-- Sanity: the focus lens is included in the closure (focus ≤ R P). -/
example (g : Nat) (P : GoalProp Nat) (focus : GoalProp Nat) (hF : focus g) :
    (PremiseNucleus.mk "test" focus).toNucleus.R P g :=
  Or.inr hF

end HeytingLean.Tests.ATP.PremiseNucleusSanity
