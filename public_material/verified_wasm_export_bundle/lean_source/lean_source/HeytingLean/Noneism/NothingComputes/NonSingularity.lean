import HeytingLean.Numbers.Surreal.NoneistKripke

namespace HeytingLean.Noneism.NothingComputes

open HeytingLean.Noneism
open HeytingLean.Noneism.KripkeProp

abbrev NKWorld := HeytingLean.Numbers.Surreal.NoneistKripke.World
abbrev NKDomainPolicy := HeytingLean.Numbers.Surreal.NoneistKripke.DomainPolicy
abbrev NKAtom := HeytingLean.Numbers.Surreal.NoneistKripke.Atom
abbrev nkModel := HeytingLean.Numbers.Surreal.NoneistKripke.model

/-- Terms are indiscernible at a world when every atomic noneist predicate gives them the same
truth value there. This keeps the existence predicate separate from the descriptive profile.
-/
def IndiscernibleTerms (policy : NKDomainPolicy) (w : NKWorld) (t u : Term) : Prop :=
  ∀ p : NKAtom,
    Forces (nkModel policy) w (.pred p [t]) ↔ Forces (nkModel policy) w (.pred p [u])

/-- “Nothing-like” tokens are exactly the existing terms in the current noneist world. -/
def ExistingNothing (policy : NKDomainPolicy) (w : NKWorld) (t : Term) : Prop :=
  Forces (nkModel policy) w (.eExists t)

/-- Singularity says there is a unique existing token among the indiscernible “Nothing-like”
objects. This is the exact theorem surface needed by the manuscript's slogan.
-/
def SingularNothingAt (policy : NKDomainPolicy) (w : NKWorld) : Prop :=
  ∃ t : Term,
    ExistingNothing policy w t ∧
      ∀ u : Term, ExistingNothing policy w u → IndiscernibleTerms policy w t u → u = t

theorem atomic_profile_independent_of_term (policy : NKDomainPolicy) (w : NKWorld)
    (p : NKAtom) (t u : Term) :
    Forces (nkModel policy) w (.pred p [t]) ↔ Forces (nkModel policy) w (.pred p [u]) := by
  cases p <;> rfl

theorem all_existing_terms_indiscernible (policy : NKDomainPolicy) (w : NKWorld)
    (t u : Term) :
    IndiscernibleTerms policy w t u := by
  intro p
  exact atomic_profile_independent_of_term policy w p t u

theorem existing_var_zero_constant (w : NKWorld) :
    ExistingNothing .constant w (.var 0) := by
  simp [ExistingNothing]

theorem existing_var_one_constant (w : NKWorld) :
    ExistingNothing .constant w (.var 1) := by
  simp [ExistingNothing]

theorem existing_var_zero_varying (w : NKWorld) :
    ExistingNothing .varying w (.var 0) := by
  exact
    (HeytingLean.Numbers.Surreal.NoneistKripke.forces_exists_varying_iff w 0).2 (Nat.zero_le _)

theorem existing_var_one_varying (w : NKWorld) (hStage : 1 ≤ w.stage) :
    ExistingNothing .varying w (.var 1) := by
  exact
    (HeytingLean.Numbers.Surreal.NoneistKripke.forces_exists_varying_iff w 1).2 hStage

theorem var_zero_ne_var_one : (.var 0 : Term) ≠ .var 1 := by
  intro h
  cases h

/-- Exact non-singularity theorem for the constant-domain noneist reading. -/
theorem nothing_not_singular_constant (w : NKWorld) :
    ¬ SingularNothingAt .constant w := by
  intro hSingular
  rcases hSingular with ⟨t, _ht, huniq⟩
  have h0 : (.var 0 : Term) = t := by
    apply huniq
    · exact existing_var_zero_constant w
    · exact all_existing_terms_indiscernible .constant w _ _
  have h1 : (.var 1 : Term) = t := by
    apply huniq
    · exact existing_var_one_constant w
    · exact all_existing_terms_indiscernible .constant w _ _
  have hEq : (.var 0 : Term) = .var 1 := h0.trans h1.symm
  exact var_zero_ne_var_one hEq

/-- Exact non-singularity theorem for the varying-domain noneist reading once the world stage is
large enough to support two distinct existing tokens.
-/
theorem nothing_not_singular_exact (w : NKWorld) (hStage : 1 ≤ w.stage) :
    ¬ SingularNothingAt .varying w := by
  intro hSingular
  rcases hSingular with ⟨t, _ht, huniq⟩
  have h0 : (.var 0 : Term) = t := by
    apply huniq
    · exact existing_var_zero_varying w
    · exact all_existing_terms_indiscernible .varying w _ _
  have h1 : (.var 1 : Term) = t := by
    apply huniq
    · exact existing_var_one_varying w hStage
    · exact all_existing_terms_indiscernible .varying w _ _
  have hEq : (.var 0 : Term) = .var 1 := h0.trans h1.symm
  exact var_zero_ne_var_one hEq

end HeytingLean.Noneism.NothingComputes
