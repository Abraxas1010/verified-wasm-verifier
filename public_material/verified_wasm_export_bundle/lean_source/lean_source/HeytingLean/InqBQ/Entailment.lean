import HeytingLean.InqBQ.Support

namespace HeytingLean
namespace InqBQ

open Set

variable {sig : Signature}

/-- Semantic entailment for InqBQ. -/
def entails (Γ : Set (Formula sig)) (ψ : Formula sig) : Prop :=
  ∀ (M : InfoModel sig) (s : Set M.W) (g : Assignment M.D),
    (∀ φ, φ ∈ Γ → supports M s g φ) → supports M s g ψ

/-- Validity is entailment from the empty set. -/
def valid (ψ : Formula sig) : Prop :=
  entails (sig := sig) ∅ ψ

/-- Semantic equivalence. -/
def equiv (φ ψ : Formula sig) : Prop :=
  ∀ (M : InfoModel sig) (s : Set M.W) (g : Assignment M.D),
    supports M s g φ ↔ supports M s g ψ

/-- Id-model-restricted entailment. -/
def idEntails (Γ : Set (Formula sig)) (ψ : Formula sig) : Prop :=
  ∀ (M : InfoModel sig), M.isIdModel →
    ∀ (s : Set M.W) (g : Assignment M.D),
      (∀ φ, φ ∈ Γ → supports M s g φ) → supports M s g ψ

/-- Id-model-restricted validity. -/
def idValid (ψ : Formula sig) : Prop :=
  idEntails (sig := sig) ∅ ψ

/-- Id-model-restricted equivalence. -/
def idEquiv (φ ψ : Formula sig) : Prop :=
  ∀ (M : InfoModel sig), M.isIdModel →
    ∀ (s : Set M.W) (g : Assignment M.D),
      supports M s g φ ↔ supports M s g ψ

/-- The rigid-equality bridge sentence `∀x∀y ?(x = y)`, using variables `0` and `1`. -/
def rhoRigidEq : Formula sig :=
  .forall_ 0 (.forall_ 1 (Formula.question (.eq (.var 0) (.var 1))))

theorem idModel_supports_rhoRigidEq
    (M : InfoModel sig) (hid : M.isIdModel) (s : Set M.W) (g : Assignment M.D) :
    supports M s g rhoRigidEq := by
  intro d
  intro e
  by_cases hde : d = e
  · left
    intro w hw
    simpa [rhoRigidEq, Formula.question, denote, hde] using (hid w d e).2 hde
  · right
    intro t ht hEq
    have hte : t = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro w hw
      have hWorld : d = e := by
        have hLoc : M.localEq w d e := by
          simpa [denote] using hEq w hw
        exact (hid w d e).mp hLoc
      exact hde hWorld
    subst hte
    rfl

end InqBQ
end HeytingLean
