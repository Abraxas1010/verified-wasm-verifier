import HeytingLean.InqBQ.Entailment

namespace HeytingLean
namespace InqBQ

open Set

variable {sig : Signature}

/-- Worldwise truth for the classical fragment. -/
def worldSatisfies (M : InfoModel sig) (w : M.W) (g : Assignment M.D) : Formula sig → Prop
  | .pred P ts =>
      M.predInterp w P (fun i => denote M w g (ts i))
  | .eq t u =>
      M.localEq w (denote M w g t) (denote M w g u)
  | .bot =>
      False
  | .conj φ ψ =>
      worldSatisfies M w g φ ∧ worldSatisfies M w g ψ
  | .inqDisj φ ψ =>
      worldSatisfies M w g φ ∨ worldSatisfies M w g ψ
  | .imp φ ψ =>
      worldSatisfies M w g φ → worldSatisfies M w g ψ
  | .forall_ x φ =>
      ∀ d : M.D, worldSatisfies M w (Assignment.update g x d) φ
  | .inqExists x φ =>
      ∃ d : M.D, worldSatisfies M w (Assignment.update g x d) φ

/-- Truth-conditionality expressed by worldwise support. -/
def truthConditional (φ : Formula sig) : Prop :=
  ∀ (M : InfoModel sig) (s : Set M.W) (g : Assignment M.D),
    supports M s g φ ↔ ∀ w, w ∈ s → worldSatisfies M w g φ

/-- Worldwise entailment notion for the classical fragment. -/
def classicallyEntails (Γ : Set (Formula sig)) (ψ : Formula sig) : Prop :=
  ∀ (M : InfoModel sig) (w : M.W) (g : Assignment M.D),
    (∀ φ, φ ∈ Γ → worldSatisfies M w g φ) → worldSatisfies M w g ψ

/-- A theory is classical if every formula in it is classical. -/
def TheoryIsClassical (Γ : Set (Formula sig)) : Prop :=
  ∀ φ, φ ∈ Γ → Formula.isClassical φ

theorem classical_support_iff_worldwise (M : InfoModel sig) (g : Assignment M.D) :
    ∀ {φ : Formula sig}, Formula.isClassical φ →
      ∀ {s : Set M.W}, supports M s g φ ↔ ∀ w, w ∈ s → worldSatisfies M w g φ
  | .pred _ _, _, s => by
      rfl
  | .eq _ _, _, s => by
      rfl
  | .bot, _, s => by
      constructor
      · intro hs w hw
        subst hs
        simpa using hw
      · intro h
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro w hw
        exact h w hw
  | .conj φ ψ, hClass, s => by
      rcases hClass with ⟨hφ, hψ⟩
      constructor
      · intro h w hw
        exact ⟨(classical_support_iff_worldwise M g hφ).1 h.1 w hw,
          (classical_support_iff_worldwise M g hψ).1 h.2 w hw⟩
      · intro h
        refine ⟨?_, ?_⟩
        · apply (classical_support_iff_worldwise M g hφ).2
          intro w hw
          exact (h w hw).1
        · apply (classical_support_iff_worldwise M g hψ).2
          intro w hw
          exact (h w hw).2
  | .inqDisj _ _, hClass, s => by
      cases hClass
  | .imp φ ψ, hClass, s => by
      rcases hClass with ⟨hφ, hψ⟩
      constructor
      · intro h w hw hsat
        have hφSingleton : supports M ({w} : Set M.W) g φ := by
          apply (classical_support_iff_worldwise M g hφ).2
          intro w' hw'
          have hw'Eq : w' = w := by simpa using hw'
          simpa [hw'Eq] using hsat
        have hψSingleton := h ({w}) (by
          intro w' hw'
          have hw'Eq : w' = w := by simpa using hw'
          simpa [hw'Eq] using hw) hφSingleton
        have hwSingleton : w ∈ ({w} : Set M.W) := by
          change w = w
          rfl
        exact
          (classical_support_iff_worldwise M g (φ := ψ) hψ).1 hψSingleton w
            hwSingleton
      · intro h
        intro t ht hSupp
        apply (classical_support_iff_worldwise M g hψ).2
        intro w hw
        have hWorldImp := h w (ht hw)
        have hWorldφ := (classical_support_iff_worldwise M g hφ).1 hSupp w hw
        exact hWorldImp hWorldφ
  | .forall_ x φ, hClass, s => by
      constructor
      · intro h w hw d
        exact
          (classical_support_iff_worldwise (M := M) (g := Assignment.update g x d)
            (φ := φ) hClass (s := s)).1 (h d) w hw
      · intro h
        intro d
        apply
          (classical_support_iff_worldwise (M := M) (g := Assignment.update g x d)
            (φ := φ) hClass (s := s)).2
        intro w hw
        exact h w hw d
  | .inqExists _ _, hClass, s => by
      cases hClass

theorem classical_truth (M : InfoModel sig) (w : M.W) (g : Assignment M.D)
    {φ : Formula sig} (hClass : Formula.isClassical φ) :
    holdsAt M w g φ ↔ worldSatisfies M w g φ := by
  constructor
  · intro h
    have hwSingleton : w ∈ ({w} : Set M.W) := by
      change w = w
      rfl
    exact
      (classical_support_iff_worldwise M g (φ := φ) hClass (s := ({w} : Set M.W))).1 h w
        hwSingleton
  · intro h
    apply (classical_support_iff_worldwise M g (φ := φ) hClass (s := ({w} : Set M.W))).2
    intro w' hw'
    have hw'Eq : w' = w := by simpa using hw'
    simpa [hw'Eq] using h

theorem classical_truthConditional {φ : Formula sig} (hClass : Formula.isClassical φ) :
    truthConditional φ := by
  intro M s g
  exact classical_support_iff_worldwise M g hClass

theorem classical_conservativity {Γ : Set (Formula sig)} {ψ : Formula sig}
    (hΓ : TheoryIsClassical Γ) (hψ : Formula.isClassical ψ) :
    entails Γ ψ ↔ classicallyEntails Γ ψ := by
  constructor
  · intro hEnt M w g hWorld
    have hSuppΓ : ∀ φ, φ ∈ Γ → supports M ({w} : Set M.W) g φ := by
      intro φ hφ
      exact (classical_support_iff_worldwise M g (hΓ φ hφ)).2 (by
        intro w' hw'
        have hw'Eq : w' = w := by simpa using hw'
        simpa [hw'Eq] using hWorld φ hφ)
    have hSuppΨ := hEnt M ({w} : Set M.W) g hSuppΓ
    have hwSingleton : w ∈ ({w} : Set M.W) := by
      change w = w
      rfl
    exact
      (classical_support_iff_worldwise M g (φ := ψ) hψ).1 hSuppΨ w
        hwSingleton
  · intro hClass M s g hSuppΓ
    apply (classical_support_iff_worldwise M g hψ).2
    intro w hw
    apply hClass M w g
    intro φ hφ
    exact (classical_support_iff_worldwise M g (hΓ φ hφ)).1 (hSuppΓ φ hφ) w hw

end InqBQ
end HeytingLean
