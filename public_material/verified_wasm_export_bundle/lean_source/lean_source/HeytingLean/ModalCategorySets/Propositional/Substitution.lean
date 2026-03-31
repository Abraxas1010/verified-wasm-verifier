import HeytingLean.ModalCategorySets.Propositional.Core

namespace HeytingLean.ModalCategorySets.Propositional

open HeytingLean.Logics.Modal

universe u v w

namespace Formula

variable {α : Type u} {β : Type v}

/-- Substitute formulas for propositional variables. -/
def subst (σ : α → Formula β) : Formula α → Formula β
  | .var p => σ p
  | .bot => .bot
  | .imp φ ψ => .imp (subst σ φ) (subst σ ψ)
  | .conj φ ψ => .conj (subst σ φ) (subst σ ψ)
  | .disj φ ψ => .disj (subst σ φ) (subst σ ψ)
  | .box φ => .box (subst σ φ)
  | .dia φ => .dia (subst σ φ)

/-- Finite conjunction of propositional formulas. -/
def conjList : List (Formula α) → Formula α
  | [] => top
  | φ :: φs => .conj φ (conjList φs)

/-- Finite disjunction of propositional formulas. -/
def disjList : List (Formula α) → Formula α
  | [] => .bot
  | φ :: φs => .disj φ (disjList φs)

end Formula

namespace Model

variable {W : Type u} {α : Type v} {β : Type w}

/-- Reinterpret a `β`-model as an `α`-model by valuing each `α`-atom with the truth
of its substituted formula in the ambient model. -/
def substModel (M : Model W β) (σ : α → Formula β) : Model W α where
  rel := M.rel
  val w p := satisfies M w (σ p)

@[simp] theorem substModel_rel (M : Model W β) (σ : α → Formula β) (x y : W) :
    (substModel M σ).rel x y ↔ M.rel x y := by
  rfl

@[simp] theorem substModel_val (M : Model W β) (σ : α → Formula β) (w : W) (p : α) :
    (substModel M σ).val w p ↔ satisfies M w (σ p) := by
  rfl

end Model

@[simp] theorem satisfies_conjList_iff
    {W : Type u} {α : Type v} (M : Model W α) (x : W) (φs : List (Formula α)) :
    satisfies M x (Formula.conjList φs) ↔ ∀ φ, φ ∈ φs → satisfies M x φ := by
  induction φs with
  | nil =>
      constructor
      · intro _ φ hφ
        cases hφ
      · intro _
        exact fun h => h
  | cons φ φs ih =>
      constructor
      · rintro ⟨hφ, hRest⟩ ψ hψ
        by_cases hEq : ψ = φ
        · subst hEq
          exact hφ
        · have hTail : ψ ∈ φs := by
            simpa [hEq] using hψ
          exact (ih.mp hRest) ψ hTail
      · intro h
        have hHead : φ ∈ φ :: φs := by simp
        refine And.intro (h φ hHead) ?_
        refine ih.mpr ?_
        intro ψ hψ
        exact h ψ (List.mem_cons_of_mem _ hψ)

@[simp] theorem satisfies_disjList_iff
    {W : Type u} {α : Type v} (M : Model W α) (x : W) (φs : List (Formula α)) :
    satisfies M x (Formula.disjList φs) ↔ ∃ φ, φ ∈ φs ∧ satisfies M x φ := by
  induction φs with
  | nil =>
      constructor
      · intro h
        exact False.elim h
      · rintro ⟨φ, hRest⟩
        rcases hRest with ⟨hφ, _⟩
        cases hφ
  | cons φ φs ih =>
      constructor
      · intro h
        rcases h with hφ | hRest
        · refine Exists.intro φ ?_
          exact And.intro (by simp) hφ
        · rcases ih.mp hRest with ⟨ψ, hTail⟩
          rcases hTail with ⟨hψ, hSat⟩
          refine Exists.intro ψ ?_
          exact And.intro (List.mem_cons_of_mem _ hψ) hSat
      · rintro ⟨ψ, hRest⟩
        rcases hRest with ⟨hψ, hSat⟩
        by_cases hEq : ψ = φ
        · subst hEq
          exact Or.inl hSat
        · have hTail : ψ ∈ φs := by
            simpa [hEq] using hψ
          exact Or.inr (ih.mpr (Exists.intro ψ (And.intro hTail hSat)))

@[simp] theorem satisfies_subst_iff
    {W : Type u} {α : Type v} {β : Type w}
    (M : Model W β) (σ : α → Formula β) (x : W) (φ : Formula α) :
    satisfies M x (Formula.subst σ φ) ↔
      satisfies (Model.substModel M σ) x φ := by
  induction φ generalizing x with
  | var p =>
      rfl
  | bot =>
      rfl
  | imp φ ψ ihφ ihψ =>
      constructor
      · intro h hφ'
        exact (ihψ x).1 (h ((ihφ x).2 hφ'))
      · intro h hφ'
        exact (ihψ x).2 (h ((ihφ x).1 hφ'))
  | conj φ ψ ihφ ihψ =>
      constructor
      · rintro ⟨hφ, hψ⟩
        exact And.intro ((ihφ x).1 hφ) ((ihψ x).1 hψ)
      · rintro ⟨hφ, hψ⟩
        exact And.intro ((ihφ x).2 hφ) ((ihψ x).2 hψ)
  | disj φ ψ ihφ ihψ =>
      constructor
      · intro h
        rcases h with hφ | hψ
        · exact Or.inl ((ihφ x).1 hφ)
        · exact Or.inr ((ihψ x).1 hψ)
      · intro h
        rcases h with hφ | hψ
        · exact Or.inl ((ihφ x).2 hφ)
        · exact Or.inr ((ihψ x).2 hψ)
  | box φ ih =>
      constructor
      · intro h v hxv
        exact (ih v).1 (h v hxv)
      · intro h v hxv
        exact (ih v).2 (h v hxv)
  | dia φ ih =>
      constructor
      · rintro ⟨v, hxv, hφ⟩
        exact Exists.intro v (And.intro hxv ((ih v).1 hφ))
      · rintro ⟨v, hxv, hφ⟩
        exact Exists.intro v (And.intro hxv ((ih v).2 hφ))

namespace Frame

variable {W : Type u} {α : Type v} {β : Type w}

/-- Frame validity is closed under propositional substitution. -/
theorem Valid.subst {F : Frame W} {φ : Formula α}
    (hValid : F.Valid φ) (σ : α → Formula β) :
    F.Valid (Formula.subst σ φ) := by
  intro val w
  let M : Model W β := mkModel F val
  have hBase :
      satisfies (Model.substModel M σ) w φ :=
    hValid (fun x p => satisfies M x (σ p)) w
  exact (satisfies_subst_iff M σ w φ).2 hBase

end Frame

end HeytingLean.ModalCategorySets.Propositional
