import HeytingLean.LambdaIR.Semantics

namespace HeytingLean
namespace LambdaIR

open HeytingLean.Core

namespace Term

/-! ## Renaming / weakening -/

def liftRename {Γ Δ α} (f : ∀ {τ}, Var Γ τ → Var Δ τ) :
    ∀ {τ}, Var (α :: Γ) τ → Var (α :: Δ) τ
  | _, .vz => .vz
  | _, .vs v => .vs (f v)

def rename {Γ Δ τ} (f : ∀ {τ}, Var Γ τ → Var Δ τ) : Term Γ τ → Term Δ τ
  | .var v => .var (f v)
  | .lam (α := α) body =>
      .lam
        (rename (Γ := α :: Γ) (Δ := α :: Δ) (liftRename (α := α) f)
          body)
  | .app g x => .app (rename f g) (rename f x)
  | .pair a b => .pair (rename f a) (rename f b)
  | .fst t => .fst (rename f t)
  | .snd t => .snd (rename f t)
  | .inl t => .inl (rename f t)
  | .inr t => .inr (rename f t)
  | .matchSum (α := α) (β := β) s k₁ k₂ =>
      .matchSum (rename f s)
        (rename (Γ := α :: Γ) (Δ := α :: Δ) (liftRename (α := α) f) k₁)
        (rename (Γ := β :: Γ) (Δ := β :: Δ) (liftRename (α := β) f) k₂)
  | .if_ c t e => .if_ (rename f c) (rename f t) (rename f e)
  | .constNat n => .constNat n
  | .constBool b => .constBool b
  | .primAddNat => .primAddNat
  | .primEqNat => .primEqNat

def weaken {Γ τ α} (t : Term Γ τ) : Term (α :: Γ) τ :=
  rename (Γ := Γ) (Δ := α :: Γ) (fun {τ} (v : Var Γ τ) => Var.vs v) t

/-! ## Substitution -/

def liftSubst {Γ Δ α} (σ : ∀ {τ}, Var Γ τ → Term Δ τ) :
    ∀ {τ}, Var (α :: Γ) τ → Term (α :: Δ) τ
  | _, .vz => .var .vz
  | _, .vs v => weaken (α := α) (σ v)

def subst {Γ Δ τ} (σ : ∀ {τ}, Var Γ τ → Term Δ τ) : Term Γ τ → Term Δ τ
  | .var v => σ v
  | .lam (α := α) body =>
      .lam (subst (Γ := α :: Γ) (Δ := α :: Δ) (liftSubst (α := α) σ) body)
  | .app g x => .app (subst σ g) (subst σ x)
  | .pair a b => .pair (subst σ a) (subst σ b)
  | .fst t => .fst (subst σ t)
  | .snd t => .snd (subst σ t)
  | .inl t => .inl (subst σ t)
  | .inr t => .inr (subst σ t)
  | .matchSum (α := α) (β := β) s k₁ k₂ =>
      .matchSum (subst σ s)
        (subst (Γ := α :: Γ) (Δ := α :: Δ) (liftSubst (α := α) σ) k₁)
        (subst (Γ := β :: Γ) (Δ := β :: Δ) (liftSubst (α := β) σ) k₂)
  | .if_ c t e => .if_ (subst σ c) (subst σ t) (subst σ e)
  | .constNat n => .constNat n
  | .constBool b => .constBool b
  | .primAddNat => .primAddNat
  | .primEqNat => .primEqNat

def subst0 {Γ α τ} (t : Term (α :: Γ) τ) (s : Term Γ α) : Term Γ τ :=
  subst (Γ := α :: Γ) (Δ := Γ)
    (fun {τ} (v : Var (α :: Γ) τ) =>
      match v with
      | .vz => s
      | .vs v' => .var v')
    t

/-! ## A tiny simplifier: constant `if` elimination -/

def simpIfConst : ∀ {Γ τ}, Term Γ τ → Term Γ τ
  | _, _, .var v => .var v
  | _, _, .lam body => .lam (simpIfConst body)
  | _, _, .app f x => .app (simpIfConst f) (simpIfConst x)
  | _, _, .pair a b => .pair (simpIfConst a) (simpIfConst b)
  | _, _, .fst t => .fst (simpIfConst t)
  | _, _, .snd t => .snd (simpIfConst t)
  | _, _, .inl t => .inl (simpIfConst t)
  | _, _, .inr t => .inr (simpIfConst t)
  | _, _, .matchSum s k₁ k₂ =>
      .matchSum (simpIfConst s) (simpIfConst k₁) (simpIfConst k₂)
  | _, _, .if_ c t e =>
      match simpIfConst c with
      | .constBool true => simpIfConst t
      | .constBool false => simpIfConst e
      | c' => .if_ c' (simpIfConst t) (simpIfConst e)
  | _, _, .constNat n => .constNat n
  | _, _, .constBool b => .constBool b
  | _, _, .primAddNat => .primAddNat
  | _, _, .primEqNat => .primEqNat

/-! ## Metrics -/

def size : ∀ {Γ τ}, Term Γ τ → Nat
  | _, _, .var _ => 1
  | _, _, .lam body => size body + 1
  | _, _, .app f x => size f + size x + 1
  | _, _, .pair a b => size a + size b + 1
  | _, _, .fst t => size t + 1
  | _, _, .snd t => size t + 1
  | _, _, .inl t => size t + 1
  | _, _, .inr t => size t + 1
  | _, _, .matchSum s k₁ k₂ => size s + size k₁ + size k₂ + 1
  | _, _, .if_ c t e => size c + size t + size e + 1
  | _, _, .constNat _ => 1
  | _, _, .constBool _ => 1
  | _, _, .primAddNat => 1
  | _, _, .primEqNat => 1

/-! ## Specialization helper (one static Bool argument) -/

private def substEnv {Γ Δ} (σ : ∀ {τ}, Var Γ τ → Term Δ τ) (ρ : Env Δ) : Env Γ :=
  fun {τ} (v : Var Γ τ) => LambdaIR.eval (σ v) ρ

private def renameEnv {Γ Δ} (f : ∀ {τ}, Var Γ τ → Var Δ τ) (ρ : Env Δ) : Env Γ :=
  fun {τ} (v : Var Γ τ) => ρ (f v)

private theorem eval_rename {Γ Δ τ} (t : Term Γ τ)
    (f : ∀ {τ}, Var Γ τ → Var Δ τ) (ρ : Env Δ) :
    LambdaIR.eval (rename f t) ρ = LambdaIR.eval t (renameEnv f ρ) := by
  have renameEnv_liftRename_extend {Γ Δ α}
      (f : ∀ {τ}, Var Γ τ → Var Δ τ) (ρ : Env Δ) (x : InterpTy α) :
      (renameEnv (liftRename (α := α) f) (Core.extendEnv ρ x) : Env (α :: Γ)) =
        (Core.extendEnv (renameEnv f ρ) x : Env (α :: Γ)) := by
    funext τ v
    cases v <;> rfl
  induction t generalizing Δ with
  | var v =>
      simp [rename, renameEnv]
  | lam body ih =>
      funext x
      have ih' := ih (f := liftRename (α := _) f) (ρ := Core.extendEnv ρ x)
      have hEnv :=
        renameEnv_liftRename_extend (f := f) (ρ := ρ) (x := x)
      simpa [rename, LambdaIR.eval, renameEnv, hEnv] using ih'
  | app g x ihG ihX =>
      simp [rename, ihG, ihX]
  | pair a b ihA ihB =>
      simp [rename, ihA, ihB]
  | fst t ih =>
      simp [rename, ih]
  | snd t ih =>
      simp [rename, ih]
  | inl t ih =>
      simp [rename, ih]
  | inr t ih =>
      simp [rename, ih]
  | matchSum s k₁ k₂ ihS ihK₁ ihK₂ =>
      cases hs : LambdaIR.eval s (renameEnv f ρ) with
      | inl a =>
          have hs' : LambdaIR.eval (rename f s) ρ = Sum.inl a := by
            simpa [hs] using (ihS (f := f) (ρ := ρ))
          have hk₁ :=
            ihK₁ (f := liftRename (α := _) f) (ρ := Core.extendEnv ρ a)
          have hEnv :=
            renameEnv_liftRename_extend (f := f) (ρ := ρ) (x := a)
          simp [rename, LambdaIR.eval, hs, hs', hk₁, hEnv]
      | inr b =>
          have hs' : LambdaIR.eval (rename f s) ρ = Sum.inr b := by
            simpa [hs] using (ihS (f := f) (ρ := ρ))
          have hk₂ :=
            ihK₂ (f := liftRename (α := _) f) (ρ := Core.extendEnv ρ b)
          have hEnv :=
            renameEnv_liftRename_extend (f := f) (ρ := ρ) (x := b)
          simp [rename, LambdaIR.eval, hs, hs', hk₂, hEnv]
  | if_ c t e ihC ihT ihE =>
      cases hc : LambdaIR.eval c (renameEnv f ρ) <;>
        simp [rename, ihC, ihT, ihE, hc]
  | constNat n =>
      simp [rename]
  | constBool b =>
      simp [rename]
  | primAddNat =>
      simp [rename]
  | primEqNat =>
      simp [rename]

private theorem substEnv_liftSubst_extend {Γ Δ α}
    (σ : ∀ {τ}, Var Γ τ → Term Δ τ) (ρ : Env Δ) (x : InterpTy α) :
    (substEnv (liftSubst (α := α) σ) (Core.extendEnv ρ x) : Env (α :: Γ)) =
      (Core.extendEnv (substEnv σ ρ) x : Env (α :: Γ)) := by
  funext τ v
  cases v with
  | vz =>
      simp [substEnv, liftSubst, Core.extendEnv]
  | vs v' =>
      have hw :
          LambdaIR.eval (weaken (α := α) (σ v')) (Core.extendEnv ρ x) =
            LambdaIR.eval (σ v') ρ := by
        simpa [weaken, Core.extendEnv] using
          (eval_rename (t := σ v') (f := fun {τ} (v : Var Δ τ) => Var.vs v) (ρ := Core.extendEnv ρ x))
      simpa [substEnv, liftSubst, Core.extendEnv] using hw

private theorem eval_subst {Γ Δ τ} (t : Term Γ τ)
    (σ : ∀ {τ}, Var Γ τ → Term Δ τ) (ρ : Env Δ) :
    LambdaIR.eval (subst σ t) ρ = LambdaIR.eval t (substEnv σ ρ) := by
  induction t generalizing Δ with
  | var v =>
      simp [subst, substEnv]
  | lam body ih =>
      funext x
      have hEnv :=
        substEnv_liftSubst_extend (σ := σ) (ρ := ρ) (x := x)
      simp [subst, ih, hEnv]
  | app g x ihG ihX =>
      simp [subst, ihG, ihX]
  | pair a b ihA ihB =>
      simp [subst, ihA, ihB]
  | fst t ih =>
      simp [subst, ih]
  | snd t ih =>
      simp [subst, ih]
  | inl t ih =>
      simp [subst, ih]
  | inr t ih =>
      simp [subst, ih]
  | matchSum s k₁ k₂ ihS ihK₁ ihK₂ =>
      cases hs : LambdaIR.eval s (substEnv σ ρ) with
      | inl a =>
          have hEnv :=
            substEnv_liftSubst_extend (σ := σ) (ρ := ρ) (x := a)
          have hs' :
              LambdaIR.eval (subst σ s) ρ = Sum.inl a := by
            simpa [hs] using (ihS (σ := σ) (ρ := ρ))
          have hk₁ :=
            ihK₁ (σ := liftSubst (α := _) σ) (ρ := Core.extendEnv ρ a)
          simp [subst, LambdaIR.eval, hs', hs, hk₁, hEnv]
      | inr b =>
          have hEnv :=
            substEnv_liftSubst_extend (σ := σ) (ρ := ρ) (x := b)
          have hs' :
              LambdaIR.eval (subst σ s) ρ = Sum.inr b := by
            simpa [hs] using (ihS (σ := σ) (ρ := ρ))
          have hk₂ :=
            ihK₂ (σ := liftSubst (α := _) σ) (ρ := Core.extendEnv ρ b)
          simp [subst, LambdaIR.eval, hs', hs, hk₂, hEnv]
  | if_ c t e ihC ihT ihE =>
      cases hc : LambdaIR.eval c (substEnv σ ρ) <;> simp [subst, ihC, ihT, ihE, hc]
  | constNat n =>
      simp [subst]
  | constBool b =>
      simp [subst]
  | primAddNat =>
      simp [subst]
  | primEqNat =>
      simp [subst]

private theorem eval_subst0 {Γ α τ} (t : Term (α :: Γ) τ) (s : Term Γ α) (ρ : Env Γ) :
    LambdaIR.eval (subst0 t s) ρ = LambdaIR.eval t (Core.extendEnv ρ (LambdaIR.eval s ρ)) := by
  let σ : ∀ {τ}, Var (α :: Γ) τ → Term Γ τ :=
    fun {τ} v =>
      match v with
      | .vz => s
      | .vs v' => Term.var v'
  have hEnv :
      (substEnv (σ := σ) ρ : Env (α :: Γ)) =
        (Core.extendEnv ρ (LambdaIR.eval s ρ) : Env (α :: Γ)) := by
    funext τ v
    cases v with
    | vz =>
        simp [substEnv, σ, Core.extendEnv]
    | vs v' =>
        simp [substEnv, σ, Core.extendEnv]
  have := eval_subst (t := t) (σ := σ) (ρ := ρ)
  simpa [subst0, σ, hEnv] using this

private theorem eval_simpIfConst {Γ τ} (t : Term Γ τ) (ρ : Env Γ) :
    LambdaIR.eval (simpIfConst t) ρ = LambdaIR.eval t ρ := by
  induction t with
  | var v =>
      simp [simpIfConst]
  | lam body ih =>
      funext x
      simp [simpIfConst, ih]
  | app f x ihF ihX =>
      simp [simpIfConst, ihF, ihX]
  | pair a b ihA ihB =>
      simp [simpIfConst, ihA, ihB]
  | fst t ih =>
      simp [simpIfConst, ih]
  | snd t ih =>
      simp [simpIfConst, ih]
  | inl t ih =>
      simp [simpIfConst, ih]
  | inr t ih =>
      simp [simpIfConst, ih]
  | matchSum s k₁ k₂ ihS ihK₁ ihK₂ =>
      cases hs : LambdaIR.eval s ρ <;> simp [simpIfConst, ihS, ihK₁, ihK₂, hs]
  | if_ c t e ihC ihT ihE =>
      cases hc' : simpIfConst c with
      | constBool b =>
          have hcEval : LambdaIR.eval c ρ = b := by
            simpa [hc'] using (ihC ρ).symm
          cases hb : b <;> simp [simpIfConst, hc', ihT, ihE, hcEval, hb]
      | _ =>
          have hcEval : LambdaIR.eval c ρ = LambdaIR.eval (simpIfConst c) ρ :=
            (ihC ρ).symm
          simp [simpIfConst, hc', ihT, ihE, hcEval]
  | constNat n =>
      simp [simpIfConst]
  | constBool b =>
      simp [simpIfConst]
  | primAddNat =>
      simp [simpIfConst]
  | primEqNat =>
      simp [simpIfConst]

/-- Specialize a Bool→(Nat→Nat) program at a concrete Bool, and simplify constant `if`s. -/
def specializeBoolNatFun (program : Term [] (Ty.arrow Ty.bool (Ty.arrow Ty.nat Ty.nat))) (b : Bool) :
    Term [] (Ty.arrow Ty.nat Ty.nat) :=
  match program with
  | .lam body =>
      simpIfConst (subst0 body (.constBool b))
  | other =>
      -- Fallback (should be rare for well-typed closed programs of this type).
      .app other (.constBool b)

theorem eval_specializeBoolNatFun (program : Term [] (Ty.arrow Ty.bool (Ty.arrow Ty.nat Ty.nat))) (b : Bool) (n : Nat) :
    LambdaIR.evalClosed (.app (specializeBoolNatFun program b) (.constNat n)) =
      LambdaIR.evalClosed (.app (.app program (.constBool b)) (.constNat n)) := by
  cases program with
  | lam body =>
      -- The specialization path substitutes + simplifies.
      have hSub :
          LambdaIR.evalClosed (.app (subst0 body (.constBool b)) (.constNat n)) =
            LambdaIR.evalClosed (.app (.app (.lam body) (.constBool b)) (.constNat n)) := by
        -- `subst0` correctness at `baseEnv`.
        have h0 := eval_subst0 (t := body) (s := (.constBool b)) (ρ := Core.baseEnv)
        -- Turn it into a statement about applying the resulting Nat→Nat function to `n`.
        simpa [LambdaIR.evalClosed, LambdaIR.eval, Core.extendEnv] using congrArg (fun f => f n) h0
      -- Discharge `simpIfConst`.
      have hSimp :
          LambdaIR.evalClosed (.app (simpIfConst (subst0 body (.constBool b))) (.constNat n)) =
            LambdaIR.evalClosed (.app (subst0 body (.constBool b)) (.constNat n)) := by
        simpa [LambdaIR.evalClosed, LambdaIR.eval] using
          congrArg (fun f => f n) (eval_simpIfConst (t := subst0 body (.constBool b)) (ρ := Core.baseEnv))
      simpa [specializeBoolNatFun, LambdaIR.evalClosed, hSub] using hSimp.trans hSub
  | var v =>
      cases v
  | app g x =>
      simp [specializeBoolNatFun, LambdaIR.evalClosed, LambdaIR.eval]
  | fst t =>
      simp [specializeBoolNatFun, LambdaIR.evalClosed, LambdaIR.eval]
  | snd t =>
      simp [specializeBoolNatFun, LambdaIR.evalClosed, LambdaIR.eval]
  | matchSum s k₁ k₂ =>
      simp [specializeBoolNatFun, LambdaIR.evalClosed, LambdaIR.eval]
  | if_ c t e =>
      simp [specializeBoolNatFun, LambdaIR.evalClosed, LambdaIR.eval]

/-- Specialize a Nat→(Nat→Nat) program at a concrete Nat, and simplify constant `if`s. -/
def specializeNatNatFun (program : Term [] (Ty.arrow Ty.nat (Ty.arrow Ty.nat Ty.nat))) (k : Nat) :
    Term [] (Ty.arrow Ty.nat Ty.nat) :=
  match program with
  | .lam body =>
      simpIfConst (subst0 body (.constNat k))
  | other =>
      -- Fallback (should be rare for well-typed closed programs of this type).
      .app other (.constNat k)

theorem eval_specializeNatNatFun (program : Term [] (Ty.arrow Ty.nat (Ty.arrow Ty.nat Ty.nat))) (k : Nat) (n : Nat) :
    LambdaIR.evalClosed (.app (specializeNatNatFun program k) (.constNat n)) =
      LambdaIR.evalClosed (.app (.app program (.constNat k)) (.constNat n)) := by
  cases program with
  | lam body =>
      have hSub :
          LambdaIR.evalClosed (.app (subst0 body (.constNat k)) (.constNat n)) =
            LambdaIR.evalClosed (.app (.app (.lam body) (.constNat k)) (.constNat n)) := by
        have h0 := eval_subst0 (t := body) (s := (.constNat k)) (ρ := Core.baseEnv)
        simpa [LambdaIR.evalClosed, LambdaIR.eval, Core.extendEnv] using congrArg (fun f => f n) h0
      have hSimp :
          LambdaIR.evalClosed (.app (simpIfConst (subst0 body (.constNat k))) (.constNat n)) =
            LambdaIR.evalClosed (.app (subst0 body (.constNat k)) (.constNat n)) := by
        simpa [LambdaIR.evalClosed, LambdaIR.eval] using
          congrArg (fun f => f n) (eval_simpIfConst (t := subst0 body (.constNat k)) (ρ := Core.baseEnv))
      simpa [specializeNatNatFun, LambdaIR.evalClosed, hSub] using hSimp.trans hSub
  | var v =>
      cases v
  | app g x =>
      simp [specializeNatNatFun, LambdaIR.evalClosed, LambdaIR.eval]
  | fst t =>
      simp [specializeNatNatFun, LambdaIR.evalClosed, LambdaIR.eval]
  | snd t =>
      simp [specializeNatNatFun, LambdaIR.evalClosed, LambdaIR.eval]
  | matchSum s k₁ k₂ =>
      simp [specializeNatNatFun, LambdaIR.evalClosed, LambdaIR.eval]
  | if_ c t e =>
      simp [specializeNatNatFun, LambdaIR.evalClosed, LambdaIR.eval]
  | primAddNat =>
      simp [specializeNatNatFun, LambdaIR.evalClosed, LambdaIR.eval]

end Term

end LambdaIR
end HeytingLean
