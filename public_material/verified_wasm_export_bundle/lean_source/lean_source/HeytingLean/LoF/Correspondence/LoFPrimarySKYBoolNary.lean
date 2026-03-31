import HeytingLean.LoF.Correspondence.LoFPrimaryClosedSKYBool

/-!
# LoFPrimarySKYBoolNary — env-free `n`-ary LoFPrimary → SKY Church booleans

`LoFPrimarySKYBool` translates a primary LoF expression under an explicit Boolean environment,
producing a **closed** SKY boolean.

This file removes that scoping: for any `A : LoFPrimary.Expr n`, we build a single SKY term
`toSKYFun A : Comb` which expects `n` Church-boolean arguments and reduces to the canonical
boolean matching `LoFPrimary.eval A ρ`.

Construction idea:
- build an `n`-ary Boolean function as a decision tree on the *first* variable, using the fact that
  a Church boolean `b` is itself an if-then-else selector (`b x y ↦ x` or `↦ y`),
- recurse after specializing the first variable to `true/false` on the LoF side.
-/

namespace HeytingLean
namespace LoF
namespace Correspondence

open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.LoFPrimary

open LoFPrimary.Expr
open StepsLemmas
open SKYBool

namespace LoFPrimary
namespace Expr

/-! ## Specializing the first variable -/

/-- Boolean constants as primary expressions: `false ↦ void`, `true ↦ mark void`. -/
def ofBool {n : Nat} : Bool → Expr n
  | true => Expr.mark Expr.void
  | false => Expr.void

@[simp] theorem eval_ofBool {n : Nat} (b : Bool) (ρ : Fin n → Bool) :
    LoFPrimary.eval (n := n) (ofBool (n := n) b) ρ = b := by
  cases b <;> simp [ofBool, LoFPrimary.eval]

/-- Specialize the **first** variable of an `(n+1)`-variable expression to a Boolean constant. -/
def specialize0 {n : Nat} (b : Bool) : Expr (n + 1) → Expr n
  | .void => .void
  | .var i =>
      Fin.cases (motive := fun _ => Expr n) (ofBool (n := n) b) (fun j => .var j) i
  | .mark A => .mark (specialize0 b A)
  | .juxt A B => .juxt (specialize0 b A) (specialize0 b B)

/-- Extend an environment by providing a value for the first variable. -/
def extendEnv {n : Nat} (b : Bool) (ρ : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.cases (motive := fun _ => Bool) b ρ

theorem extendEnv_head_tail {n : Nat} (ρ : Fin (n + 1) → Bool) :
    extendEnv (n := n) (ρ 0) (fun i => ρ i.succ) = ρ := by
  funext i
  refine Fin.cases (motive := fun i => extendEnv (n := n) (ρ 0) (fun i => ρ i.succ) i = ρ i) ?_
      (fun j => ?_) i <;>
    simp [extendEnv]

theorem eval_specialize0 {n : Nat} (A : Expr (n + 1)) (b : Bool) (ρ : Fin n → Bool) :
    LoFPrimary.eval (n := n) (specialize0 (n := n) b A) ρ =
      LoFPrimary.eval (n := n + 1) A (extendEnv (n := n) b ρ) := by
  induction A with
  | void =>
      simp [specialize0, LoFPrimary.eval]
  | var i =>
      -- Split on whether `i` is the first variable or a successor.
      refine
        Fin.cases
          (motive := fun i : Fin (n + 1) =>
            LoFPrimary.eval (n := n) (specialize0 (n := n) b (.var i)) ρ =
              LoFPrimary.eval (n := n + 1) (.var i) (extendEnv (n := n) b ρ))
          ?_
          (fun j => ?_)
          i
      · simp [specialize0, extendEnv, LoFPrimary.eval]
      · simp [specialize0, extendEnv, LoFPrimary.eval]
  | mark A ih =>
      simp [specialize0, extendEnv, LoFPrimary.eval, ih]
  | juxt A B ihA ihB =>
      simp [specialize0, extendEnv, LoFPrimary.eval, ihA, ihB]

theorem eval_specialize0_head_tail {n : Nat} (A : Expr (n + 1)) (ρ : Fin (n + 1) → Bool) :
    LoFPrimary.eval (n := n) (specialize0 (n := n) (ρ 0) A) (fun i => ρ i.succ) =
      LoFPrimary.eval (n := n + 1) A ρ := by
  have h :=
    eval_specialize0 (n := n) (A := A) (b := ρ 0) (ρ := fun i => ρ i.succ)
  simpa [extendEnv_head_tail (n := n) (ρ := ρ)] using h

end Expr
end LoFPrimary

namespace SKYBool

/-! ## Boolean choice as a combinator -/

/-- `iteFun t f` is the curried combinator `λb. b t f`. -/
def iteFun (t f : Comb) : Comb :=
  let X : Comb := Comb.app (Comb.app .S .I) (Comb.app .K t)   -- `S I (K t)`
  Comb.app (Comb.app .S X) (Comb.app .K f)                   -- `S X (K f)`

theorem iteFun_reduces (b t f : Comb) :
    Comb.Steps (Comb.app (iteFun t f) b) (Comb.app (Comb.app b t) f) := by
  -- Expand `(S X Y) b ↦ X b (Y b)` with `X = S I (K t)`, `Y = K f`.
  let X : Comb := Comb.app (Comb.app .S .I) (Comb.app .K t)
  let Yterm : Comb := Comb.app .K f
  have h1 :
      Comb.Steps (Comb.app (iteFun t f) b) (Comb.app (Comb.app X b) (Comb.app Yterm b)) := by
    refine Comb.Steps.trans ?_ (Comb.Steps.refl _)
    simpa [iteFun, X, Yterm] using Comb.Step.S_rule (x := X) (y := Yterm) (z := b)
  -- Reduce `Y b ↦ f`.
  have hY : Comb.Steps (Comb.app Yterm b) f := by
    refine Comb.Steps.trans ?_ (Comb.Steps.refl _)
    simpa [Yterm] using Comb.Step.K_rule (x := f) (y := b)
  -- Reduce `X b ↦* b t`.
  have hX : Comb.Steps (Comb.app X b) (Comb.app b t) := by
    -- `X b = (S I (K t)) b ↦ I b ((K t) b) ↦ b t`.
    have hX1 :
        Comb.Steps (Comb.app X b)
          (Comb.app (Comb.app .I b) (Comb.app (Comb.app .K t) b)) := by
      refine Comb.Steps.trans ?_ (Comb.Steps.refl _)
      simpa [X] using Comb.Step.S_rule (x := Comb.I) (y := Comb.app Comb.K t) (z := b)
    have hIb : Comb.Steps (Comb.app Comb.I b) b := Comb.I_reduces b
    have hX2 :
        Comb.Steps
          (Comb.app (Comb.app .I b) (Comb.app (Comb.app .K t) b))
          (Comb.app b (Comb.app (Comb.app .K t) b)) :=
      StepsLemmas.steps_app_left (a := Comb.app (Comb.app Comb.K t) b) hIb
    have hKt : Comb.Steps (Comb.app (Comb.app .K t) b) t := by
      refine Comb.Steps.trans ?_ (Comb.Steps.refl _)
      simpa using Comb.Step.K_rule (x := t) (y := b)
    have hX3 :
        Comb.Steps (Comb.app b (Comb.app (Comb.app .K t) b)) (Comb.app b t) :=
      StepsLemmas.steps_app_right (f := b) hKt
    exact StepsLemmas.steps_transitive hX1 (StepsLemmas.steps_transitive hX2 hX3)
  -- Combine reductions under application.
  have h2 :
      Comb.Steps (Comb.app (Comb.app X b) (Comb.app Yterm b)) (Comb.app (Comb.app b t) f) := by
    exact StepsLemmas.steps_congr_app (hf := hX) (ha := hY)
  exact StepsLemmas.steps_transitive h1 h2

theorem iteFun_ofBool (b : Bool) (t f : Comb) :
    Comb.Steps (Comb.app (iteFun t f) (SKYBool.ofBool b)) (if b then t else f) := by
  have h :
      Comb.Steps (Comb.app (iteFun t f) (SKYBool.ofBool b))
        (Comb.app (Comb.app (SKYBool.ofBool b) t) f) :=
    iteFun_reduces (b := SKYBool.ofBool b) (t := t) (f := f)
  cases b with
  | true =>
      exact StepsLemmas.steps_transitive h (SKYBool.tt_select t f)
  | false =>
      exact StepsLemmas.steps_transitive h (SKYBool.ff_select t f)

end SKYBool

namespace LoFPrimarySKYBoolNary

/-! ## Applying `n` arguments -/

def applyArgs : {n : Nat} → Comb → (Fin n → Comb) → Comb
  | 0, t, _ => t
  | n + 1, t, args => applyArgs (n := n) (Comb.app t (args 0)) (fun i => args i.succ)

def applyBools {n : Nat} (t : Comb) (ρ : Fin n → Bool) : Comb :=
  applyArgs (n := n) t (fun i => SKYBool.ofBool (ρ i))

theorem steps_applyArgs {n : Nat} {f g : Comb} (hfg : Comb.Steps f g) (args : Fin n → Comb) :
    Comb.Steps (applyArgs (n := n) f args) (applyArgs (n := n) g args) := by
  induction n generalizing f g with
  | zero =>
      simpa [applyArgs] using hfg
  | succ n ih =>
      have h1 : Comb.Steps (Comb.app f (args 0)) (Comb.app g (args 0)) :=
        StepsLemmas.steps_app_left (a := args 0) hfg
      -- Continue by applying the remaining arguments.
      simpa [applyArgs] using
        ih (f := Comb.app f (args 0)) (g := Comb.app g (args 0)) h1 (args := fun i => args i.succ)

/-! ## Env-free translation -/

def toSKYFun : {n : Nat} → LoFPrimary.Expr n → Comb
  | 0, A => LoFPrimaryClosed.toSKYBool A
  | n + 1, A =>
      SKYBool.iteFun
        (toSKYFun (n := n) (LoFPrimary.Expr.specialize0 (n := n) true A))
        (toSKYFun (n := n) (LoFPrimary.Expr.specialize0 (n := n) false A))

theorem toSKYFun_correct : ∀ {n : Nat} (A : LoFPrimary.Expr n) (ρ : Fin n → Bool),
    Comb.Steps (applyBools (n := n) (toSKYFun (n := n) A) ρ) (SKYBool.ofBool (LoFPrimary.eval A ρ)) := by
  intro n
  induction n with
  | zero =>
      intro A ρ
      have hρ : ρ = SKYBool.env0 := by
        funext i
        exact Fin.elim0 i
      subst hρ
      -- No arguments to apply; reduce to the closed-fragment correctness theorem.
      simpa [applyBools, applyArgs, toSKYFun, LoFPrimaryClosed.eval0] using
        (LoFPrimaryClosed.toSKYBool_correct A)
  | succ n ih =>
      intro A ρ
      let ρtail : Fin n → Bool := fun i => ρ i.succ
      let argsTail : Fin n → Comb := fun i => SKYBool.ofBool (ρtail i)
      -- Unfold once: apply the first argument, then the remaining `n` arguments.
      have hchoose :
          Comb.Steps
            (Comb.app (toSKYFun (n := n + 1) A) (SKYBool.ofBool (ρ 0)))
            (if ρ 0 then
                toSKYFun (n := n) (LoFPrimary.Expr.specialize0 (n := n) true A)
              else
                toSKYFun (n := n) (LoFPrimary.Expr.specialize0 (n := n) false A)) := by
        simpa [toSKYFun] using
          (SKYBool.iteFun_ofBool (b := ρ 0)
            (t := toSKYFun (n := n) (LoFPrimary.Expr.specialize0 (n := n) true A))
            (f := toSKYFun (n := n) (LoFPrimary.Expr.specialize0 (n := n) false A)))

      have hlift :
          Comb.Steps
            (applyArgs (n := n) (Comb.app (toSKYFun (n := n + 1) A) (SKYBool.ofBool (ρ 0))) argsTail)
            (applyArgs (n := n)
              (if ρ 0 then
                  toSKYFun (n := n) (LoFPrimary.Expr.specialize0 (n := n) true A)
                else
                  toSKYFun (n := n) (LoFPrimary.Expr.specialize0 (n := n) false A))
              argsTail) :=
        steps_applyArgs (n := n) hchoose argsTail

      -- Now finish by cases on the first Boolean argument.
      cases h0 : ρ 0 with
      | false =>
          -- Reduce to the `false` branch function, then apply IH.
          have hIH :
              Comb.Steps
                (applyArgs (n := n)
                  (toSKYFun (n := n) (LoFPrimary.Expr.specialize0 (n := n) false A))
                  argsTail)
                (SKYBool.ofBool (LoFPrimary.eval (LoFPrimary.Expr.specialize0 (n := n) false A) ρtail)) :=
            ih (A := LoFPrimary.Expr.specialize0 (n := n) false A) (ρ := ρtail)

          have heval :
              LoFPrimary.eval (LoFPrimary.Expr.specialize0 (n := n) false A) ρtail =
                LoFPrimary.eval A ρ := by
            have h := LoFPrimary.Expr.eval_specialize0_head_tail (n := n) (A := A) (ρ := ρ)
            simpa [h0, ρtail] using h

          have hIH' :
              Comb.Steps
                (applyArgs (n := n)
                  (toSKYFun (n := n) (LoFPrimary.Expr.specialize0 (n := n) false A))
                  argsTail)
                (SKYBool.ofBool (LoFPrimary.eval A ρ)) := by
            exact StepsLemmas.steps_transitive hIH (Comb.Steps.of_eq (by simp [heval]))

          -- Put the pieces together.
          have hstart :
              Comb.Steps
                (applyBools (n := n + 1) (toSKYFun (n := n + 1) A) ρ)
                (applyArgs (n := n)
                  (toSKYFun (n := n) (LoFPrimary.Expr.specialize0 (n := n) false A))
                  argsTail) := by
            -- Unfold `applyBools` and simplify `if` with `h0`.
            simpa [applyBools, applyArgs, ρtail, argsTail, toSKYFun, h0] using hlift

          exact StepsLemmas.steps_transitive hstart hIH'
      | true =>
          -- Reduce to the `true` branch function, then apply IH.
          have hIH :
              Comb.Steps
                (applyArgs (n := n)
                  (toSKYFun (n := n) (LoFPrimary.Expr.specialize0 (n := n) true A))
                  argsTail)
                (SKYBool.ofBool (LoFPrimary.eval (LoFPrimary.Expr.specialize0 (n := n) true A) ρtail)) :=
            ih (A := LoFPrimary.Expr.specialize0 (n := n) true A) (ρ := ρtail)

          have heval :
              LoFPrimary.eval (LoFPrimary.Expr.specialize0 (n := n) true A) ρtail =
                LoFPrimary.eval A ρ := by
            have h := LoFPrimary.Expr.eval_specialize0_head_tail (n := n) (A := A) (ρ := ρ)
            simpa [h0, ρtail] using h

          have hIH' :
              Comb.Steps
                (applyArgs (n := n)
                  (toSKYFun (n := n) (LoFPrimary.Expr.specialize0 (n := n) true A))
                  argsTail)
                (SKYBool.ofBool (LoFPrimary.eval A ρ)) := by
            exact StepsLemmas.steps_transitive hIH (Comb.Steps.of_eq (by simp [heval]))

          have hstart :
              Comb.Steps
                (applyBools (n := n + 1) (toSKYFun (n := n + 1) A) ρ)
                (applyArgs (n := n)
                  (toSKYFun (n := n) (LoFPrimary.Expr.specialize0 (n := n) true A))
                  argsTail) := by
            simpa [applyBools, applyArgs, ρtail, argsTail, toSKYFun, h0] using hlift

          exact StepsLemmas.steps_transitive hstart hIH'

/-! ## LoF rewrite steps are joinable under the SKY Boolean semantics -/

/-- Two SKY terms are joinable if they both reduce to a common term. -/
def Joinable (t u : Comb) : Prop :=
  ∃ w : Comb, Comb.Steps t w ∧ Comb.Steps u w

theorem step_joinable_applyBools {n : Nat} {A B : LoFPrimary.Expr n} (h : LoFPrimary.Step A B)
    (ρ : Fin n → Bool) :
    Joinable (applyBools (n := n) (toSKYFun (n := n) A) ρ) (applyBools (n := n) (toSKYFun (n := n) B) ρ) := by
  refine ⟨SKYBool.ofBool (LoFPrimary.eval A ρ), ?_, ?_⟩
  · exact toSKYFun_correct (n := n) A ρ
  · have hEqv : LoFPrimary.Eqv (n := n) A B :=
      LoFPrimary.step_sound (n := n) h
    have hev : LoFPrimary.eval B ρ = LoFPrimary.eval A ρ := (hEqv ρ).symm
    have hB : Comb.Steps (applyBools (n := n) (toSKYFun (n := n) B) ρ) (SKYBool.ofBool (LoFPrimary.eval B ρ)) :=
      toSKYFun_correct (n := n) B ρ
    exact StepsLemmas.steps_transitive hB (Comb.Steps.of_eq (by simp [hev]))

theorem steps_joinable_applyBools {n : Nat} {A B : LoFPrimary.Expr n} (h : LoFPrimary.Steps A B)
    (ρ : Fin n → Bool) :
    Joinable (applyBools (n := n) (toSKYFun (n := n) A) ρ) (applyBools (n := n) (toSKYFun (n := n) B) ρ) := by
  refine ⟨SKYBool.ofBool (LoFPrimary.eval A ρ), ?_, ?_⟩
  · exact toSKYFun_correct (n := n) A ρ
  · have hEqv : LoFPrimary.Eqv (n := n) A B :=
      LoFPrimary.steps_sound (n := n) h
    have hev : LoFPrimary.eval B ρ = LoFPrimary.eval A ρ := (hEqv ρ).symm
    have hB : Comb.Steps (applyBools (n := n) (toSKYFun (n := n) B) ρ) (SKYBool.ofBool (LoFPrimary.eval B ρ)) :=
      toSKYFun_correct (n := n) B ρ
    exact StepsLemmas.steps_transitive hB (Comb.Steps.of_eq (by simp [hev]))

end LoFPrimarySKYBoolNary

end Correspondence
end LoF
end HeytingLean
