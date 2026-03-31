import HeytingLean.Noneism.ProofTheory.ND
import HeytingLean.Noneism.ProofTheory.Quantifiers.Hygiene
import HeytingLean.Noneism.Semantics.KripkeFO

/-!
# Noneism.ProofTheory.Soundness.KripkeFO

Soundness of the ND proof system `Noneism.ProofTheory.ND.Derives` with respect to the Kripke
semantics in `Noneism.Semantics.KripkeFO`.

This is the first-order-ish analogue of `Soundness.KripkeProp`:
- we keep `pred` and `eExists` as atoms, but allow them to depend on interpreted term values;
- we interpret `sigma/pi` quantifiers using a **constant domain** `D`;
- we prove that all ND rules, including the explicit eigenvariable side-conditions, are sound.
-/

namespace HeytingLean
namespace Noneism

open scoped Classical

open Formula

namespace KripkeFO

open KripkeFO

variable {σ : Type}

/-! ## Persistence (monotonicity in the world preorder) -/

theorem forces_mono {W : Type} [Preorder W] {D : Type} (M : Model W σ D) :
    ∀ (ρ : Valuation D) {w v : W}, w ≤ v → ∀ {φ : Formula σ}, Forces M ρ w φ → Forces M ρ v φ := by
  intro ρ w v hwv φ
  induction φ generalizing ρ w v with
  | top =>
      intro _; trivial
  | bot =>
      intro h; cases h
  | pred p args =>
      intro h
      exact M.monoPred hwv p (args.map (evalTerm ρ)) h
  | eExists t =>
      intro h
      exact M.monoEx hwv (evalTerm ρ t) h
  | not φ ih =>
      intro hNot u hvu huφ
      have hwu : w ≤ u := le_trans hwv hvu
      exact hNot u hwu huφ
  | and φ ψ ihφ ihψ =>
      intro hAnd
      exact And.intro
        (ihφ (ρ := ρ) (w := w) (v := v) hwv hAnd.1)
        (ihψ (ρ := ρ) (w := w) (v := v) hwv hAnd.2)
  | or φ ψ ihφ ihψ =>
      intro hOr
      cases hOr with
      | inl h => exact Or.inl (ihφ (ρ := ρ) (w := w) (v := v) hwv h)
      | inr h => exact Or.inr (ihψ (ρ := ρ) (w := w) (v := v) hwv h)
  | imp φ ψ ihφ ihψ =>
      intro hImp u hvu huφ
      have hwu : w ≤ u := le_trans hwv hvu
      exact hImp u hwu huφ
  | sigma x φ ih =>
      rintro ⟨d, hd⟩
      exact ⟨d, ih (ρ := update ρ x d) hwv hd⟩
  | pi x φ ih =>
      intro hPi u hvu d
      have hwu : w ≤ u := le_trans hwv hvu
      exact hPi u hwu d

/-! ## Valuation update invariance (eigenvariable reasoning) -/

theorem evalTerm_update_of_ne {D} (ρ : Valuation D) (y : Var) (d : D) :
    ∀ t : Term, y ∉ Syntax.fvTerm t → evalTerm (update ρ y d) t = evalTerm ρ t := by
  intro t ht
  cases t with
  | var x =>
      simp [Syntax.fvTerm] at ht
      simp [evalTerm, update, Ne.symm ht]

theorem evalTerms_update_of_ne {D} (ρ : Valuation D) (y : Var) (d : D) :
    ∀ ts : List Term, y ∉ Syntax.fvTerms ts →
      (ts.map (evalTerm (update ρ y d))) = (ts.map (evalTerm ρ)) := by
  intro ts hts
  induction ts with
  | nil => simp
  | cons t ts ih =>
      simp [Syntax.fvTerms, Finset.mem_union] at hts
      have ht : y ∉ Syntax.fvTerm t := by
        intro hy; exact hts.1 hy
      have hts' : y ∉ Syntax.fvTerms ts := by
        intro hy; exact hts.2 hy
      simp [evalTerm_update_of_ne (ρ := ρ) (y := y) (d := d) t ht, ih hts']

theorem forces_update_of_not_mem_fvFormula {W : Type} [Preorder W] {D : Type}
    (M : Model W σ D) (ρ : Valuation D) (y : Var) (d : D) :
    ∀ φ : Formula σ, y ∉ Syntax.fvFormula φ →
      ∀ w : W, Forces M (update ρ y d) w φ ↔ Forces M ρ w φ := by
  intro φ
  induction φ generalizing ρ with
  | top =>
      intro _ w
      simp [Forces]
  | bot =>
      intro _ w
      simp [Forces]
  | pred p args =>
      intro hy w
      have hy' : y ∉ Syntax.fvTerms args := by
        simpa [Syntax.fvFormula] using hy
      have hmap := evalTerms_update_of_ne (ρ := ρ) (y := y) (d := d) args hy'
      simp [Forces, hmap]
  | eExists t =>
      intro hy w
      have hy' : y ∉ Syntax.fvTerm t := by
        simpa [Syntax.fvFormula] using hy
      have hterm := evalTerm_update_of_ne (ρ := ρ) (y := y) (d := d) t hy'
      simp [Forces, hterm]
  | not φ ih =>
      intro hy w
      have hy' : y ∉ Syntax.fvFormula φ := hy
      constructor
      · intro h v hwv hvφ
        have : Forces M (update ρ y d) v φ := (ih (ρ := ρ) hy' v).2 hvφ
        exact h v hwv this
      · intro h v hwv hvφ
        have : Forces M ρ v φ := (ih (ρ := ρ) hy' v).1 hvφ
        exact h v hwv this
  | and φ ψ ihφ ihψ =>
      intro hy w
      have hy' : y ∉ Syntax.fvFormula φ ∧ y ∉ Syntax.fvFormula ψ := by
        simpa [Syntax.fvFormula, Finset.mem_union] using hy
      have hyφ : y ∉ Syntax.fvFormula φ := hy'.1
      have hyψ : y ∉ Syntax.fvFormula ψ := hy'.2
      simp [Forces, ihφ (ρ := ρ) hyφ w, ihψ (ρ := ρ) hyψ w]
  | or φ ψ ihφ ihψ =>
      intro hy w
      have hy' : y ∉ Syntax.fvFormula φ ∧ y ∉ Syntax.fvFormula ψ := by
        simpa [Syntax.fvFormula, Finset.mem_union] using hy
      have hyφ : y ∉ Syntax.fvFormula φ := hy'.1
      have hyψ : y ∉ Syntax.fvFormula ψ := hy'.2
      simp [Forces, ihφ (ρ := ρ) hyφ w, ihψ (ρ := ρ) hyψ w]
  | imp φ ψ ihφ ihψ =>
      intro hy w
      have hy' : y ∉ Syntax.fvFormula φ ∧ y ∉ Syntax.fvFormula ψ := by
        simpa [Syntax.fvFormula, Finset.mem_union] using hy
      have hyφ : y ∉ Syntax.fvFormula φ := hy'.1
      have hyψ : y ∉ Syntax.fvFormula ψ := hy'.2
      constructor
      · intro h v hwv hvφ
        have hvφ' : Forces M (update ρ y d) v φ := (ihφ (ρ := ρ) hyφ v).2 hvφ
        have hvψ' : Forces M (update ρ y d) v ψ := h v hwv hvφ'
        exact (ihψ (ρ := ρ) hyψ v).1 hvψ'
      · intro h v hwv hvφ
        have hvφ' : Forces M ρ v φ := (ihφ (ρ := ρ) hyφ v).1 hvφ
        have hvψ' : Forces M ρ v ψ := h v hwv hvφ'
        exact (ihψ (ρ := ρ) hyψ v).2 hvψ'
  | sigma x φ ih =>
      intro hy w
      by_cases hxy : y = x
      · subst hxy
        constructor
        · rintro ⟨e, he⟩
          -- `update` at `x` is overwritten by the witness anyway.
          refine ⟨e, ?_⟩
          simpa [update_update_same] using he
        · rintro ⟨e, he⟩
          refine ⟨e, ?_⟩
          simpa [update_update_same] using he
      ·
        have hyErase : y ∉ (Syntax.fvFormula φ).erase x := by
          simpa [Syntax.fvFormula] using hy
        have hy' : y ∉ Syntax.fvFormula φ := by
          intro hyMem
          exact hyErase (Finset.mem_erase.2 ⟨hxy, hyMem⟩)
        constructor
        · rintro ⟨e, he⟩
          have hcomm : update (update ρ y d) x e = update (update ρ x e) y d := by
            simp [update_comm (ρ := ρ) (dx := e) (dy := d) (h := Ne.symm hxy)]
          have he' : Forces M (update (update ρ x e) y d) w φ := by
            simpa [hcomm] using he
          have : Forces M (update ρ x e) w φ :=
            (ih (ρ := update ρ x e) hy' w).1 he'
          exact ⟨e, this⟩
        · rintro ⟨e, he⟩
          have he' : Forces M (update (update ρ x e) y d) w φ :=
            (ih (ρ := update ρ x e) hy' w).2 he
          have hcomm : update (update ρ y d) x e = update (update ρ x e) y d := by
            simp [update_comm (ρ := ρ) (dx := e) (dy := d) (h := Ne.symm hxy)]
          exact ⟨e, by simpa [hcomm] using he'⟩
  | pi x φ ih =>
      intro hy w
      by_cases hxy : y = x
      · subst hxy
        constructor
        · intro h v hwv e
          -- `update` at `x` is overwritten by the witness anyway.
          simpa [update_update_same] using h v hwv e
        · intro h v hwv e
          simpa [update_update_same] using h v hwv e
      ·
        have hyErase : y ∉ (Syntax.fvFormula φ).erase x := by
          simpa [Syntax.fvFormula] using hy
        have hy' : y ∉ Syntax.fvFormula φ := by
          intro hyMem
          exact hyErase (Finset.mem_erase.2 ⟨hxy, hyMem⟩)
        constructor
        · intro h v hwv e
          have hv : Forces M (update (update ρ y d) x e) v φ := h v hwv e
          have hcomm : update (update ρ y d) x e = update (update ρ x e) y d := by
            simp [update_comm (ρ := ρ) (dx := e) (dy := d) (h := Ne.symm hxy)]
          have hv' : Forces M (update (update ρ x e) y d) v φ := by simpa [hcomm] using hv
          exact (ih (ρ := update ρ x e) hy' v).1 hv'
        · intro h v hwv e
          have hv : Forces M (update ρ x e) v φ := h v hwv e
          have hv' : Forces M (update (update ρ x e) y d) v φ := (ih (ρ := update ρ x e) hy' v).2 hv
          have hcomm : update (update ρ y d) x e = update (update ρ x e) y d := by
            simp [update_comm (ρ := ρ) (dx := e) (dy := d) (h := Ne.symm hxy)]
          simpa [hcomm] using hv'

theorem forces_update_of_not_mem_varsFormula {W : Type} [Preorder W] {D : Type}
    (M : Model W σ D) (ρ : Valuation D) (y : Var) (d : D) (w : W) :
    ∀ φ : Formula σ, y ∉ Syntax.varsFormula (σ := σ) φ →
      (Forces M (update ρ y d) w φ ↔ Forces M ρ w φ) := by
  intro φ
  exact fun hy => by
    have hy' : y ∉ Syntax.fvFormula (σ := σ) φ :=
      Syntax.not_mem_fvFormula_of_not_mem_varsFormula (σ := σ) (a := y) (φ := φ) hy
    exact forces_update_of_not_mem_fvFormula (σ := σ) (M := M) (ρ := ρ) (y := y) (d := d) φ hy' w

/-! ## Substitution lemma (specialized to `x ↦ var a`) -/

theorem forces_substFormula_var_of_not_mem_boundVars {W : Type} [Preorder W] {D : Type}
    (M : Model W σ D) (ρ : Valuation D) (w : W) :
    ∀ (x a : Var) (φ : Formula σ),
      a ∉ Syntax.boundVars (σ := σ) φ →
        (Forces M ρ w (Syntax.substFormula (σ := σ) x (.var a) φ) ↔
          Forces M (update ρ x (ρ a)) w φ) := by
  intro x a φ ha
  induction φ generalizing ρ w with
  | top =>
      simp [Syntax.substFormula, Forces]
  | bot =>
      simp [Syntax.substFormula, Forces]
  | pred p args =>
      have hEq :
          List.map (evalTerm ρ ∘ Syntax.substTerm x (.var a)) args =
            List.map (evalTerm (update ρ x (ρ a))) args := by
        apply List.map_congr_left
        intro t ht
        cases t with
        | var z =>
            by_cases hzx : z = x <;> simp [Syntax.substTerm, evalTerm, update, hzx]
      simp [Syntax.substFormula, Forces, Syntax.substTerms, hEq]
  | eExists t =>
      cases t with
      | var z =>
          by_cases hzx : z = x <;> simp [Syntax.substFormula, Forces, Syntax.substTerm, evalTerm, update, hzx]
  | not φ ih =>
      have haφ : a ∉ Syntax.boundVars (σ := σ) φ := by
        simpa [Syntax.boundVars] using ha
      constructor
      · intro h
        have hNot : ∀ v, w ≤ v → Forces M ρ v (Syntax.substFormula (σ := σ) x (.var a) φ) → False := by
          simpa [Syntax.substFormula, Forces] using h
        intro v hwv hvφ
        have : Forces M ρ v (Syntax.substFormula (σ := σ) x (.var a) φ) :=
          (ih (ρ := ρ) (w := v) haφ).2 hvφ
        exact hNot v hwv this
      · intro h
        have hNot : ∀ v, w ≤ v → Forces M (update ρ x (ρ a)) v φ → False := by
          simpa [Forces] using h
        -- Unfold the goal to a `∀ v ≥ w, ...` statement to avoid relying on definitional unfolding
        -- of `Syntax.substFormula`.
        have : Forces M ρ w (.not (Syntax.substFormula (σ := σ) x (.var a) φ)) := by
          intro v hwv hvSub
          have hvφ : Forces M (update ρ x (ρ a)) v φ :=
            (ih (ρ := ρ) (w := v) haφ).1 hvSub
          exact hNot v hwv hvφ
        simpa [Syntax.substFormula, Forces] using this
  | and φ ψ ihφ ihψ =>
      have ha' : a ∉ Syntax.boundVars (σ := σ) φ ∧ a ∉ Syntax.boundVars (σ := σ) ψ := by
        simpa [Syntax.boundVars, Finset.mem_union] using ha
      simp [Syntax.substFormula, Forces, ihφ (ρ := ρ) (w := w) ha'.1, ihψ (ρ := ρ) (w := w) ha'.2]
  | or φ ψ ihφ ihψ =>
      have ha' : a ∉ Syntax.boundVars (σ := σ) φ ∧ a ∉ Syntax.boundVars (σ := σ) ψ := by
        simpa [Syntax.boundVars, Finset.mem_union] using ha
      simp [Syntax.substFormula, Forces, ihφ (ρ := ρ) (w := w) ha'.1, ihψ (ρ := ρ) (w := w) ha'.2]
  | imp φ ψ ihφ ihψ =>
      have ha' : a ∉ Syntax.boundVars (σ := σ) φ ∧ a ∉ Syntax.boundVars (σ := σ) ψ := by
        simpa [Syntax.boundVars, Finset.mem_union] using ha
      constructor
      · intro h
        have hImp :
            ∀ v, w ≤ v →
              Forces M ρ v (Syntax.substFormula (σ := σ) x (.var a) φ) →
                Forces M ρ v (Syntax.substFormula (σ := σ) x (.var a) ψ) := by
          simpa [Syntax.substFormula, Forces] using h
        intro v hwv hvφ
        have hvφ' : Forces M ρ v (Syntax.substFormula (σ := σ) x (.var a) φ) :=
          (ihφ (ρ := ρ) (w := v) ha'.1).2 hvφ
        have hvψ' : Forces M ρ v (Syntax.substFormula (σ := σ) x (.var a) ψ) := hImp v hwv hvφ'
        exact (ihψ (ρ := ρ) (w := v) ha'.2).1 hvψ'
      · intro h
        have hImp : ∀ v, w ≤ v → Forces M (update ρ x (ρ a)) v φ → Forces M (update ρ x (ρ a)) v ψ := by
          simpa [Forces] using h
        have : Forces M ρ w (.imp (Syntax.substFormula (σ := σ) x (.var a) φ)
            (Syntax.substFormula (σ := σ) x (.var a) ψ)) := by
          intro v hwv hvSubφ
          have hvφ : Forces M (update ρ x (ρ a)) v φ :=
            (ihφ (ρ := ρ) (w := v) ha'.1).1 hvSubφ
          have hvψ : Forces M (update ρ x (ρ a)) v ψ := hImp v hwv hvφ
          exact (ihψ (ρ := ρ) (w := v) ha'.2).2 hvψ
        simpa [Syntax.substFormula, Forces] using this
  | sigma z φ ih =>
      have ha' : a ≠ z ∧ a ∉ Syntax.boundVars (σ := σ) φ := by
        simpa [Syntax.boundVars, Finset.mem_insert, Finset.mem_union] using ha
      have haz : a ≠ z := ha'.1
      have haφ : a ∉ Syntax.boundVars (σ := σ) φ := ha'.2
      by_cases hzx : z = x
      · subst hzx
        -- substitution stops under binder for `x`; update at `x` is overwritten
        simp [Syntax.substFormula, Forces, update_update_same]
      ·
        have hza : z ≠ a := Ne.symm haz
        have hfvt : z ∉ Syntax.fvTerm (.var a) := by
          simp [Syntax.fvTerm, hza]
        simp [Syntax.substFormula, hzx, hfvt, Forces]
        constructor
        · rintro ⟨d, hd⟩
          refine ⟨d, ?_⟩
          have hih := ih (ρ := update ρ z d) (w := w) haφ
          have hb : Forces M (update (update ρ z d) x ((update ρ z d) a)) w φ := hih.1 hd
          have hza' : update ρ z d a = ρ a := by simp [update, haz]
          have hb' : Forces M (update (update ρ z d) x (ρ a)) w φ := by simpa [hza'] using hb
          have hcomm : update (update ρ z d) x (ρ a) = update (update ρ x (ρ a)) z d := by
            simpa using (update_comm (ρ := ρ) (x := z) (y := x) (dx := d) (dy := ρ a) hzx)
          simpa [hcomm] using hb'
        · rintro ⟨d, hd⟩
          refine ⟨d, ?_⟩
          have hih := ih (ρ := update ρ z d) (w := w) haφ
          have hcomm : update (update ρ x (ρ a)) z d = update (update ρ z d) x (ρ a) := by
            simpa using (update_comm (ρ := ρ) (x := z) (y := x) (dx := d) (dy := ρ a) hzx).symm
          have hd' : Forces M (update (update ρ z d) x (ρ a)) w φ := by
            simpa [hcomm] using hd
          have hza' : update ρ z d a = ρ a := by simp [update, haz]
          have hd'' : Forces M (update (update ρ z d) x ((update ρ z d) a)) w φ := by
            simpa [hza'] using hd'
          exact hih.2 hd''
  | pi z φ ih =>
      have ha' : a ≠ z ∧ a ∉ Syntax.boundVars (σ := σ) φ := by
        simpa [Syntax.boundVars, Finset.mem_insert, Finset.mem_union] using ha
      have haz : a ≠ z := ha'.1
      have haφ : a ∉ Syntax.boundVars (σ := σ) φ := ha'.2
      by_cases hzx : z = x
      · subst hzx
        simp [Syntax.substFormula, Forces, update_update_same]
      ·
        have hza : z ≠ a := Ne.symm haz
        have hfvt : z ∉ Syntax.fvTerm (.var a) := by
          simp [Syntax.fvTerm, hza]
        simp [Syntax.substFormula, hzx, hfvt, Forces]
        constructor
        · intro h v hwv d
          have hih := ih (ρ := update ρ z d) (w := v) haφ
          have hb : Forces M (update (update ρ z d) x ((update ρ z d) a)) v φ := hih.1 (h v hwv d)
          have hza' : update ρ z d a = ρ a := by simp [update, haz]
          have hb' : Forces M (update (update ρ z d) x (ρ a)) v φ := by simpa [hza'] using hb
          have hcomm : update (update ρ z d) x (ρ a) = update (update ρ x (ρ a)) z d := by
            simpa using (update_comm (ρ := ρ) (x := z) (y := x) (dx := d) (dy := ρ a) hzx)
          simpa [hcomm] using hb'
        · intro h v hwv d
          have hih := ih (ρ := update ρ z d) (w := v) haφ
          have hcomm : update (update ρ x (ρ a)) z d = update (update ρ z d) x (ρ a) := by
            simpa using (update_comm (ρ := ρ) (x := z) (y := x) (dx := d) (dy := ρ a) hzx).symm
          have hb : Forces M (update (update ρ z d) x (ρ a)) v φ := by
            simpa [hcomm] using h v hwv d
          have hza' : update ρ z d a = ρ a := by simp [update, haz]
          have hb' : Forces M (update (update ρ z d) x ((update ρ z d) a)) v φ := by
            simpa [hza'] using hb
          exact hih.2 hb'

theorem forces_substFormula_var_of_not_mem_varsFormula {W : Type} [Preorder W] {D : Type}
    (M : Model W σ D) (ρ : Valuation D) (w : W) :
    ∀ (x a : Var) (φ : Formula σ),
      a ∉ Syntax.varsFormula (σ := σ) φ →
        (Forces M ρ w (Syntax.substFormula (σ := σ) x (.var a) φ) ↔
          Forces M (update ρ x (ρ a)) w φ) := by
  intro x a φ ha
  exact forces_substFormula_var_of_not_mem_boundVars (σ := σ) (M := M) (ρ := ρ) (w := w)
    x a φ (Syntax.not_mem_boundVars_of_not_mem_varsFormula (σ := σ) ha)

set_option linter.unusedVariables false

theorem _root_.HeytingLean.Noneism.KripkeFO.forces_renameFormula_of_not_mem_varsFormula : ∀ {σ W : Type}
  [inst : Preorder.{0} W] {D : Type} (M : @HeytingLean.Noneism.KripkeFO.Model W σ D inst)
  (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (x y : HeytingLean.Noneism.Var) (φ : HeytingLean.Noneism.Formula σ),
  Not
      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
        (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y) →
    ∀ (w : W),
      Iff (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w φ) :=
fun {σ W : Type} [inst : Preorder.{0} W] {D : Type} (M : @HeytingLean.Noneism.KripkeFO.Model W σ D inst)
    (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (x y : HeytingLean.Noneism.Var)
    (φ : HeytingLean.Noneism.Formula σ) =>
  @HeytingLean.Noneism.Formula.rec.{0} σ
    (fun (φ : HeytingLean.Noneism.Formula σ) =>
      ∀ (ρ : HeytingLean.Noneism.KripkeFO.Valuation D),
        Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y) →
          ∀ (w : W),
            Iff
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
                φ))
    (fun (ρ : HeytingLean.Noneism.KripkeFO.Valuation D)
        (_hy :
          Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@HeytingLean.Noneism.Syntax.varsFormula σ (@HeytingLean.Noneism.Formula.top σ)) y))
        (w : W) =>
      @of_eq_true (Iff True True) (iff_self True))
    (fun (ρ : HeytingLean.Noneism.KripkeFO.Valuation D)
        (_hy :
          Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@HeytingLean.Noneism.Syntax.varsFormula σ (@HeytingLean.Noneism.Formula.bot σ)) y))
        (w : W) =>
      @of_eq_true (Iff False False) (iff_self False))
    (fun (p : σ) (args : List.{0} HeytingLean.Noneism.Term) (ρ : HeytingLean.Noneism.KripkeFO.Valuation D)
        (_hy :
          Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@HeytingLean.Noneism.Syntax.varsFormula σ (@HeytingLean.Noneism.Formula.pred σ p args)) y))
        (w : W) =>
      have hMap :
        @Eq.{1} (List.{0} D)
          (@List.map.{0, 0} HeytingLean.Noneism.Term D
            (@Function.comp.{1, 1, 1} HeytingLean.Noneism.Term HeytingLean.Noneism.Term D
              (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ) (HeytingLean.Noneism.Syntax.renameTerm x y))
            args)
          (@List.map.{0, 0} HeytingLean.Noneism.Term D
            (@HeytingLean.Noneism.KripkeFO.evalTerm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y))) args) :=
        @List.map_congr_left.{0, 0} HeytingLean.Noneism.Term args D
          (@Function.comp.{1, 1, 1} HeytingLean.Noneism.Term HeytingLean.Noneism.Term D
            (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ) (HeytingLean.Noneism.Syntax.renameTerm x y))
          (@HeytingLean.Noneism.KripkeFO.evalTerm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)))
          fun (t : HeytingLean.Noneism.Term)
            (ht :
              @Membership.mem.{0, 0} HeytingLean.Noneism.Term (List.{0} HeytingLean.Noneism.Term)
                (@List.instMembership.{0} HeytingLean.Noneism.Term) args t) =>
          @HeytingLean.Noneism.Term.casesOn.{0}
            (fun (t_1 : HeytingLean.Noneism.Term) =>
              ∀ (h : @Eq.{1} HeytingLean.Noneism.Term t t_1),
                @Eq.{1} D
                  (@Function.comp.{1, 1, 1} HeytingLean.Noneism.Term HeytingLean.Noneism.Term D
                    (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ) (HeytingLean.Noneism.Syntax.renameTerm x y) t)
                  (@HeytingLean.Noneism.KripkeFO.evalTerm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) t))
            t
            (fun (z : HeytingLean.Noneism.Var)
                (h : @Eq.{1} HeytingLean.Noneism.Term t (HeytingLean.Noneism.Term.var z)) =>
              @Eq.ndrec.{0, 1} HeytingLean.Noneism.Term (HeytingLean.Noneism.Term.var z)
                (fun (t : HeytingLean.Noneism.Term) =>
                  ∀
                    (ht :
                      @Membership.mem.{0, 0} HeytingLean.Noneism.Term (List.{0} HeytingLean.Noneism.Term)
                        (@List.instMembership.{0} HeytingLean.Noneism.Term) args t),
                    @Eq.{1} D
                      (@Function.comp.{1, 1, 1} HeytingLean.Noneism.Term HeytingLean.Noneism.Term D
                        (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ) (HeytingLean.Noneism.Syntax.renameTerm x y) t)
                      (@HeytingLean.Noneism.KripkeFO.evalTerm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) t))
                (fun
                    (ht :
                      @Membership.mem.{0, 0} HeytingLean.Noneism.Term (List.{0} HeytingLean.Noneism.Term)
                        (@List.instMembership.{0} HeytingLean.Noneism.Term) args (HeytingLean.Noneism.Term.var z)) =>
                  @dite.{0}
                    (@Eq.{1} D
                      (@Function.comp.{1, 1, 1} HeytingLean.Noneism.Term HeytingLean.Noneism.Term D
                        (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ) (HeytingLean.Noneism.Syntax.renameTerm x y)
                        (HeytingLean.Noneism.Term.var z))
                      (@HeytingLean.Noneism.KripkeFO.evalTerm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y))
                        (HeytingLean.Noneism.Term.var z)))
                    (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x)
                    (fun (hzx : @Eq.{1} HeytingLean.Noneism.Var z x) =>
                      @of_eq_true
                        (@Eq.{1} D
                          (@Function.comp.{1, 1, 1} HeytingLean.Noneism.Term HeytingLean.Noneism.Term D
                            (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ) (HeytingLean.Noneism.Syntax.renameTerm x y)
                            (HeytingLean.Noneism.Term.var z))
                          (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ y) (ρ z)))
                        (@Eq.trans.{1} Prop
                          (@Eq.{1} D
                            (@Function.comp.{1, 1, 1} HeytingLean.Noneism.Term HeytingLean.Noneism.Term D
                              (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ) (HeytingLean.Noneism.Syntax.renameTerm x y)
                              (HeytingLean.Noneism.Term.var z))
                            (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ y) (ρ z)))
                          (@Eq.{1} D (ρ (HeytingLean.Noneism.Term.var y).1) (ρ y)) True
                          (@congr.{1, 1} D Prop
                            (@Eq.{1} D
                              (@Function.comp.{1, 1, 1} HeytingLean.Noneism.Term HeytingLean.Noneism.Term D
                                (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ) (HeytingLean.Noneism.Syntax.renameTerm x y)
                                (HeytingLean.Noneism.Term.var z)))
                            (@Eq.{1} D (ρ (HeytingLean.Noneism.Term.var y).1))
                            (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ y) (ρ z))
                            (ρ y)
                            (@congrArg.{1, 1} D (D → Prop)
                              (@Function.comp.{1, 1, 1} HeytingLean.Noneism.Term HeytingLean.Noneism.Term D
                                (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ) (HeytingLean.Noneism.Syntax.renameTerm x y)
                                (HeytingLean.Noneism.Term.var z))
                              (ρ (HeytingLean.Noneism.Term.var y).1) (@Eq.{1} D)
                              (@Eq.trans.{1} D
                                (@Function.comp.{1, 1, 1} HeytingLean.Noneism.Term HeytingLean.Noneism.Term D
                                  (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ)
                                  (HeytingLean.Noneism.Syntax.renameTerm x y) (HeytingLean.Noneism.Term.var z))
                                (@Function.comp.{1, 1, 1} HeytingLean.Noneism.Term HeytingLean.Noneism.Term D
                                  (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ)
                                  (HeytingLean.Noneism.Syntax.renameTerm x y) (HeytingLean.Noneism.Term.var x))
                                (ρ (HeytingLean.Noneism.Term.var y).1)
                                (@congrArg.{1, 1} HeytingLean.Noneism.Var D z x
                                  (fun (x_1 : HeytingLean.Noneism.Var) =>
                                    @Function.comp.{1, 1, 1} HeytingLean.Noneism.Term HeytingLean.Noneism.Term D
                                      (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ)
                                      (HeytingLean.Noneism.Syntax.renameTerm x y) (HeytingLean.Noneism.Term.var x_1))
                                  hzx)
                                (@congrArg.{1, 1} HeytingLean.Noneism.Var D
                                  (HeytingLean.Noneism.Syntax.renameTerm x y (HeytingLean.Noneism.Term.var x)).1
                                  (HeytingLean.Noneism.Term.var y).1 ρ
                                  (@Eq.ndrec.{0, 1} HeytingLean.Noneism.Term
                                    (@ite.{1} HeytingLean.Noneism.Term (@Eq.{1} HeytingLean.Noneism.Var x x)
                                      (instDecidableEqNat x x) (HeytingLean.Noneism.Term.var y)
                                      (HeytingLean.Noneism.Term.var x))
                                    (fun (s : HeytingLean.Noneism.Term) =>
                                      @Eq.{1} HeytingLean.Noneism.Var
                                        (HeytingLean.Noneism.Syntax.renameTerm x y (HeytingLean.Noneism.Term.var x)).1
                                        s.1)
                                    (@Eq.refl.{1} HeytingLean.Noneism.Var
                                      (HeytingLean.Noneism.Syntax.renameTerm x y (HeytingLean.Noneism.Term.var x)).1)
                                    (HeytingLean.Noneism.Term.var y)
                                    (@ite_cond_eq_true.{1} HeytingLean.Noneism.Term
                                      (@Eq.{1} HeytingLean.Noneism.Var x x) (instDecidableEqNat x x)
                                      (HeytingLean.Noneism.Term.var y) (HeytingLean.Noneism.Term.var x)
                                      (@eq_self.{1} HeytingLean.Noneism.Var x))))))
                            (@ite_cond_eq_true.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x)
                              (ρ y) (ρ z)
                              (@Eq.trans.{1} Prop (@Eq.{1} HeytingLean.Noneism.Var z x)
                                (@Eq.{1} HeytingLean.Noneism.Var x x) True
                                (@congrArg.{1, 1} HeytingLean.Noneism.Var Prop z x
                                  (fun (x_1 : HeytingLean.Noneism.Var) => @Eq.{1} HeytingLean.Noneism.Var x_1 x) hzx)
                                (@eq_self.{1} HeytingLean.Noneism.Var x))))
                          (@eq_self.{1} D (ρ y))))
                    fun (hzx : Not (@Eq.{1} HeytingLean.Noneism.Var z x)) =>
                    @of_eq_true
                      (@Eq.{1} D (ρ (HeytingLean.Noneism.Syntax.renameTerm x y (HeytingLean.Noneism.Term.var z)).1)
                        (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ y) (ρ z)))
                      (@Eq.trans.{1} Prop
                        (@Eq.{1} D (ρ (HeytingLean.Noneism.Syntax.renameTerm x y (HeytingLean.Noneism.Term.var z)).1)
                          (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ y) (ρ z)))
                        (@Eq.{1} D (ρ (HeytingLean.Noneism.Term.var z).1) (ρ z)) True
                        (@congr.{1, 1} D Prop
                          (@Eq.{1} D (ρ (HeytingLean.Noneism.Syntax.renameTerm x y (HeytingLean.Noneism.Term.var z)).1))
                          (@Eq.{1} D (ρ (HeytingLean.Noneism.Term.var z).1))
                          (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ y) (ρ z)) (ρ z)
                          (@congrArg.{1, 1} HeytingLean.Noneism.Var (D → Prop)
                            (HeytingLean.Noneism.Syntax.renameTerm x y (HeytingLean.Noneism.Term.var z)).1
                            (HeytingLean.Noneism.Term.var z).1 (fun (x : HeytingLean.Noneism.Var) => @Eq.{1} D (ρ x))
                            (@Eq.ndrec.{0, 1} HeytingLean.Noneism.Term
                              (@ite.{1} HeytingLean.Noneism.Term (@Eq.{1} HeytingLean.Noneism.Var z x)
                                (instDecidableEqNat z x) (HeytingLean.Noneism.Term.var y)
                                (HeytingLean.Noneism.Term.var z))
                              (fun (s : HeytingLean.Noneism.Term) =>
                                @Eq.{1} HeytingLean.Noneism.Var
                                  (HeytingLean.Noneism.Syntax.renameTerm x y (HeytingLean.Noneism.Term.var z)).1 s.1)
                              (@Eq.refl.{1} HeytingLean.Noneism.Var
                                (HeytingLean.Noneism.Syntax.renameTerm x y (HeytingLean.Noneism.Term.var z)).1)
                              (HeytingLean.Noneism.Term.var z)
                              (@ite_cond_eq_false.{1} HeytingLean.Noneism.Term (@Eq.{1} HeytingLean.Noneism.Var z x)
                                (instDecidableEqNat z x) (HeytingLean.Noneism.Term.var y)
                                (HeytingLean.Noneism.Term.var z)
                                (@eq_false (@Eq.{1} HeytingLean.Noneism.Var z x) hzx))))
                          (@ite_cond_eq_false.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ y)
                            (ρ z) (@eq_false (@Eq.{1} HeytingLean.Noneism.Var z x) hzx)))
                        (@eq_self.{1} D (ρ z))))
                t (@Eq.symm.{1} HeytingLean.Noneism.Term t (HeytingLean.Noneism.Term.var z) h) ht)
            (@Eq.refl.{1} HeytingLean.Noneism.Term t);
      @of_eq_true
        (Iff
          (@HeytingLean.Noneism.KripkeFO.Model.valPred W σ D inst M w p
            (@List.map.{0, 0} HeytingLean.Noneism.Term D (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ)
              (@List.map.{0, 0} HeytingLean.Noneism.Term HeytingLean.Noneism.Term
                (HeytingLean.Noneism.Syntax.renameTerm x y) args)))
          (@HeytingLean.Noneism.KripkeFO.Model.valPred W σ D inst M w p
            (@List.map.{0, 0} HeytingLean.Noneism.Term D
              (@HeytingLean.Noneism.KripkeFO.evalTerm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y))) args)))
        (@Eq.trans.{1} Prop
          (Iff
            (@HeytingLean.Noneism.KripkeFO.Model.valPred W σ D inst M w p
              (@List.map.{0, 0} HeytingLean.Noneism.Term D (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ)
                (@List.map.{0, 0} HeytingLean.Noneism.Term HeytingLean.Noneism.Term
                  (HeytingLean.Noneism.Syntax.renameTerm x y) args)))
            (@HeytingLean.Noneism.KripkeFO.Model.valPred W σ D inst M w p
              (@List.map.{0, 0} HeytingLean.Noneism.Term D
                (@HeytingLean.Noneism.KripkeFO.evalTerm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y))) args)))
          (Iff
            (@HeytingLean.Noneism.KripkeFO.Model.valPred W σ D inst M w p
              (@List.map.{0, 0} HeytingLean.Noneism.Term D
                (@HeytingLean.Noneism.KripkeFO.evalTerm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y))) args))
            (@HeytingLean.Noneism.KripkeFO.Model.valPred W σ D inst M w p
              (@List.map.{0, 0} HeytingLean.Noneism.Term D
                (@HeytingLean.Noneism.KripkeFO.evalTerm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y))) args)))
          True
          (@congrArg.{1, 1} (List.{0} D) Prop
            (@List.map.{0, 0} HeytingLean.Noneism.Term D (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ)
              (@List.map.{0, 0} HeytingLean.Noneism.Term HeytingLean.Noneism.Term
                (HeytingLean.Noneism.Syntax.renameTerm x y) args))
            (@List.map.{0, 0} HeytingLean.Noneism.Term D
              (@HeytingLean.Noneism.KripkeFO.evalTerm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y))) args)
            (fun (x_1 : List.{0} D) =>
              Iff (@HeytingLean.Noneism.KripkeFO.Model.valPred W σ D inst M w p x_1)
                (@HeytingLean.Noneism.KripkeFO.Model.valPred W σ D inst M w p
                  (@List.map.{0, 0} HeytingLean.Noneism.Term D
                    (@HeytingLean.Noneism.KripkeFO.evalTerm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)))
                    args)))
            (@Eq.trans.{1} (List.{0} D)
              (@List.map.{0, 0} HeytingLean.Noneism.Term D (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ)
                (@List.map.{0, 0} HeytingLean.Noneism.Term HeytingLean.Noneism.Term
                  (HeytingLean.Noneism.Syntax.renameTerm x y) args))
              (@List.map.{0, 0} HeytingLean.Noneism.Term D
                (@Function.comp.{1, 1, 1} HeytingLean.Noneism.Term HeytingLean.Noneism.Term D
                  (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ) (HeytingLean.Noneism.Syntax.renameTerm x y))
                args)
              (@List.map.{0, 0} HeytingLean.Noneism.Term D
                (@HeytingLean.Noneism.KripkeFO.evalTerm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y))) args)
              (@List.map_map.{0, 0, 0} HeytingLean.Noneism.Term D HeytingLean.Noneism.Term
                (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ) (HeytingLean.Noneism.Syntax.renameTerm x y) args)
              hMap))
          (iff_self
            (@HeytingLean.Noneism.KripkeFO.Model.valPred W σ D inst M w p
              (@List.map.{0, 0} HeytingLean.Noneism.Term D
                (@HeytingLean.Noneism.KripkeFO.evalTerm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y))) args)))))
    (fun (t : HeytingLean.Noneism.Term) (ρ : HeytingLean.Noneism.KripkeFO.Valuation D)
        (_hy :
          Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@HeytingLean.Noneism.Syntax.varsFormula σ (@HeytingLean.Noneism.Formula.eExists σ t)) y))
        (w : W) =>
      @HeytingLean.Noneism.Term.casesOn.{0}
        (fun (t_1 : HeytingLean.Noneism.Term) =>
          ∀ (h : @Eq.{1} HeytingLean.Noneism.Term t t_1),
            Iff
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.eExists σ t)))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
                (@HeytingLean.Noneism.Formula.eExists σ t)))
        t
        (fun (z : HeytingLean.Noneism.Var) (h : @Eq.{1} HeytingLean.Noneism.Term t (HeytingLean.Noneism.Term.var z)) =>
          @Eq.ndrec.{0, 1} HeytingLean.Noneism.Term (HeytingLean.Noneism.Term.var z)
            (fun (t : HeytingLean.Noneism.Term) =>
              ∀
                (_hy :
                  Not
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ (@HeytingLean.Noneism.Formula.eExists σ t)) y)),
                Iff
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.eExists σ t)))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y))
                    w (@HeytingLean.Noneism.Formula.eExists σ t)))
            (fun
                (_hy :
                  Not
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ
                        (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var z)))
                      y)) =>
              @dite.{0}
                (Iff
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y
                      (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var z))))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y))
                    w (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var z))))
                (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x)
                (fun (hzx : @Eq.{1} HeytingLean.Noneism.Var z x) =>
                  @of_eq_true
                    (Iff
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                        (@HeytingLean.Noneism.Formula.eExists σ
                          (@ite.{1} HeytingLean.Noneism.Term (@Eq.{1} HeytingLean.Noneism.Var z x)
                            (instDecidableEqNat z x) (HeytingLean.Noneism.Term.var y)
                            (HeytingLean.Noneism.Term.var z))))
                      (@HeytingLean.Noneism.KripkeFO.Model.valEx W σ D inst M w
                        (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ y) (ρ z))))
                    (@Eq.trans.{1} Prop
                      (Iff
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                          (@HeytingLean.Noneism.Formula.eExists σ
                            (@ite.{1} HeytingLean.Noneism.Term (@Eq.{1} HeytingLean.Noneism.Var z x)
                              (instDecidableEqNat z x) (HeytingLean.Noneism.Term.var y)
                              (HeytingLean.Noneism.Term.var z))))
                        (@HeytingLean.Noneism.KripkeFO.Model.valEx W σ D inst M w
                          (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ y) (ρ z))))
                      (Iff
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                          (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var y)))
                        (@HeytingLean.Noneism.KripkeFO.Model.valEx W σ D inst M w (ρ y)))
                      True
                      (@congr.{1, 1} Prop Prop
                        (Iff
                          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                            (@HeytingLean.Noneism.Formula.eExists σ
                              (@ite.{1} HeytingLean.Noneism.Term (@Eq.{1} HeytingLean.Noneism.Var z x)
                                (instDecidableEqNat z x) (HeytingLean.Noneism.Term.var y)
                                (HeytingLean.Noneism.Term.var z)))))
                        (Iff
                          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                            (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var y))))
                        (@HeytingLean.Noneism.KripkeFO.Model.valEx W σ D inst M w
                          (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ y) (ρ z)))
                        (@HeytingLean.Noneism.KripkeFO.Model.valEx W σ D inst M w (ρ y))
                        (@congrArg.{1, 1} HeytingLean.Noneism.Term ((b : Prop) → Prop)
                          (@ite.{1} HeytingLean.Noneism.Term (@Eq.{1} HeytingLean.Noneism.Var z x)
                            (instDecidableEqNat z x) (HeytingLean.Noneism.Term.var y) (HeytingLean.Noneism.Term.var z))
                          (HeytingLean.Noneism.Term.var y)
                          (fun (x : HeytingLean.Noneism.Term) =>
                            Iff
                              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                                (@HeytingLean.Noneism.Formula.eExists σ x)))
                          (@ite_cond_eq_true.{1} HeytingLean.Noneism.Term (@Eq.{1} HeytingLean.Noneism.Var z x)
                            (instDecidableEqNat z x) (HeytingLean.Noneism.Term.var y) (HeytingLean.Noneism.Term.var z)
                            (@Eq.trans.{1} Prop (@Eq.{1} HeytingLean.Noneism.Var z x)
                              (@Eq.{1} HeytingLean.Noneism.Var x x) True
                              (@congrArg.{1, 1} HeytingLean.Noneism.Var Prop z x
                                (fun (x_1 : HeytingLean.Noneism.Var) => @Eq.{1} HeytingLean.Noneism.Var x_1 x) hzx)
                              (@eq_self.{1} HeytingLean.Noneism.Var x))))
                        (@congrArg.{1, 1} D Prop
                          (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ y) (ρ z)) (ρ y)
                          (@HeytingLean.Noneism.KripkeFO.Model.valEx W σ D inst M w)
                          (@ite_cond_eq_true.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ y)
                            (ρ z)
                            (@Eq.trans.{1} Prop (@Eq.{1} HeytingLean.Noneism.Var z x)
                              (@Eq.{1} HeytingLean.Noneism.Var x x) True
                              (@congrArg.{1, 1} HeytingLean.Noneism.Var Prop z x
                                (fun (x_1 : HeytingLean.Noneism.Var) => @Eq.{1} HeytingLean.Noneism.Var x_1 x) hzx)
                              (@eq_self.{1} HeytingLean.Noneism.Var x)))))
                      (iff_self (@HeytingLean.Noneism.KripkeFO.Model.valEx W σ D inst M w (ρ y)))))
                fun (hzx : Not (@Eq.{1} HeytingLean.Noneism.Var z x)) =>
                @of_eq_true
                  (Iff
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                      (@HeytingLean.Noneism.Formula.eExists σ
                        (@ite.{1} HeytingLean.Noneism.Term (@Eq.{1} HeytingLean.Noneism.Var z x)
                          (instDecidableEqNat z x) (HeytingLean.Noneism.Term.var y) (HeytingLean.Noneism.Term.var z))))
                    (@HeytingLean.Noneism.KripkeFO.Model.valEx W σ D inst M w
                      (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ y) (ρ z))))
                  (@Eq.trans.{1} Prop
                    (Iff
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                        (@HeytingLean.Noneism.Formula.eExists σ
                          (@ite.{1} HeytingLean.Noneism.Term (@Eq.{1} HeytingLean.Noneism.Var z x)
                            (instDecidableEqNat z x) (HeytingLean.Noneism.Term.var y)
                            (HeytingLean.Noneism.Term.var z))))
                      (@HeytingLean.Noneism.KripkeFO.Model.valEx W σ D inst M w
                        (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ y) (ρ z))))
                    (Iff
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                        (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var z)))
                      (@HeytingLean.Noneism.KripkeFO.Model.valEx W σ D inst M w (ρ z)))
                    True
                    (@congr.{1, 1} Prop Prop
                      (Iff
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                          (@HeytingLean.Noneism.Formula.eExists σ
                            (@ite.{1} HeytingLean.Noneism.Term (@Eq.{1} HeytingLean.Noneism.Var z x)
                              (instDecidableEqNat z x) (HeytingLean.Noneism.Term.var y)
                              (HeytingLean.Noneism.Term.var z)))))
                      (Iff
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                          (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var z))))
                      (@HeytingLean.Noneism.KripkeFO.Model.valEx W σ D inst M w
                        (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ y) (ρ z)))
                      (@HeytingLean.Noneism.KripkeFO.Model.valEx W σ D inst M w (ρ z))
                      (@congrArg.{1, 1} HeytingLean.Noneism.Term ((b : Prop) → Prop)
                        (@ite.{1} HeytingLean.Noneism.Term (@Eq.{1} HeytingLean.Noneism.Var z x)
                          (instDecidableEqNat z x) (HeytingLean.Noneism.Term.var y) (HeytingLean.Noneism.Term.var z))
                        (HeytingLean.Noneism.Term.var z)
                        (fun (x : HeytingLean.Noneism.Term) =>
                          Iff
                            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                              (@HeytingLean.Noneism.Formula.eExists σ x)))
                        (@ite_cond_eq_false.{1} HeytingLean.Noneism.Term (@Eq.{1} HeytingLean.Noneism.Var z x)
                          (instDecidableEqNat z x) (HeytingLean.Noneism.Term.var y) (HeytingLean.Noneism.Term.var z)
                          (@eq_false (@Eq.{1} HeytingLean.Noneism.Var z x) hzx)))
                      (@congrArg.{1, 1} D Prop
                        (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ y) (ρ z)) (ρ z)
                        (@HeytingLean.Noneism.KripkeFO.Model.valEx W σ D inst M w)
                        (@ite_cond_eq_false.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ y)
                          (ρ z) (@eq_false (@Eq.{1} HeytingLean.Noneism.Var z x) hzx))))
                    (iff_self (@HeytingLean.Noneism.KripkeFO.Model.valEx W σ D inst M w (ρ z)))))
            t (@Eq.symm.{1} HeytingLean.Noneism.Term t (HeytingLean.Noneism.Term.var z) h) _hy)
        (@Eq.refl.{1} HeytingLean.Noneism.Term t))
    (fun (φ : HeytingLean.Noneism.Formula σ)
        (ih :
          ∀ (ρ : HeytingLean.Noneism.KripkeFO.Valuation D),
            Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  y) →
              ∀ (w : W),
                Iff
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y))
                    w φ))
        (ρ : HeytingLean.Noneism.KripkeFO.Valuation D)
        (hy :
          Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@HeytingLean.Noneism.Syntax.varsFormula σ (@HeytingLean.Noneism.Formula.not σ φ)) y))
        (w : W) =>
      have hyφ :
        Not
          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
            (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y) :=
        hy;
      @Iff.intro
        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
          (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.not σ φ)))
        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
          (@HeytingLean.Noneism.Formula.not σ φ))
        (fun
            (h :
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.not σ φ)))
            (v : W) (hwv : @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v)
            (hv :
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) v
                φ) =>
          have hv' :
            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ) :=
            @Iff.mpr
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) v φ)
              (ih ρ hyφ v) hv;
          h v hwv hv')
        fun
          (h :
            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
              (@HeytingLean.Noneism.Formula.not σ φ))
          (v : W) (hwv : @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v)
          (hv :
            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
              (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ)) =>
        have hv' :
          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) v φ :=
          @Iff.mp
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) v φ)
            (ih ρ hyφ v) hv;
        h v hwv hv')
    (fun (φ ψ : HeytingLean.Noneism.Formula σ)
        (ihφ :
          ∀ (ρ : HeytingLean.Noneism.KripkeFO.Valuation D),
            Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  y) →
              ∀ (w : W),
                Iff
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y))
                    w φ))
        (ihψ :
          ∀ (ρ : HeytingLean.Noneism.KripkeFO.Valuation D),
            Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ)
                  y) →
              ∀ (w : W),
                Iff
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y ψ))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y))
                    w ψ))
        (ρ : HeytingLean.Noneism.KripkeFO.Valuation D)
        (hy :
          Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@HeytingLean.Noneism.Syntax.varsFormula σ (@HeytingLean.Noneism.Formula.and σ φ ψ)) y))
        (w : W) =>
      have hy' :
        And
          (Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y))
          (Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ) y)) :=
        @Eq.mp.{0}
          (Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@HeytingLean.Noneism.Syntax.varsFormula σ (@HeytingLean.Noneism.Formula.and σ φ ψ)) y))
          (And
            (Not
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y))
            (Not
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ) y)))
          (@Eq.trans.{1} Prop
            (Not
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ))
                y))
            (Not
              (Or
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y)
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ)
                  y)))
            (And
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y))
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ)
                  y)))
            (@congrArg.{1, 1} Prop Prop
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ))
                y)
              (Or
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y)
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ) y))
              Not
              (@Finset.mem_union._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ) y))
            (@not_or._simp_1
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y)
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ) y)))
          hy;
      @of_eq_true
        (Iff
          (And
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w (@HeytingLean.Noneism.Syntax.renameFormula σ x y ψ)))
          (And
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w φ)
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w ψ)))
        (@Eq.trans.{1} Prop
          (Iff
            (And
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.renameFormula σ x y ψ)))
            (And
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w φ)
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
                ψ)))
          (Iff
            (And
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w φ)
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
                ψ))
            (And
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w φ)
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
                ψ)))
          True
          (@congrArg.{1, 1} Prop Prop
            (And
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.renameFormula σ x y ψ)))
            (And
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w φ)
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
                ψ))
            (fun (x_1 : Prop) =>
              Iff x_1
                (And
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y))
                    w φ)
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y))
                    w ψ)))
            (@congr.{1, 1} Prop Prop
              (And
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                  (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ)))
              (And
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
                  φ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.renameFormula σ x y ψ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w ψ)
              (@congrArg.{1, 1} Prop ((b : Prop) → Prop)
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                  (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
                  φ)
                And
                (@propext
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y))
                    w φ)
                  (ihφ ρ
                    (@And.left
                      (Not
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y))
                      (Not
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ ψ) y))
                      hy')
                    w)))
              (@propext
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                  (@HeytingLean.Noneism.Syntax.renameFormula σ x y ψ))
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
                  ψ)
                (ihψ ρ
                  (@And.right
                    (Not
                      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y))
                    (Not
                      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ ψ) y))
                    hy')
                  w))))
          (iff_self
            (And
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w φ)
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
                ψ)))))
    (fun (φ ψ : HeytingLean.Noneism.Formula σ)
        (ihφ :
          ∀ (ρ : HeytingLean.Noneism.KripkeFO.Valuation D),
            Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  y) →
              ∀ (w : W),
                Iff
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y))
                    w φ))
        (ihψ :
          ∀ (ρ : HeytingLean.Noneism.KripkeFO.Valuation D),
            Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ)
                  y) →
              ∀ (w : W),
                Iff
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y ψ))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y))
                    w ψ))
        (ρ : HeytingLean.Noneism.KripkeFO.Valuation D)
        (hy :
          Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@HeytingLean.Noneism.Syntax.varsFormula σ (@HeytingLean.Noneism.Formula.or σ φ ψ)) y))
        (w : W) =>
      have hy' :
        And
          (Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y))
          (Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ) y)) :=
        @Eq.mp.{0}
          (Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@HeytingLean.Noneism.Syntax.varsFormula σ (@HeytingLean.Noneism.Formula.or σ φ ψ)) y))
          (And
            (Not
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y))
            (Not
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ) y)))
          (@Eq.trans.{1} Prop
            (Not
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ))
                y))
            (Not
              (Or
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y)
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ)
                  y)))
            (And
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y))
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ)
                  y)))
            (@congrArg.{1, 1} Prop Prop
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ))
                y)
              (Or
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y)
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ) y))
              Not
              (@Finset.mem_union._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ) y))
            (@not_or._simp_1
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y)
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ) y)))
          hy;
      @of_eq_true
        (Iff
          (Or
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w (@HeytingLean.Noneism.Syntax.renameFormula σ x y ψ)))
          (Or (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w φ)
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w ψ)))
        (@Eq.trans.{1} Prop
          (Iff
            (Or
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.renameFormula σ x y ψ)))
            (Or
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w φ)
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
                ψ)))
          (Iff
            (Or
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w φ)
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
                ψ))
            (Or
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w φ)
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
                ψ)))
          True
          (@congrArg.{1, 1} Prop Prop
            (Or
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.renameFormula σ x y ψ)))
            (Or
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w φ)
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
                ψ))
            (fun (x_1 : Prop) =>
              Iff x_1
                (Or
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y))
                    w φ)
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y))
                    w ψ)))
            (@congr.{1, 1} Prop Prop
              (Or
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                  (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ)))
              (Or
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
                  φ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.renameFormula σ x y ψ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w ψ)
              (@congrArg.{1, 1} Prop ((b : Prop) → Prop)
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                  (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
                  φ)
                Or
                (@propext
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y))
                    w φ)
                  (ihφ ρ
                    (@And.left
                      (Not
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y))
                      (Not
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ ψ) y))
                      hy')
                    w)))
              (@propext
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                  (@HeytingLean.Noneism.Syntax.renameFormula σ x y ψ))
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
                  ψ)
                (ihψ ρ
                  (@And.right
                    (Not
                      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y))
                    (Not
                      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ ψ) y))
                    hy')
                  w))))
          (iff_self
            (Or
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w φ)
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
                ψ)))))
    (fun (φ ψ : HeytingLean.Noneism.Formula σ)
        (ihφ :
          ∀ (ρ : HeytingLean.Noneism.KripkeFO.Valuation D),
            Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  y) →
              ∀ (w : W),
                Iff
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y))
                    w φ))
        (ihψ :
          ∀ (ρ : HeytingLean.Noneism.KripkeFO.Valuation D),
            Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ)
                  y) →
              ∀ (w : W),
                Iff
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y ψ))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y))
                    w ψ))
        (ρ : HeytingLean.Noneism.KripkeFO.Valuation D)
        (hy :
          Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@HeytingLean.Noneism.Syntax.varsFormula σ (@HeytingLean.Noneism.Formula.imp σ φ ψ)) y))
        (w : W) =>
      have hy' :
        And
          (Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y))
          (Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ) y)) :=
        @Eq.mp.{0}
          (Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@HeytingLean.Noneism.Syntax.varsFormula σ (@HeytingLean.Noneism.Formula.imp σ φ ψ)) y))
          (And
            (Not
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y))
            (Not
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ) y)))
          (@Eq.trans.{1} Prop
            (Not
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ))
                y))
            (Not
              (Or
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y)
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ)
                  y)))
            (And
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y))
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ)
                  y)))
            (@congrArg.{1, 1} Prop Prop
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ))
                y)
              (Or
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y)
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ) y))
              Not
              (@Finset.mem_union._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ) y))
            (@not_or._simp_1
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y)
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ) y)))
          hy;
      @Iff.intro
        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
          (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.imp σ φ ψ)))
        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
          (@HeytingLean.Noneism.Formula.imp σ φ ψ))
        (fun
            (h :
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.imp σ φ ψ)))
            (v : W) (hwv : @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v)
            (hvφ :
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) v
                φ) =>
          have hvφ' :
            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ) :=
            @Iff.mpr
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) v φ)
              (ihφ ρ
                (@And.left
                  (Not
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      y))
                  (Not
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ)
                      y))
                  hy')
                v)
              hvφ;
          have hvψ' :
            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v (@HeytingLean.Noneism.Syntax.renameFormula σ x y ψ) :=
            h v hwv hvφ';
          @Iff.mp
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v (@HeytingLean.Noneism.Syntax.renameFormula σ x y ψ))
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) v ψ)
            (ihψ ρ
              (@And.right
                (Not
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    y))
                (Not
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ)
                    y))
                hy')
              v)
            hvψ')
        fun
          (h :
            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
              (@HeytingLean.Noneism.Formula.imp σ φ ψ))
          (v : W) (hwv : @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v)
          (hvφ :
            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
              (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ)) =>
        have hvφ' :
          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) v φ :=
          @Iff.mp
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) v φ)
            (ihφ ρ
              (@And.left
                (Not
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    y))
                (Not
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ)
                    y))
                hy')
              v)
            hvφ;
        have hvψ' :
          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) v ψ :=
          h v hwv hvφ';
        @Iff.mpr
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v (@HeytingLean.Noneism.Syntax.renameFormula σ x y ψ))
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) v ψ)
          (ihψ ρ
            (@And.right
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y))
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ ψ) y))
              hy')
            v)
          hvψ')
    (fun (z : HeytingLean.Noneism.Var) (φ : HeytingLean.Noneism.Formula σ)
        (ih :
          ∀ (ρ : HeytingLean.Noneism.KripkeFO.Valuation D),
            Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  y) →
              ∀ (w : W),
                Iff
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y))
                    w φ))
        (ρ : HeytingLean.Noneism.KripkeFO.Valuation D)
        (hy :
          Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@HeytingLean.Noneism.Syntax.varsFormula σ (@HeytingLean.Noneism.Formula.sigma σ z φ)) y))
        (w : W) =>
      have hyIns :
        Not
          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
            (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
              (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
            y) :=
        @Eq.mpr.{0}
          (Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
              y))
          (And (Not (@Eq.{1} HeytingLean.Noneism.Var y z))
            (Not
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y)))
          (@id.{0}
            (@Eq.{1} Prop
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
                  y))
              (And (Not (@Eq.{1} HeytingLean.Noneism.Var y z))
                (Not
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    y))))
            (@Eq.trans.{1} Prop
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
                  y))
              (Not
                (Or (@Eq.{1} HeytingLean.Noneism.Var y z)
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    y)))
              (And (Not (@Eq.{1} HeytingLean.Noneism.Var y z))
                (Not
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    y)))
              (@congrArg.{1, 1} Prop Prop
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
                  y)
                (Or (@Eq.{1} HeytingLean.Noneism.Var y z)
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    y))
                Not
                (@Finset.mem_insert._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y z))
              (@not_or._simp_1 (@Eq.{1} HeytingLean.Noneism.Var y z)
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  y))))
          (@Eq.mp.{0}
            (Not
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@HeytingLean.Noneism.Syntax.varsFormula σ (@HeytingLean.Noneism.Formula.sigma σ z φ)) y))
            (And (Not (@Eq.{1} HeytingLean.Noneism.Var y z))
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  y)))
            (@Eq.trans.{1} Prop
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
                  y))
              (Not
                (Or (@Eq.{1} HeytingLean.Noneism.Var y z)
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    y)))
              (And (Not (@Eq.{1} HeytingLean.Noneism.Var y z))
                (Not
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    y)))
              (@congrArg.{1, 1} Prop Prop
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
                  y)
                (Or (@Eq.{1} HeytingLean.Noneism.Var y z)
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    y))
                Not
                (@Finset.mem_insert._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y z))
              (@not_or._simp_1 (@Eq.{1} HeytingLean.Noneism.Var y z)
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  y)))
            hy);
      have hyz : @Ne.{1} HeytingLean.Noneism.Var y z := fun (hyEq : @Eq.{1} HeytingLean.Noneism.Var y z) =>
        hyIns
          (@of_eq_true
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
              y)
            (@Eq.trans.{1} Prop
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
                y)
              (Or (@Eq.{1} HeytingLean.Noneism.Var z z)
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) z))
              True
              (@Eq.trans.{1} Prop
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
                  y)
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
                  z)
                (Or (@Eq.{1} HeytingLean.Noneism.Var z z)
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    z))
                (@congrArg.{1, 1} HeytingLean.Noneism.Var Prop y z
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)))
                  hyEq)
                (@Finset.mem_insert._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ) z z))
              (@Eq.trans.{1} Prop
                (Or (@Eq.{1} HeytingLean.Noneism.Var z z)
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    z))
                (Or True
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    z))
                True
                (@congrArg.{1, 1} Prop Prop (@Eq.{1} HeytingLean.Noneism.Var z z) True
                  (fun (x : Prop) =>
                    Or x
                      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ) z))
                  (@eq_self.{1} HeytingLean.Noneism.Var z))
                (true_or
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    z)))));
      have hyφ :
        Not
          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
            (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y) :=
        fun
          (hyMem :
            @Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y) =>
        hyIns
          (@of_eq_true
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
              y)
            (@Eq.trans.{1} Prop
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
                y)
              (Or (@Eq.{1} HeytingLean.Noneism.Var y z)
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y))
              True
              (@Finset.mem_insert._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y z)
              (@Eq.trans.{1} Prop
                (Or (@Eq.{1} HeytingLean.Noneism.Var y z)
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    y))
                (Or (@Eq.{1} HeytingLean.Noneism.Var y z) True) True
                (@congrArg.{1, 1} Prop Prop
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    y)
                  True (Or (@Eq.{1} HeytingLean.Noneism.Var y z))
                  (@eq_true
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      y)
                    hyMem))
                (or_true (@Eq.{1} HeytingLean.Noneism.Var y z)))));
      @dite.{0}
        (Iff
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
            (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.sigma σ z φ)))
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
            (@HeytingLean.Noneism.Formula.sigma σ z φ)))
        (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x)
        (fun (hzx : @Eq.{1} HeytingLean.Noneism.Var z x) =>
          have hyx : @Ne.{1} HeytingLean.Noneism.Var y x :=
            @id.{0} (@Ne.{1} HeytingLean.Noneism.Var y x)
              (@Eq.mp.{0} (@Ne.{1} HeytingLean.Noneism.Var y z) (Not (@Eq.{1} HeytingLean.Noneism.Var y x))
                (@congrArg.{1, 1} HeytingLean.Noneism.Var Prop z x (@Ne.{1} HeytingLean.Noneism.Var y) hzx) hyz);
          @Iff.intro
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
              (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.sigma σ z φ)))
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
              (@HeytingLean.Noneism.Formula.sigma σ z φ))
            (fun
                (h :
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.sigma σ z φ))) =>
              @Exists.casesOn.{1} D
                (fun (d : D) =>
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ y d) w
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                (fun
                    (x_1 :
                      @Exists.{1} D fun (d : D) =>
                        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ y d)
                          w (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ)) =>
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
                    (@HeytingLean.Noneism.Formula.sigma σ z φ))
                (@Eq.mp.{0}
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.sigma σ z φ)))
                  (@Exists.{1} D fun (d : D) =>
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ y d) w
                      (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                  (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) Prop
                    (@ite.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var z x)
                      (instDecidableEqNat z x)
                      (@HeytingLean.Noneism.Formula.sigma σ y (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                      (@HeytingLean.Noneism.Formula.sigma σ z (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ)))
                    (@HeytingLean.Noneism.Formula.sigma σ y (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w)
                    (@ite_cond_eq_true.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var z x)
                      (instDecidableEqNat z x)
                      (@HeytingLean.Noneism.Formula.sigma σ y (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                      (@HeytingLean.Noneism.Formula.sigma σ z (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                      (@Eq.trans.{1} Prop (@Eq.{1} HeytingLean.Noneism.Var z x) (@Eq.{1} HeytingLean.Noneism.Var x x)
                        True
                        (@congrArg.{1, 1} HeytingLean.Noneism.Var Prop z x
                          (fun (x_1 : HeytingLean.Noneism.Var) => @Eq.{1} HeytingLean.Noneism.Var x_1 x) hzx)
                        (@eq_self.{1} HeytingLean.Noneism.Var x))))
                  h)
                fun (d : D)
                  (hd :
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ y d) w
                      (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ)) =>
                have hd' :
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y d) x
                      (@HeytingLean.Noneism.KripkeFO.update D ρ y d y))
                    w φ :=
                  @Iff.mp
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ y d) w
                      (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y d) x
                        (@HeytingLean.Noneism.KripkeFO.update D ρ y d y))
                      w φ)
                    (ih (@HeytingLean.Noneism.KripkeFO.update D ρ y d) hyφ w) hd;
                have hd'' :
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y d) x d) w φ :=
                  @Eq.mp.{0}
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y d) x
                        (@HeytingLean.Noneism.KripkeFO.update D ρ y d y))
                      w φ)
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y d) x d) w φ)
                    (@congrArg.{1, 1} D Prop (@HeytingLean.Noneism.KripkeFO.update D ρ y d y) d
                      (fun (x_1 : D) =>
                        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y d) x x_1)
                          w φ)
                      (@HeytingLean.Noneism.KripkeFO.update_self D ρ y d))
                    hd';
                have hComm :
                  @Eq.{1} (HeytingLean.Noneism.KripkeFO.Valuation D)
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y d) x d)
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x d) y d) :=
                  @HeytingLean.Noneism.KripkeFO.update_comm D ρ y x d d hyx;
                have hdComm :
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x d) y d) w φ :=
                  @Eq.mp.{0}
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y d) x d) w φ)
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x d) y d) w φ)
                    (@congrArg.{1, 1} (HeytingLean.Noneism.KripkeFO.Valuation D) Prop
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y d) x d)
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x d) y d)
                      (fun (x : HeytingLean.Noneism.KripkeFO.Valuation D) =>
                        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M x w φ)
                      hComm)
                    hd'';
                have hdFinal :
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x d) w
                    φ :=
                  @Iff.mp
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x d) y d) w φ)
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x d) w
                      φ)
                    (@HeytingLean.Noneism.KripkeFO.forces_update_of_not_mem_varsFormula σ W inst D M
                      (@HeytingLean.Noneism.KripkeFO.update D ρ x d) y d w φ hyφ)
                    hdComm;
                have this :
                  @Exists.{1} D fun (d : D) =>
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x d) w
                      φ :=
                  @Exists.intro.{1} D
                    (fun (d : D) =>
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x d) w
                        φ)
                    d hdFinal;
                @Eq.mpr.{0}
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y))
                    w (@HeytingLean.Noneism.Formula.sigma σ z φ))
                  (@Exists.{1} D fun (d : D) =>
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x d) w
                      φ)
                  (@id.{0}
                    (@Eq.{1} Prop
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w (@HeytingLean.Noneism.Formula.sigma σ z φ))
                      (@Exists.{1} D fun (d : D) =>
                        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x d)
                          w φ))
                    (@congrArg.{1, 1} (D → Prop) Prop
                      (fun (x_1 : D) =>
                        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z
                            x_1)
                          w φ)
                      (fun (x_1 : D) =>
                        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                          (@HeytingLean.Noneism.KripkeFO.update D ρ x x_1) w φ)
                      (@Exists.{1} D)
                      (@funext.{1, 1} D (fun (x : D) => Prop)
                        (fun (x_1 : D) =>
                          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z
                              x_1)
                            w φ)
                        (fun (x_1 : D) =>
                          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                            (@HeytingLean.Noneism.KripkeFO.update D ρ x x_1) w φ)
                        fun (d : D) =>
                        @congrArg.{1, 1} (HeytingLean.Noneism.KripkeFO.Valuation D) Prop
                          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z
                            d)
                          (@HeytingLean.Noneism.KripkeFO.update D ρ x d)
                          (fun (x : HeytingLean.Noneism.KripkeFO.Valuation D) =>
                            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M x w φ)
                          (@Eq.trans.{1} (HeytingLean.Noneism.KripkeFO.Valuation D)
                            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z
                              d)
                            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) x
                              d)
                            (@HeytingLean.Noneism.KripkeFO.update D ρ x d)
                            (@congrArg.{1, 1} HeytingLean.Noneism.Var (HeytingLean.Noneism.KripkeFO.Valuation D) z x
                              (fun (x_1 : HeytingLean.Noneism.Var) =>
                                @HeytingLean.Noneism.KripkeFO.update D
                                  (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) x_1 d)
                              hzx)
                            (@HeytingLean.Noneism.KripkeFO.update_update_same D ρ x (ρ y) d)))))
                  this)
            fun
              (h :
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
                  (@HeytingLean.Noneism.Formula.sigma σ z φ)) =>
            @Exists.casesOn.{1} D
              (fun (d : D) =>
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x d) w φ)
              (fun
                  (x_1 :
                    @Exists.{1} D fun (d : D) =>
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x d) w
                        φ) =>
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                  (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.sigma σ z φ)))
              (@Eq.mp.{0}
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
                  (@HeytingLean.Noneism.Formula.sigma σ z φ))
                (@Exists.{1} D fun (d : D) =>
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x d) w φ)
                (@congrArg.{1, 1} (D → Prop) Prop
                  (fun (x_1 : D) =>
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z x_1)
                      w φ)
                  (fun (x_1 : D) =>
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x x_1) w
                      φ)
                  (@Exists.{1} D)
                  (@funext.{1, 1} D (fun (x : D) => Prop)
                    (fun (x_1 : D) =>
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z
                          x_1)
                        w φ)
                    (fun (x_1 : D) =>
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x x_1)
                        w φ)
                    fun (d : D) =>
                    @congrArg.{1, 1} (HeytingLean.Noneism.KripkeFO.Valuation D) Prop
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z d)
                      (@HeytingLean.Noneism.KripkeFO.update D ρ x d)
                      (fun (x : HeytingLean.Noneism.KripkeFO.Valuation D) =>
                        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M x w φ)
                      (@Eq.trans.{1} (HeytingLean.Noneism.KripkeFO.Valuation D)
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z d)
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) x d)
                        (@HeytingLean.Noneism.KripkeFO.update D ρ x d)
                        (@congrArg.{1, 1} HeytingLean.Noneism.Var (HeytingLean.Noneism.KripkeFO.Valuation D) z x
                          (fun (x_1 : HeytingLean.Noneism.Var) =>
                            @HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y))
                              x_1 d)
                          hzx)
                        (@HeytingLean.Noneism.KripkeFO.update_update_same D ρ x (ρ y) d))))
                h)
              fun (d : D)
                (hd :
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x d) w
                    φ) =>
              have hdBase :
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x d) w φ :=
                hd;
              have hdWithY :
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x d) y d) w φ :=
                @Iff.mpr
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x d) y d) w φ)
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x d) w φ)
                  (@HeytingLean.Noneism.KripkeFO.forces_update_of_not_mem_varsFormula σ W inst D M
                    (@HeytingLean.Noneism.KripkeFO.update D ρ x d) y d w φ hyφ)
                  hdBase;
              have hComm :
                @Eq.{1} (HeytingLean.Noneism.KripkeFO.Valuation D)
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y d) x d)
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x d) y d) :=
                @HeytingLean.Noneism.KripkeFO.update_comm D ρ y x d d hyx;
              have hdComm :
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y d) x d) w φ :=
                @Eq.mpr.{0}
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y d) x d) w φ)
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x d) y d) w φ)
                  (@id.{0}
                    (@Eq.{1} Prop
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y d) x d) w φ)
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x d) y d) w
                        φ))
                    (@congrArg.{1, 1} (HeytingLean.Noneism.KripkeFO.Valuation D) Prop
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y d) x d)
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x d) y d)
                      (fun (x : HeytingLean.Noneism.KripkeFO.Valuation D) =>
                        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M x w φ)
                      hComm))
                  hdWithY;
              have hdRen :
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ y d) w
                  (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ) :=
                @Iff.mpr
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ y d) w
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y d) x
                      (@HeytingLean.Noneism.KripkeFO.update D ρ y d y))
                    w φ)
                  (ih (@HeytingLean.Noneism.KripkeFO.update D ρ y d) hyφ w)
                  (@Eq.mpr.{0}
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y d) x
                        (@HeytingLean.Noneism.KripkeFO.update D ρ y d y))
                      w φ)
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y d) x d) w φ)
                    (@id.{0}
                      (@Eq.{1} Prop
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y d) x
                            (@HeytingLean.Noneism.KripkeFO.update D ρ y d y))
                          w φ)
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y d) x d) w
                          φ))
                      (@congrArg.{1, 1} D Prop (@HeytingLean.Noneism.KripkeFO.update D ρ y d y) d
                        (fun (x_1 : D) =>
                          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y d) x
                              x_1)
                            w φ)
                        (@HeytingLean.Noneism.KripkeFO.update_self D ρ y d)))
                    hdComm);
              have this :
                @Exists.{1} D fun (d : D) =>
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ y d) w
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ) :=
                @Exists.intro.{1} D
                  (fun (d : D) =>
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ y d) w
                      (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                  d hdRen;
              @Eq.mpr.{0}
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                  (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.sigma σ z φ)))
                (@Exists.{1} D fun (d : D) =>
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ y d) w
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                (@id.{0}
                  (@Eq.{1} Prop
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                      (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.sigma σ z φ)))
                    (@Exists.{1} D fun (d : D) =>
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ y d) w
                        (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ)))
                  (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) Prop
                    (@ite.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var z x)
                      (instDecidableEqNat z x)
                      (@HeytingLean.Noneism.Formula.sigma σ y (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                      (@HeytingLean.Noneism.Formula.sigma σ z (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ)))
                    (@HeytingLean.Noneism.Formula.sigma σ y (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w)
                    (@ite_cond_eq_true.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var z x)
                      (instDecidableEqNat z x)
                      (@HeytingLean.Noneism.Formula.sigma σ y (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                      (@HeytingLean.Noneism.Formula.sigma σ z (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                      (@Eq.trans.{1} Prop (@Eq.{1} HeytingLean.Noneism.Var z x) (@Eq.{1} HeytingLean.Noneism.Var x x)
                        True
                        (@congrArg.{1, 1} HeytingLean.Noneism.Var Prop z x
                          (fun (x_1 : HeytingLean.Noneism.Var) => @Eq.{1} HeytingLean.Noneism.Var x_1 x) hzx)
                        (@eq_self.{1} HeytingLean.Noneism.Var x)))))
                this)
        fun (hzx : Not (@Eq.{1} HeytingLean.Noneism.Var z x)) =>
        @Iff.intro
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
            (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.sigma σ z φ)))
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
            (@HeytingLean.Noneism.Formula.sigma σ z φ))
          (fun
              (h :
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                  (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.sigma σ z φ))) =>
            @Exists.casesOn.{1} D
              (fun (d : D) =>
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) w
                  (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
              (fun
                  (x_1 :
                    @Exists.{1} D fun (d : D) =>
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) w
                        (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ)) =>
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
                  (@HeytingLean.Noneism.Formula.sigma σ z φ))
              (@Eq.mp.{0}
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                  (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.sigma σ z φ)))
                (@Exists.{1} D fun (d : D) =>
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) w
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) Prop
                  (@ite.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var z x)
                    (instDecidableEqNat z x)
                    (@HeytingLean.Noneism.Formula.sigma σ y (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                    (@HeytingLean.Noneism.Formula.sigma σ z (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ)))
                  (@HeytingLean.Noneism.Formula.sigma σ z (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w)
                  (@ite_cond_eq_false.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var z x)
                    (instDecidableEqNat z x)
                    (@HeytingLean.Noneism.Formula.sigma σ y (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                    (@HeytingLean.Noneism.Formula.sigma σ z (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                    (@eq_false (@Eq.{1} HeytingLean.Noneism.Var z x) hzx)))
                h)
              fun (d : D)
                (hd :
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) w
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ)) =>
              have hd' :
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                    (@HeytingLean.Noneism.KripkeFO.update D ρ z d y))
                  w φ :=
                @Iff.mp
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) w
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                      (@HeytingLean.Noneism.KripkeFO.update D ρ z d y))
                    w φ)
                  (ih (@HeytingLean.Noneism.KripkeFO.update D ρ z d) hyφ w) hd;
              have hyKeep : @Eq.{1} D (@HeytingLean.Noneism.KripkeFO.update D ρ z d y) (ρ y) :=
                @of_eq_true
                  (@Eq.{1} D (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var y z) (instDecidableEqNat y z) d (ρ y)) (ρ y))
                  (@Eq.trans.{1} Prop
                    (@Eq.{1} D (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var y z) (instDecidableEqNat y z) d (ρ y))
                      (ρ y))
                    (@Eq.{1} D (ρ y) (ρ y)) True
                    (@congrArg.{1, 1} D Prop
                      (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var y z) (instDecidableEqNat y z) d (ρ y)) (ρ y)
                      (fun (x : D) => @Eq.{1} D x (ρ y))
                      (@ite_cond_eq_false.{1} D (@Eq.{1} HeytingLean.Noneism.Var y z) (instDecidableEqNat y z) d (ρ y)
                        (@eq_false (@Eq.{1} HeytingLean.Noneism.Var y z) hyz)))
                    (@eq_self.{1} D (ρ y)));
              have hd'' :
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ y)) w φ :=
                @Eq.mp.{0}
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                      (@HeytingLean.Noneism.KripkeFO.update D ρ z d y))
                    w φ)
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ y)) w φ)
                  (@congrArg.{1, 1} D Prop (@HeytingLean.Noneism.KripkeFO.update D ρ z d y) (ρ y)
                    (fun (x_1 : D) =>
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x x_1) w
                        φ)
                    hyKeep)
                  hd';
              have hComm :
                @Eq.{1} (HeytingLean.Noneism.KripkeFO.Valuation D)
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ y))
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z d) :=
                @HeytingLean.Noneism.KripkeFO.update_comm D ρ z x d (ρ y) hzx;
              have this :
                @Exists.{1} D fun (d : D) =>
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z d) w
                    φ :=
                @Exists.intro.{1} D
                  (fun (d : D) =>
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z d) w
                      φ)
                  d
                  (@Eq.mp.{0}
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ y)) w
                      φ)
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z d) w
                      φ)
                    (@congrArg.{1, 1} (HeytingLean.Noneism.KripkeFO.Valuation D) Prop
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ y))
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z d)
                      (fun (x : HeytingLean.Noneism.KripkeFO.Valuation D) =>
                        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M x w φ)
                      hComm)
                    hd'');
              @id.{0}
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
                  (@HeytingLean.Noneism.Formula.sigma σ z φ))
                this)
          fun
            (h :
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
                (@HeytingLean.Noneism.Formula.sigma σ z φ)) =>
          @Exists.casesOn.{1} D
            (fun (d : D) =>
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z d) w φ)
            (fun
                (x_1 :
                  @Exists.{1} D fun (d : D) =>
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z d) w
                      φ) =>
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.sigma σ z φ)))
            h
            fun (d : D)
              (hd :
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z d) w
                  φ) =>
            have hComm :
              @Eq.{1} (HeytingLean.Noneism.KripkeFO.Valuation D)
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ y))
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z d) :=
              @HeytingLean.Noneism.KripkeFO.update_comm D ρ z x d (ρ y) hzx;
            have hd' :
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ y)) w φ :=
              @Eq.mpr.{0}
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ y)) w φ)
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z d) w φ)
                (@id.{0}
                  (@Eq.{1} Prop
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ y)) w
                      φ)
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z d) w
                      φ))
                  (@congrArg.{1, 1} (HeytingLean.Noneism.KripkeFO.Valuation D) Prop
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ y))
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z d)
                    (fun (x : HeytingLean.Noneism.KripkeFO.Valuation D) =>
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M x w φ)
                    hComm))
                hd;
            have hyKeep : @Eq.{1} D (@HeytingLean.Noneism.KripkeFO.update D ρ z d y) (ρ y) :=
              @of_eq_true
                (@Eq.{1} D (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var y z) (instDecidableEqNat y z) d (ρ y)) (ρ y))
                (@Eq.trans.{1} Prop
                  (@Eq.{1} D (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var y z) (instDecidableEqNat y z) d (ρ y)) (ρ y))
                  (@Eq.{1} D (ρ y) (ρ y)) True
                  (@congrArg.{1, 1} D Prop
                    (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var y z) (instDecidableEqNat y z) d (ρ y)) (ρ y)
                    (fun (x : D) => @Eq.{1} D x (ρ y))
                    (@ite_cond_eq_false.{1} D (@Eq.{1} HeytingLean.Noneism.Var y z) (instDecidableEqNat y z) d (ρ y)
                      (@eq_false (@Eq.{1} HeytingLean.Noneism.Var y z) hyz)))
                  (@eq_self.{1} D (ρ y)));
            have hd'' :
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                  (@HeytingLean.Noneism.KripkeFO.update D ρ z d y))
                w φ :=
              @Eq.mpr.{0}
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                    (@HeytingLean.Noneism.KripkeFO.update D ρ z d y))
                  w φ)
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ y)) w φ)
                (@id.{0}
                  (@Eq.{1} Prop
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                        (@HeytingLean.Noneism.KripkeFO.update D ρ z d y))
                      w φ)
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ y)) w
                      φ))
                  (@congrArg.{1, 1} D Prop (@HeytingLean.Noneism.KripkeFO.update D ρ z d y) (ρ y)
                    (fun (x_1 : D) =>
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x x_1) w
                        φ)
                    hyKeep))
                hd';
            have hRen :
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) w
                (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ) :=
              @Iff.mpr
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) w
                  (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                    (@HeytingLean.Noneism.KripkeFO.update D ρ z d y))
                  w φ)
                (ih (@HeytingLean.Noneism.KripkeFO.update D ρ z d) hyφ w) hd'';
            have this :
              @Exists.{1} D fun (d : D) =>
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) w
                  (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ) :=
              @Exists.intro.{1} D
                (fun (d : D) =>
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) w
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                d hRen;
            @Eq.mpr.{0}
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.sigma σ z φ)))
              (@Exists.{1} D fun (d : D) =>
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) w
                  (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
              (@id.{0}
                (@Eq.{1} Prop
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.sigma σ z φ)))
                  (@Exists.{1} D fun (d : D) =>
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) w
                      (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ)))
                (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) Prop
                  (@ite.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var z x)
                    (instDecidableEqNat z x)
                    (@HeytingLean.Noneism.Formula.sigma σ y (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                    (@HeytingLean.Noneism.Formula.sigma σ z (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ)))
                  (@HeytingLean.Noneism.Formula.sigma σ z (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w)
                  (@ite_cond_eq_false.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var z x)
                    (instDecidableEqNat z x)
                    (@HeytingLean.Noneism.Formula.sigma σ y (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                    (@HeytingLean.Noneism.Formula.sigma σ z (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                    (@eq_false (@Eq.{1} HeytingLean.Noneism.Var z x) hzx))))
              this)
    (fun (z : HeytingLean.Noneism.Var) (φ : HeytingLean.Noneism.Formula σ)
        (ih :
          ∀ (ρ : HeytingLean.Noneism.KripkeFO.Valuation D),
            Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  y) →
              ∀ (w : W),
                Iff
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y))
                    w φ))
        (ρ : HeytingLean.Noneism.KripkeFO.Valuation D)
        (hy :
          Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@HeytingLean.Noneism.Syntax.varsFormula σ (@HeytingLean.Noneism.Formula.pi σ z φ)) y))
        (w : W) =>
      have hyIns :
        Not
          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
            (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
              (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
            y) :=
        @Eq.mpr.{0}
          (Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
              y))
          (And (Not (@Eq.{1} HeytingLean.Noneism.Var y z))
            (Not
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y)))
          (@id.{0}
            (@Eq.{1} Prop
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
                  y))
              (And (Not (@Eq.{1} HeytingLean.Noneism.Var y z))
                (Not
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    y))))
            (@Eq.trans.{1} Prop
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
                  y))
              (Not
                (Or (@Eq.{1} HeytingLean.Noneism.Var y z)
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    y)))
              (And (Not (@Eq.{1} HeytingLean.Noneism.Var y z))
                (Not
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    y)))
              (@congrArg.{1, 1} Prop Prop
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
                  y)
                (Or (@Eq.{1} HeytingLean.Noneism.Var y z)
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    y))
                Not
                (@Finset.mem_insert._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y z))
              (@not_or._simp_1 (@Eq.{1} HeytingLean.Noneism.Var y z)
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  y))))
          (@Eq.mp.{0}
            (Not
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@HeytingLean.Noneism.Syntax.varsFormula σ (@HeytingLean.Noneism.Formula.pi σ z φ)) y))
            (And (Not (@Eq.{1} HeytingLean.Noneism.Var y z))
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  y)))
            (@Eq.trans.{1} Prop
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
                  y))
              (Not
                (Or (@Eq.{1} HeytingLean.Noneism.Var y z)
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    y)))
              (And (Not (@Eq.{1} HeytingLean.Noneism.Var y z))
                (Not
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    y)))
              (@congrArg.{1, 1} Prop Prop
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
                  y)
                (Or (@Eq.{1} HeytingLean.Noneism.Var y z)
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    y))
                Not
                (@Finset.mem_insert._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y z))
              (@not_or._simp_1 (@Eq.{1} HeytingLean.Noneism.Var y z)
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  y)))
            hy);
      have hyz : @Ne.{1} HeytingLean.Noneism.Var y z := fun (hyEq : @Eq.{1} HeytingLean.Noneism.Var y z) =>
        hyIns
          (@of_eq_true
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
              y)
            (@Eq.trans.{1} Prop
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
                y)
              (Or (@Eq.{1} HeytingLean.Noneism.Var z z)
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) z))
              True
              (@Eq.trans.{1} Prop
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
                  y)
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
                  z)
                (Or (@Eq.{1} HeytingLean.Noneism.Var z z)
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    z))
                (@congrArg.{1, 1} HeytingLean.Noneism.Var Prop y z
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)))
                  hyEq)
                (@Finset.mem_insert._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ) z z))
              (@Eq.trans.{1} Prop
                (Or (@Eq.{1} HeytingLean.Noneism.Var z z)
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    z))
                (Or True
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    z))
                True
                (@congrArg.{1, 1} Prop Prop (@Eq.{1} HeytingLean.Noneism.Var z z) True
                  (fun (x : Prop) =>
                    Or x
                      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ) z))
                  (@eq_self.{1} HeytingLean.Noneism.Var z))
                (true_or
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    z)))));
      have hyφ :
        Not
          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
            (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y) :=
        fun
          (hyMem :
            @Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y) =>
        hyIns
          (@of_eq_true
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
              y)
            (@Eq.trans.{1} Prop
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
                y)
              (Or (@Eq.{1} HeytingLean.Noneism.Var y z)
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y))
              True
              (@Finset.mem_insert._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ) y z)
              (@Eq.trans.{1} Prop
                (Or (@Eq.{1} HeytingLean.Noneism.Var y z)
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    y))
                (Or (@Eq.{1} HeytingLean.Noneism.Var y z) True) True
                (@congrArg.{1, 1} Prop Prop
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    y)
                  True (Or (@Eq.{1} HeytingLean.Noneism.Var y z))
                  (@eq_true
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      y)
                    hyMem))
                (or_true (@Eq.{1} HeytingLean.Noneism.Var y z)))));
      @dite.{0}
        (Iff
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
            (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.pi σ z φ)))
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
            (@HeytingLean.Noneism.Formula.pi σ z φ)))
        (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x)
        (fun (hzx : @Eq.{1} HeytingLean.Noneism.Var z x) =>
          have hyx : @Ne.{1} HeytingLean.Noneism.Var y x :=
            @id.{0} (@Ne.{1} HeytingLean.Noneism.Var y x)
              (@Eq.mp.{0} (@Ne.{1} HeytingLean.Noneism.Var y z) (Not (@Eq.{1} HeytingLean.Noneism.Var y x))
                (@congrArg.{1, 1} HeytingLean.Noneism.Var Prop z x (@Ne.{1} HeytingLean.Noneism.Var y) hzx) hyz);
          @Iff.intro
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
              (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.pi σ z φ)))
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
              (@HeytingLean.Noneism.Formula.pi σ z φ))
            (fun
                (h :
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.pi σ z φ)))
                (v : W) (hwv : @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v) (d : D) =>
              have hRenAll :
                ∀ (u : W),
                  @LE.le.{0} W (@Preorder.toLE.{0} W inst) w u →
                    ∀ (e : D),
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ y e) u
                        (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ) :=
                @Eq.mp.{0}
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.pi σ z φ)))
                  (∀ (v : W),
                    @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                      ∀ (d : D),
                        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ y d)
                          v (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                  (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) Prop
                    (@ite.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var z x)
                      (instDecidableEqNat z x)
                      (@HeytingLean.Noneism.Formula.pi σ y (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                      (@HeytingLean.Noneism.Formula.pi σ z (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ)))
                    (@HeytingLean.Noneism.Formula.pi σ y (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w)
                    (@ite_cond_eq_true.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var z x)
                      (instDecidableEqNat z x)
                      (@HeytingLean.Noneism.Formula.pi σ y (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                      (@HeytingLean.Noneism.Formula.pi σ z (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                      (@Eq.trans.{1} Prop (@Eq.{1} HeytingLean.Noneism.Var z x) (@Eq.{1} HeytingLean.Noneism.Var x x)
                        True
                        (@congrArg.{1, 1} HeytingLean.Noneism.Var Prop z x
                          (fun (x_1 : HeytingLean.Noneism.Var) => @Eq.{1} HeytingLean.Noneism.Var x_1 x) hzx)
                        (@eq_self.{1} HeytingLean.Noneism.Var x))))
                  h;
              have hd :
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y d) x
                    (@HeytingLean.Noneism.KripkeFO.update D ρ y d y))
                  v φ :=
                @Iff.mp
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ y d) v
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y d) x
                      (@HeytingLean.Noneism.KripkeFO.update D ρ y d y))
                    v φ)
                  (ih (@HeytingLean.Noneism.KripkeFO.update D ρ y d) hyφ v) (hRenAll v hwv d);
              have hd' :
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y d) x d) v φ :=
                @Eq.mp.{0}
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y d) x
                      (@HeytingLean.Noneism.KripkeFO.update D ρ y d y))
                    v φ)
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y d) x d) v φ)
                  (@congrArg.{1, 1} D Prop (@HeytingLean.Noneism.KripkeFO.update D ρ y d y) d
                    (fun (x_1 : D) =>
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y d) x x_1) v
                        φ)
                    (@HeytingLean.Noneism.KripkeFO.update_self D ρ y d))
                  hd;
              have hComm :
                @Eq.{1} (HeytingLean.Noneism.KripkeFO.Valuation D)
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y d) x d)
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x d) y d) :=
                @HeytingLean.Noneism.KripkeFO.update_comm D ρ y x d d hyx;
              have hdComm :
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x d) y d) v φ :=
                @Eq.mp.{0}
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y d) x d) v φ)
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x d) y d) v φ)
                  (@congrArg.{1, 1} (HeytingLean.Noneism.KripkeFO.Valuation D) Prop
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y d) x d)
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x d) y d)
                    (fun (x : HeytingLean.Noneism.KripkeFO.Valuation D) =>
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M x v φ)
                    hComm)
                  hd';
              have hdFinal :
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x d) v φ :=
                @Iff.mp
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x d) y d) v φ)
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x d) v φ)
                  (@HeytingLean.Noneism.KripkeFO.forces_update_of_not_mem_varsFormula σ W inst D M
                    (@HeytingLean.Noneism.KripkeFO.update D ρ x d) y d v φ hyφ)
                  hdComm;
              @Eq.mpr.{0}
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z d) v φ)
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x d) v φ)
                (@id.{0}
                  (@Eq.{1} Prop
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z d) v
                      φ)
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x d) v
                      φ))
                  (@congrArg.{1, 1} (HeytingLean.Noneism.KripkeFO.Valuation D) Prop
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z d)
                    (@HeytingLean.Noneism.KripkeFO.update D ρ x d)
                    (fun (x : HeytingLean.Noneism.KripkeFO.Valuation D) =>
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M x v φ)
                    (@Eq.trans.{1} (HeytingLean.Noneism.KripkeFO.Valuation D)
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z d)
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) x d)
                      (@HeytingLean.Noneism.KripkeFO.update D ρ x d)
                      (@congrArg.{1, 1} HeytingLean.Noneism.Var (HeytingLean.Noneism.KripkeFO.Valuation D) z x
                        (fun (x_1 : HeytingLean.Noneism.Var) =>
                          @HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) x_1
                            d)
                        hzx)
                      (@HeytingLean.Noneism.KripkeFO.update_update_same D ρ x (ρ y) d))))
                hdFinal)
            fun
              (h :
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
                  (@HeytingLean.Noneism.Formula.pi σ z φ)) =>
            have hAll :
              ∀ (u : W),
                @LE.le.{0} W (@Preorder.toLE.{0} W inst) w u →
                  ∀ (e : D),
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x e) u
                      φ :=
              @Eq.mp.{0}
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
                  (@HeytingLean.Noneism.Formula.pi σ z φ))
                (∀ (v : W),
                  @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                    ∀ (d : D),
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x d) v
                        φ)
                (@forall_congr.{1} W
                  (fun (a : W) =>
                    @LE.le.{0} W (@Preorder.toLE.{0} W inst) w a →
                      ∀ (a_2 : D),
                        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z
                            a_2)
                          a φ)
                  (fun (a : W) =>
                    @LE.le.{0} W (@Preorder.toLE.{0} W inst) w a →
                      ∀ (a_2 : D),
                        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                          (@HeytingLean.Noneism.KripkeFO.update D ρ x a_2) a φ)
                  fun (v : W) =>
                  @implies_congr.{0, 0} (@LE.le.{0} W (@Preorder.toLE.{0} W inst) w v)
                    (@LE.le.{0} W (@Preorder.toLE.{0} W inst) w v)
                    (∀ (a : D),
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z a)
                        v φ)
                    (∀ (a : D),
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x a) v
                        φ)
                    (@Eq.refl.{1} Prop (@LE.le.{0} W (@Preorder.toLE.{0} W inst) w v))
                    (@forall_congr.{1} D
                      (fun (a : D) =>
                        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z
                            a)
                          v φ)
                      (fun (a : D) =>
                        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x a)
                          v φ)
                      fun (d : D) =>
                      @congrArg.{1, 1} (HeytingLean.Noneism.KripkeFO.Valuation D) Prop
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z d)
                        (@HeytingLean.Noneism.KripkeFO.update D ρ x d)
                        (fun (x : HeytingLean.Noneism.KripkeFO.Valuation D) =>
                          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M x v φ)
                        (@Eq.trans.{1} (HeytingLean.Noneism.KripkeFO.Valuation D)
                          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z
                            d)
                          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) x
                            d)
                          (@HeytingLean.Noneism.KripkeFO.update D ρ x d)
                          (@congrArg.{1, 1} HeytingLean.Noneism.Var (HeytingLean.Noneism.KripkeFO.Valuation D) z x
                            (fun (x_1 : HeytingLean.Noneism.Var) =>
                              @HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y))
                                x_1 d)
                            hzx)
                          (@HeytingLean.Noneism.KripkeFO.update_update_same D ρ x (ρ y) d))))
                h;
            have this :
              ∀ (u : W),
                @LE.le.{0} W (@Preorder.toLE.{0} W inst) w u →
                  ∀ (e : D),
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ y e) u
                      (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ) :=
              fun (u : W) (hwu : @LE.le.{0} W (@Preorder.toLE.{0} W inst) w u) (e : D) =>
              have hEBase :
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x e) u φ :=
                hAll u hwu e;
              have hEWithY :
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x e) y e) u φ :=
                @Iff.mpr
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x e) y e) u φ)
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x e) u φ)
                  (@HeytingLean.Noneism.KripkeFO.forces_update_of_not_mem_varsFormula σ W inst D M
                    (@HeytingLean.Noneism.KripkeFO.update D ρ x e) y e u φ hyφ)
                  hEBase;
              have hEComm :
                @Eq.{1} (HeytingLean.Noneism.KripkeFO.Valuation D)
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y e) x e)
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x e) y e) :=
                @HeytingLean.Noneism.KripkeFO.update_comm D ρ y x e e hyx;
              have hECommForces :
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y e) x e) u φ :=
                @Eq.mpr.{0}
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y e) x e) u φ)
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x e) y e) u φ)
                  (@id.{0}
                    (@Eq.{1} Prop
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y e) x e) u φ)
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x e) y e) u
                        φ))
                    (@congrArg.{1, 1} (HeytingLean.Noneism.KripkeFO.Valuation D) Prop
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y e) x e)
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x e) y e)
                      (fun (x : HeytingLean.Noneism.KripkeFO.Valuation D) =>
                        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M x u φ)
                      hEComm))
                  hEWithY;
              @Iff.mpr
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ y e) u
                  (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y e) x
                    (@HeytingLean.Noneism.KripkeFO.update D ρ y e y))
                  u φ)
                (ih (@HeytingLean.Noneism.KripkeFO.update D ρ y e) hyφ u)
                (@Eq.mpr.{0}
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y e) x
                      (@HeytingLean.Noneism.KripkeFO.update D ρ y e y))
                    u φ)
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y e) x e) u φ)
                  (@id.{0}
                    (@Eq.{1} Prop
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y e) x
                          (@HeytingLean.Noneism.KripkeFO.update D ρ y e y))
                        u φ)
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y e) x e) u
                        φ))
                    (@congrArg.{1, 1} D Prop (@HeytingLean.Noneism.KripkeFO.update D ρ y e y) e
                      (fun (x_1 : D) =>
                        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ y e) x x_1)
                          u φ)
                      (@HeytingLean.Noneism.KripkeFO.update_self D ρ y e)))
                  hECommForces);
            @Eq.mpr.{0}
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.pi σ z φ)))
              (∀ (v : W),
                @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                  ∀ (d : D),
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ y d) v
                      (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
              (@id.{0}
                (@Eq.{1} Prop
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.pi σ z φ)))
                  (∀ (v : W),
                    @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                      ∀ (d : D),
                        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ y d)
                          v (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ)))
                (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) Prop
                  (@ite.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var z x)
                    (instDecidableEqNat z x)
                    (@HeytingLean.Noneism.Formula.pi σ y (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                    (@HeytingLean.Noneism.Formula.pi σ z (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ)))
                  (@HeytingLean.Noneism.Formula.pi σ y (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w)
                  (@ite_cond_eq_true.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var z x)
                    (instDecidableEqNat z x)
                    (@HeytingLean.Noneism.Formula.pi σ y (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                    (@HeytingLean.Noneism.Formula.pi σ z (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                    (@Eq.trans.{1} Prop (@Eq.{1} HeytingLean.Noneism.Var z x) (@Eq.{1} HeytingLean.Noneism.Var x x) True
                      (@congrArg.{1, 1} HeytingLean.Noneism.Var Prop z x
                        (fun (x_1 : HeytingLean.Noneism.Var) => @Eq.{1} HeytingLean.Noneism.Var x_1 x) hzx)
                      (@eq_self.{1} HeytingLean.Noneism.Var x)))))
              this)
        fun (hzx : Not (@Eq.{1} HeytingLean.Noneism.Var z x)) =>
        @Iff.intro
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
            (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.pi σ z φ)))
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
            (@HeytingLean.Noneism.Formula.pi σ z φ))
          (fun
              (h :
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                  (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.pi σ z φ)))
              (v : W) (hwv : @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v) (d : D) =>
            have hRenAll :
              ∀ (u : W),
                @LE.le.{0} W (@Preorder.toLE.{0} W inst) w u →
                  ∀ (e : D),
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z e) u
                      (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ) :=
              @Eq.mp.{0}
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                  (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.pi σ z φ)))
                (∀ (v : W),
                  @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                    ∀ (d : D),
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) v
                        (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) Prop
                  (@ite.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var z x)
                    (instDecidableEqNat z x)
                    (@HeytingLean.Noneism.Formula.pi σ y (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                    (@HeytingLean.Noneism.Formula.pi σ z (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ)))
                  (@HeytingLean.Noneism.Formula.pi σ z (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w)
                  (@ite_cond_eq_false.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var z x)
                    (instDecidableEqNat z x)
                    (@HeytingLean.Noneism.Formula.pi σ y (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                    (@HeytingLean.Noneism.Formula.pi σ z (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                    (@eq_false (@Eq.{1} HeytingLean.Noneism.Var z x) hzx)))
                h;
            have hd :
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                  (@HeytingLean.Noneism.KripkeFO.update D ρ z d y))
                v φ :=
              @Iff.mp
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) v
                  (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                    (@HeytingLean.Noneism.KripkeFO.update D ρ z d y))
                  v φ)
                (ih (@HeytingLean.Noneism.KripkeFO.update D ρ z d) hyφ v) (hRenAll v hwv d);
            have hyKeep : @Eq.{1} D (@HeytingLean.Noneism.KripkeFO.update D ρ z d y) (ρ y) :=
              @of_eq_true
                (@Eq.{1} D (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var y z) (instDecidableEqNat y z) d (ρ y)) (ρ y))
                (@Eq.trans.{1} Prop
                  (@Eq.{1} D (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var y z) (instDecidableEqNat y z) d (ρ y)) (ρ y))
                  (@Eq.{1} D (ρ y) (ρ y)) True
                  (@congrArg.{1, 1} D Prop
                    (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var y z) (instDecidableEqNat y z) d (ρ y)) (ρ y)
                    (fun (x : D) => @Eq.{1} D x (ρ y))
                    (@ite_cond_eq_false.{1} D (@Eq.{1} HeytingLean.Noneism.Var y z) (instDecidableEqNat y z) d (ρ y)
                      (@eq_false (@Eq.{1} HeytingLean.Noneism.Var y z) hyz)))
                  (@eq_self.{1} D (ρ y)));
            have hd' :
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ y)) v φ :=
              @Eq.mp.{0}
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                    (@HeytingLean.Noneism.KripkeFO.update D ρ z d y))
                  v φ)
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ y)) v φ)
                (@congrArg.{1, 1} D Prop (@HeytingLean.Noneism.KripkeFO.update D ρ z d y) (ρ y)
                  (fun (x_1 : D) =>
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x x_1) v φ)
                  hyKeep)
                hd;
            have hComm :
              @Eq.{1} (HeytingLean.Noneism.KripkeFO.Valuation D)
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ y))
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z d) :=
              @HeytingLean.Noneism.KripkeFO.update_comm D ρ z x d (ρ y) hzx;
            have hOut :
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z d) v φ :=
              @Eq.mp.{0}
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ y)) v φ)
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z d) v φ)
                (@congrArg.{1, 1} (HeytingLean.Noneism.KripkeFO.Valuation D) Prop
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ y))
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z d)
                  (fun (x : HeytingLean.Noneism.KripkeFO.Valuation D) =>
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M x v φ)
                  hComm)
                hd';
            hOut)
          fun
            (h :
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) w
                (@HeytingLean.Noneism.Formula.pi σ z φ)) =>
          have hAll :
            ∀ (u : W),
              @LE.le.{0} W (@Preorder.toLE.{0} W inst) w u →
                ∀ (e : D),
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z e) u
                    φ :=
            h;
          have this :
            ∀ (u : W),
              @LE.le.{0} W (@Preorder.toLE.{0} W inst) w u →
                ∀ (e : D),
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z e) u
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ) :=
            fun (u : W) (hwu : @LE.le.{0} W (@Preorder.toLE.{0} W inst) w u) (e : D) =>
            have hCommE :
              @Eq.{1} (HeytingLean.Noneism.KripkeFO.Valuation D)
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z e) x (ρ y))
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z e) :=
              @HeytingLean.Noneism.KripkeFO.update_comm D ρ z x e (ρ y) hzx;
            have hBase :
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z e) x (ρ y)) u φ :=
              @Eq.mpr.{0}
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z e) x (ρ y)) u φ)
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z e) u φ)
                (@id.{0}
                  (@Eq.{1} Prop
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z e) x (ρ y)) u
                      φ)
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z e) u
                      φ))
                  (@congrArg.{1, 1} (HeytingLean.Noneism.KripkeFO.Valuation D) Prop
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z e) x (ρ y))
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ y)) z e)
                    (fun (x : HeytingLean.Noneism.KripkeFO.Valuation D) =>
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M x u φ)
                    hCommE))
                (hAll u hwu e);
            have hyKeepE : @Eq.{1} D (@HeytingLean.Noneism.KripkeFO.update D ρ z e y) (ρ y) :=
              @of_eq_true
                (@Eq.{1} D (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var y z) (instDecidableEqNat y z) e (ρ y)) (ρ y))
                (@Eq.trans.{1} Prop
                  (@Eq.{1} D (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var y z) (instDecidableEqNat y z) e (ρ y)) (ρ y))
                  (@Eq.{1} D (ρ y) (ρ y)) True
                  (@congrArg.{1, 1} D Prop
                    (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var y z) (instDecidableEqNat y z) e (ρ y)) (ρ y)
                    (fun (x : D) => @Eq.{1} D x (ρ y))
                    (@ite_cond_eq_false.{1} D (@Eq.{1} HeytingLean.Noneism.Var y z) (instDecidableEqNat y z) e (ρ y)
                      (@eq_false (@Eq.{1} HeytingLean.Noneism.Var y z) hyz)))
                  (@eq_self.{1} D (ρ y)));
            have hLift :
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z e) x
                  (@HeytingLean.Noneism.KripkeFO.update D ρ z e y))
                u φ :=
              @Eq.mpr.{0}
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z e) x
                    (@HeytingLean.Noneism.KripkeFO.update D ρ z e y))
                  u φ)
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z e) x (ρ y)) u φ)
                (@id.{0}
                  (@Eq.{1} Prop
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z e) x
                        (@HeytingLean.Noneism.KripkeFO.update D ρ z e y))
                      u φ)
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z e) x (ρ y)) u
                      φ))
                  (@congrArg.{1, 1} D Prop (@HeytingLean.Noneism.KripkeFO.update D ρ z e y) (ρ y)
                    (fun (x_1 : D) =>
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z e) x x_1) u
                        φ)
                    hyKeepE))
                hBase;
            @Iff.mpr
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z e) u
                (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z e) x
                  (@HeytingLean.Noneism.KripkeFO.update D ρ z e y))
                u φ)
              (ih (@HeytingLean.Noneism.KripkeFO.update D ρ z e) hyφ u) hLift;
          @Eq.mpr.{0}
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
              (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.pi σ z φ)))
            (∀ (v : W),
              @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                ∀ (d : D),
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) v
                    (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
            (@id.{0}
              (@Eq.{1} Prop
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                  (@HeytingLean.Noneism.Syntax.renameFormula σ x y (@HeytingLean.Noneism.Formula.pi σ z φ)))
                (∀ (v : W),
                  @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                    ∀ (d : D),
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) v
                        (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ)))
              (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) Prop
                (@ite.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x)
                  (@HeytingLean.Noneism.Formula.pi σ y (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                  (@HeytingLean.Noneism.Formula.pi σ z (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ)))
                (@HeytingLean.Noneism.Formula.pi σ z (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w)
                (@ite_cond_eq_false.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var z x)
                  (instDecidableEqNat z x)
                  (@HeytingLean.Noneism.Formula.pi σ y (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                  (@HeytingLean.Noneism.Formula.pi σ z (@HeytingLean.Noneism.Syntax.renameFormula σ x y φ))
                  (@eq_false (@Eq.{1} HeytingLean.Noneism.Var z x) hzx))))
            this)
    φ ρ
theorem _root_.HeytingLean.Noneism.KripkeFO.forces_substFormula_var_of_not_mem_boundVars_or_not_mem_fvFormula : ∀ {σ W : Type}
  [inst : Preorder.{0} W] {D : Type} (M : @HeytingLean.Noneism.KripkeFO.Model W σ D inst)
  (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W) (x a : HeytingLean.Noneism.Var)
  (φ : HeytingLean.Noneism.Formula σ),
  Or
      (Not
        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
          (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.boundVars σ φ) a))
      (Not
        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
          (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x)) →
    Iff
      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w φ) :=
fun {σ W : Type} [inst : Preorder.{0} W] {D : Type} (M : @HeytingLean.Noneism.KripkeFO.Model W σ D inst)
    (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W) (x a : HeytingLean.Noneism.Var)
    (φ : HeytingLean.Noneism.Formula σ)
    (h :
      Or
        (Not
          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
            (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.boundVars σ φ) a))
        (Not
          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
            (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))) =>
  @Or.casesOn
    (Not
      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
        (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.boundVars σ φ) a))
    (Not
      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
        (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))
    (fun
        (x_1 :
          Or
            (Not
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.boundVars σ φ) a))
            (Not
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))) =>
      Iff
        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w φ))
    h
    (fun
        (ha :
          Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.boundVars σ φ) a)) =>
      @HeytingLean.Noneism.KripkeFO.forces_substFormula_var_of_not_mem_boundVars σ W inst D M ρ w x a φ ha)
    fun
      (hx :
        Not
          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
            (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x)) =>
    have hSubEq :
      @Eq.{1} (HeytingLean.Noneism.Formula σ)
        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ) φ :=
      @HeytingLean.Noneism.Syntax.substFormula_eq_self_of_not_mem_fvFormula σ x (HeytingLean.Noneism.Term.var a) φ hx;
    have hUpdateIrrel :
      Iff (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w φ)
        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w φ) :=
      @HeytingLean.Noneism.KripkeFO.forces_update_of_not_mem_fvFormula σ W inst D M ρ x (ρ a) φ hx w;
    @Eq.mpr.{0}
      (Iff
        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w φ))
      (Iff (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w φ)
        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w φ))
      (@id.{0}
        (@Eq.{1} Prop
          (Iff
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w φ))
          (Iff (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w φ)
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w φ)))
        (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) Prop
          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ) φ
          (fun (x_1 : HeytingLean.Noneism.Formula σ) =>
            Iff (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w x_1)
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                φ))
          hSubEq))
      (@Iff.symm
        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w φ)
        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w φ) hUpdateIrrel)
theorem _root_.HeytingLean.Noneism.KripkeFO.forces_substFormula_var_sigma_capture : ∀ {σ W : Type} [inst : Preorder.{0} W]
  {D : Type} (M : @HeytingLean.Noneism.KripkeFO.Model W σ D inst) (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W)
  (x a : HeytingLean.Noneism.Var) (φ : HeytingLean.Noneism.Formula σ) (hax : @Ne.{1} HeytingLean.Noneism.Var a x)
  (hx :
    @Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x),
  Iff
    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
        (@HeytingLean.Noneism.Formula.sigma σ a φ)))
    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
      (@HeytingLean.Noneism.Formula.sigma σ a φ)) :=
fun {σ W : Type} [inst : Preorder.{0} W] {D : Type} (M : @HeytingLean.Noneism.KripkeFO.Model W σ D inst)
    (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W) (x a : HeytingLean.Noneism.Var)
    (φ : HeytingLean.Noneism.Formula σ) (hax : @Ne.{1} HeytingLean.Noneism.Var a x)
    (hx :
      @Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
        (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x) =>
  let avoid : Finset.{0} HeytingLean.Noneism.Var :=
    @Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)));
  let z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
  have hz'NotAvoid :
    Not
      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
        (@Finset.instMembership.{0} HeytingLean.Noneism.Var) avoid z') :=
    @Eq.mpr.{0}
      (Not
        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
          (@Finset.instMembership.{0} HeytingLean.Noneism.Var) avoid z'))
      (And
        (Not
          (@Eq.{1} HeytingLean.Noneism.Var
            (HeytingLean.Noneism.Syntax.freshVar
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
            x))
        (And
          (Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
              (HeytingLean.Noneism.Syntax.freshVar
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
          (Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
              (HeytingLean.Noneism.Syntax.freshVar
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
      (@id.{0}
        (@Eq.{1} Prop
          (Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var) avoid z'))
          (And
            (Not
              (@Eq.{1} HeytingLean.Noneism.Var
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                x))
            (And
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))))))
        (@Eq.trans.{1} Prop
          (Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
              (HeytingLean.Noneism.Syntax.freshVar
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
          (And
            (Not
              (@Eq.{1} HeytingLean.Noneism.Var
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                x))
            (Not
              (Or
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
          (And
            (Not
              (@Eq.{1} HeytingLean.Noneism.Var
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                x))
            (And
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
          (@Eq.trans.{1} Prop
            (Not
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
            (Not
              (Or
                (@Eq.{1} HeytingLean.Noneism.Var
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                  x)
                (Or
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
            (And
              (Not
                (@Eq.{1} HeytingLean.Noneism.Var
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                  x))
              (Not
                (Or
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
            (@congrArg.{1, 1} Prop Prop
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
              (Or
                (@Eq.{1} HeytingLean.Noneism.Var
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                  x)
                (Or
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))))
              Not
              (@Eq.trans.{1} Prop
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                (Or
                  (@Eq.{1} HeytingLean.Noneism.Var
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                    x)
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
                (Or
                  (@Eq.{1} HeytingLean.Noneism.Var
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                    x)
                  (Or
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.freshVar
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                      (HeytingLean.Noneism.Syntax.freshVar
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))))
                (@Finset.mem_insert._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                  x)
                (@congrArg.{1, 1} Prop Prop
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                  (Or
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.freshVar
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                      (HeytingLean.Noneism.Syntax.freshVar
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
                  (Or
                    (@Eq.{1} HeytingLean.Noneism.Var
                      (HeytingLean.Noneism.Syntax.freshVar
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                      x))
                  (@Finset.mem_union._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
            (@not_or._simp_1
              (@Eq.{1} HeytingLean.Noneism.Var
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                x)
              (Or
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
          (@congrArg.{1, 1} Prop Prop
            (Not
              (Or
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))))
            (And
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))))
            (And
              (Not
                (@Eq.{1} HeytingLean.Noneism.Var
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                  x)))
            (@not_or._simp_1
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))))))
      (@Eq.mp.{0}
        (Not
          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
            (@Finset.instMembership.{0} HeytingLean.Noneism.Var) avoid (HeytingLean.Noneism.Syntax.freshVar avoid)))
        (And
          (Not
            (@Eq.{1} HeytingLean.Noneism.Var
              (HeytingLean.Noneism.Syntax.freshVar
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
              x))
          (And
            (Not
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
            (Not
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
        (@Eq.trans.{1} Prop
          (Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
              (HeytingLean.Noneism.Syntax.freshVar
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
          (And
            (Not
              (@Eq.{1} HeytingLean.Noneism.Var
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                x))
            (Not
              (Or
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
          (And
            (Not
              (@Eq.{1} HeytingLean.Noneism.Var
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                x))
            (And
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
          (@Eq.trans.{1} Prop
            (Not
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
            (Not
              (Or
                (@Eq.{1} HeytingLean.Noneism.Var
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                  x)
                (Or
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
            (And
              (Not
                (@Eq.{1} HeytingLean.Noneism.Var
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                  x))
              (Not
                (Or
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
            (@congrArg.{1, 1} Prop Prop
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
              (Or
                (@Eq.{1} HeytingLean.Noneism.Var
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                  x)
                (Or
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))))
              Not
              (@Eq.trans.{1} Prop
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                (Or
                  (@Eq.{1} HeytingLean.Noneism.Var
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                    x)
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
                (Or
                  (@Eq.{1} HeytingLean.Noneism.Var
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                    x)
                  (Or
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.freshVar
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                      (HeytingLean.Noneism.Syntax.freshVar
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))))
                (@Finset.mem_insert._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                  x)
                (@congrArg.{1, 1} Prop Prop
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                  (Or
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.freshVar
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                      (HeytingLean.Noneism.Syntax.freshVar
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
                  (Or
                    (@Eq.{1} HeytingLean.Noneism.Var
                      (HeytingLean.Noneism.Syntax.freshVar
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                      x))
                  (@Finset.mem_union._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
            (@not_or._simp_1
              (@Eq.{1} HeytingLean.Noneism.Var
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                x)
              (Or
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
          (@congrArg.{1, 1} Prop Prop
            (Not
              (Or
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))))
            (And
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))))
            (And
              (Not
                (@Eq.{1} HeytingLean.Noneism.Var
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                  x)))
            (@not_or._simp_1
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
        (HeytingLean.Noneism.Syntax.freshVar_not_mem avoid));
  have hz'NotVars :
    Not
      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
        (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) z') :=
    fun
      (hzv :
        @Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
          (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) z') =>
    hz'NotAvoid
      (@of_eq_true
        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
          (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
            (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
            (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
              (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
          z')
        (@Eq.trans.{1} Prop
          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
            (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
              (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
            z')
          (Or (@Eq.{1} HeytingLean.Noneism.Var z' x)
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
              z'))
          True
          (@Finset.mem_insert._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
            (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
              (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
            z' x)
          (@Eq.trans.{1} Prop
            (Or (@Eq.{1} HeytingLean.Noneism.Var z' x)
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                z'))
            (Or (@Eq.{1} HeytingLean.Noneism.Var z' x) True) True
            (@congrArg.{1, 1} Prop Prop
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                z')
              True (Or (@Eq.{1} HeytingLean.Noneism.Var z' x))
              (@Eq.trans.{1} Prop
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                  z')
                (Or
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    z')
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z'))
                True
                (@Finset.mem_union._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z')
                (@Eq.trans.{1} Prop
                  (Or
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      z')
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z'))
                  (Or True
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z'))
                  True
                  (@congrArg.{1, 1} Prop Prop
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      z')
                    True
                    (fun (x : Prop) =>
                      Or x
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z'))
                    (@eq_true
                      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ) z')
                      hzv))
                  (true_or
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z')))))
            (or_true (@Eq.{1} HeytingLean.Noneism.Var z' x)))));
  have hz'neX : @Ne.{1} HeytingLean.Noneism.Var z' x := fun (hzx' : @Eq.{1} HeytingLean.Noneism.Var z' x) =>
    hz'NotAvoid
      (@of_eq_true
        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
          (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
            (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
            (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
              (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
          z')
        (@Eq.trans.{1} Prop
          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
            (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
              (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
            z')
          (Or (@Eq.{1} HeytingLean.Noneism.Var x x)
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
              x))
          True
          (@Eq.trans.{1} Prop
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
              z')
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
              x)
            (Or (@Eq.{1} HeytingLean.Noneism.Var x x)
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                x))
            (@congrArg.{1, 1} HeytingLean.Noneism.Var Prop z' x
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
              hzx')
            (@Finset.mem_insert._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
              (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
              x x))
          (@Eq.trans.{1} Prop
            (Or (@Eq.{1} HeytingLean.Noneism.Var x x)
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                x))
            (Or True
              (Or
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) x)
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) x)))
            True
            (@congr.{1, 1} Prop Prop (Or (@Eq.{1} HeytingLean.Noneism.Var x x)) (Or True)
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                x)
              (Or
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) x)
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) x))
              (@congrArg.{1, 1} Prop ((b : Prop) → Prop) (@Eq.{1} HeytingLean.Noneism.Var x x) True Or
                (@eq_self.{1} HeytingLean.Noneism.Var x))
              (@Finset.mem_union._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) x))
            (true_or
              (Or
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) x)
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) x))))));
  have hz'neA : @Ne.{1} HeytingLean.Noneism.Var z' a := fun (hza' : @Eq.{1} HeytingLean.Noneism.Var z' a) =>
    hz'NotAvoid
      (@of_eq_true
        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
          (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
            (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
            (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
              (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
              (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)))
          z')
        (@Eq.trans.{1} Prop
          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
            (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
              (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)))
            z')
          (Or (@Eq.{1} HeytingLean.Noneism.Var a x)
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) a
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
              a))
          True
          (@Eq.trans.{1} Prop
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)))
              z')
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) a
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)))
              a)
            (Or (@Eq.{1} HeytingLean.Noneism.Var a x)
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) a
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
                a))
            (@congr.{1, 1} HeytingLean.Noneism.Var Prop
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a))))
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) a
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ))))
              z' a
              (@congrArg.{1, 1} (Finset.{0} HeytingLean.Noneism.Var) (HeytingLean.Noneism.Var → Prop)
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a))
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) a
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
                (fun (x_1 : Finset.{0} HeytingLean.Noneism.Var) =>
                  @Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x x_1))
                (@Finset.union_singleton.{0} HeytingLean.Noneism.Var instDecidableEqNat a
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)))
              hza')
            (@Finset.mem_insert._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) a
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
              a x))
          (@Eq.trans.{1} Prop
            (Or (@Eq.{1} HeytingLean.Noneism.Var a x)
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) a
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
                a))
            (Or (@Eq.{1} HeytingLean.Noneism.Var a x) True) True
            (@congrArg.{1, 1} Prop Prop
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) a
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
                a)
              True (Or (@Eq.{1} HeytingLean.Noneism.Var a x))
              (@Eq.trans.{1} Prop
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) a
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
                  a)
                (Or (@Eq.{1} HeytingLean.Noneism.Var a a)
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    a))
                True
                (@Finset.mem_insert._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ) a a)
                (@Eq.trans.{1} Prop
                  (Or (@Eq.{1} HeytingLean.Noneism.Var a a)
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      a))
                  (Or True
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      a))
                  True
                  (@congrArg.{1, 1} Prop Prop (@Eq.{1} HeytingLean.Noneism.Var a a) True
                    (fun (x : Prop) =>
                      Or x
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ) a))
                    (@eq_self.{1} HeytingLean.Noneism.Var a))
                  (true_or
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      a)))))
            (or_true (@Eq.{1} HeytingLean.Noneism.Var a x)))));
  have haNeZ' : @Ne.{1} HeytingLean.Noneism.Var a z' := @Ne.symm.{1} HeytingLean.Noneism.Var z' a hz'neA;
  have hBoundRen :
    Not
      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
        (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
        (@HeytingLean.Noneism.Syntax.boundVars σ (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)) a) :=
    _root_.HeytingLean.Noneism.Syntax.not_mem_boundVars_renameFormula_target σ a z' hz'neA φ;
  have hguard :
    And
      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
        (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
        (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x) :=
    @And.intro
      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
        (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
        (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x)
      (@of_eq_true
        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
          (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
            (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)
          a)
        (@Eq.trans.{1} Prop
          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
            (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)
            a)
          (@Eq.{1} HeytingLean.Noneism.Var a a) True (@Finset.mem_singleton._simp_1.{0} HeytingLean.Noneism.Var a a)
          (@eq_self.{1} HeytingLean.Noneism.Var a)))
      hx;
  have hSubstSigma :
    @Eq.{1} (HeytingLean.Noneism.Formula σ)
      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
        (@HeytingLean.Noneism.Formula.sigma σ a φ))
      (@HeytingLean.Noneism.Formula.sigma σ z'
        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
          (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))) :=
    @of_eq_true
      (@Eq.{1} (HeytingLean.Noneism.Formula σ)
        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
          (@HeytingLean.Noneism.Formula.sigma σ a φ))
        (@HeytingLean.Noneism.Formula.sigma σ
          (HeytingLean.Noneism.Syntax.freshVar
            (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
              (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
            (@HeytingLean.Noneism.Syntax.renameFormula σ a
              (HeytingLean.Noneism.Syntax.freshVar
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
              φ))))
      (@Eq.trans.{1} Prop
        (@Eq.{1} (HeytingLean.Noneism.Formula σ)
          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
            (@HeytingLean.Noneism.Formula.sigma σ a φ))
          (@HeytingLean.Noneism.Formula.sigma σ
            (HeytingLean.Noneism.Syntax.freshVar
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Syntax.renameFormula σ a
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                φ))))
        (@Eq.{1} (HeytingLean.Noneism.Formula σ)
          (@HeytingLean.Noneism.Formula.sigma σ
            (HeytingLean.Noneism.Syntax.freshVar
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Syntax.renameFormula σ a
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                φ)))
          (@HeytingLean.Noneism.Formula.sigma σ
            (HeytingLean.Noneism.Syntax.freshVar
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Syntax.renameFormula σ a
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                φ))))
        True
        (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) Prop
          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
            (@HeytingLean.Noneism.Formula.sigma σ a φ))
          (@HeytingLean.Noneism.Formula.sigma σ
            (HeytingLean.Noneism.Syntax.freshVar
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Syntax.renameFormula σ a
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                φ)))
          (fun (x_1 : HeytingLean.Noneism.Formula σ) =>
            @Eq.{1} (HeytingLean.Noneism.Formula σ) x_1
              (@HeytingLean.Noneism.Formula.sigma σ
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                  (@HeytingLean.Noneism.Syntax.renameFormula σ a
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                    φ))))
          (@Eq.trans.{1} (HeytingLean.Noneism.Formula σ)
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Formula.sigma σ a φ))
            (@ite.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var a x) (instDecidableEqNat a x)
              (@HeytingLean.Noneism.Formula.sigma σ a φ)
              (@ite.{1} (HeytingLean.Noneism.Formula σ)
                (And
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))
                (@instDecidableAnd
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x)
                  (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat a
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                  (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat x
                    (@HeytingLean.Noneism.Syntax.fvFormula σ φ)))
                (have avoid : Finset.{0} HeytingLean.Noneism.Var :=
                  @Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a));
                have z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
                @HeytingLean.Noneism.Formula.sigma σ z'
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                    (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))
                (@HeytingLean.Noneism.Formula.sigma σ a
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))))
            (@HeytingLean.Noneism.Formula.sigma σ
              (HeytingLean.Noneism.Syntax.freshVar
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                (@HeytingLean.Noneism.Syntax.renameFormula σ a
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                  φ)))
            (@HeytingLean.Noneism.Syntax.substFormula.eq_9 σ x (HeytingLean.Noneism.Term.var a) a φ)
            (@Eq.trans.{1} (HeytingLean.Noneism.Formula σ)
              (@ite.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var a x) (instDecidableEqNat a x)
                (@HeytingLean.Noneism.Formula.sigma σ a φ)
                (@ite.{1} (HeytingLean.Noneism.Formula σ)
                  (And
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ)
                      x))
                  (@instDecidableAnd
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ)
                      x)
                    (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat a
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                    (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat x
                      (@HeytingLean.Noneism.Syntax.fvFormula σ φ)))
                  (have avoid : Finset.{0} HeytingLean.Noneism.Var :=
                    @Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a));
                  have z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
                  @HeytingLean.Noneism.Formula.sigma σ z'
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                      (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))
                  (@HeytingLean.Noneism.Formula.sigma σ a
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))))
              (@ite.{1} (HeytingLean.Noneism.Formula σ)
                (And
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))
                (@instDecidableAnd
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x)
                  (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat a
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                  (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat x
                    (@HeytingLean.Noneism.Syntax.fvFormula σ φ)))
                (have avoid : Finset.{0} HeytingLean.Noneism.Var :=
                  @Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a));
                have z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
                @HeytingLean.Noneism.Formula.sigma σ z'
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                    (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))
                (@HeytingLean.Noneism.Formula.sigma σ a
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))
              (@HeytingLean.Noneism.Formula.sigma σ
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                  (@HeytingLean.Noneism.Syntax.renameFormula σ a
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                    φ)))
              (@ite_cond_eq_false.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var a x)
                (instDecidableEqNat a x) (@HeytingLean.Noneism.Formula.sigma σ a φ)
                (@ite.{1} (HeytingLean.Noneism.Formula σ)
                  (And
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ)
                      x))
                  (@instDecidableAnd
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ)
                      x)
                    (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat a
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                    (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat x
                      (@HeytingLean.Noneism.Syntax.fvFormula σ φ)))
                  (have avoid : Finset.{0} HeytingLean.Noneism.Var :=
                    @Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a));
                  have z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
                  @HeytingLean.Noneism.Formula.sigma σ z'
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                      (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))
                  (@HeytingLean.Noneism.Formula.sigma σ a
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))
                (@eq_false (@Eq.{1} HeytingLean.Noneism.Var a x) hax))
              (@Eq.trans.{1} (HeytingLean.Noneism.Formula σ)
                (@ite.{1} (HeytingLean.Noneism.Formula σ)
                  (And
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ)
                      x))
                  (@instDecidableAnd
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ)
                      x)
                    (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat a
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                    (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat x
                      (@HeytingLean.Noneism.Syntax.fvFormula σ φ)))
                  (have avoid : Finset.{0} HeytingLean.Noneism.Var :=
                    @Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a));
                  have z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
                  @HeytingLean.Noneism.Formula.sigma σ z'
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                      (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))
                  (@HeytingLean.Noneism.Formula.sigma σ a
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))
                (have avoid : Finset.{0} HeytingLean.Noneism.Var :=
                  @Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a));
                have z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
                @HeytingLean.Noneism.Formula.sigma σ z'
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                    (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))
                (@HeytingLean.Noneism.Formula.sigma σ
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                    (@HeytingLean.Noneism.Syntax.renameFormula σ a
                      (HeytingLean.Noneism.Syntax.freshVar
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                      φ)))
                (@ite_cond_eq_true.{1} (HeytingLean.Noneism.Formula σ)
                  (And
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ)
                      x))
                  (@instDecidableAnd
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ)
                      x)
                    (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat a
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                    (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat x
                      (@HeytingLean.Noneism.Syntax.fvFormula σ φ)))
                  (have avoid : Finset.{0} HeytingLean.Noneism.Var :=
                    @Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a));
                  have z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
                  @HeytingLean.Noneism.Formula.sigma σ z'
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                      (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))
                  (@HeytingLean.Noneism.Formula.sigma σ a
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                  (@Eq.trans.{1} Prop
                    (And
                      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ)
                        x))
                    (And True True) True
                    (@congr.{1, 1} Prop Prop
                      (And
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a))
                      (And True)
                      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ)
                        x)
                      True
                      (@congrArg.{1, 1} Prop ((b : Prop) → Prop)
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                        True And
                        (@eq_true
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                          hguard.1))
                      (@eq_true
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x)
                        hguard.2))
                    (and_self True)))
                (@congr.{1, 1} (HeytingLean.Noneism.Formula σ) (HeytingLean.Noneism.Formula σ)
                  (@HeytingLean.Noneism.Formula.sigma σ
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)))))
                  (@HeytingLean.Noneism.Formula.sigma σ
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                    (@HeytingLean.Noneism.Syntax.renameFormula σ a
                      (HeytingLean.Noneism.Syntax.freshVar
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                          (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                            (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a))))
                      φ))
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                    (@HeytingLean.Noneism.Syntax.renameFormula σ a
                      (HeytingLean.Noneism.Syntax.freshVar
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                      φ))
                  (@congrArg.{1, 1} (Finset.{0} HeytingLean.Noneism.Var)
                    ((φ : HeytingLean.Noneism.Formula σ) → HeytingLean.Noneism.Formula σ)
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)))
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
                    (fun (x : Finset.{0} HeytingLean.Noneism.Var) =>
                      @HeytingLean.Noneism.Formula.sigma σ (HeytingLean.Noneism.Syntax.freshVar x))
                    (@Eq.trans.{1} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)))
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                          (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)))
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
                      (@Finset.union_insert.{0} HeytingLean.Noneism.Var instDecidableEqNat x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                        (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a))
                      (@congrArg.{1, 1} (Finset.{0} HeytingLean.Noneism.Var) (Finset.{0} HeytingLean.Noneism.Var)
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                          (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a))
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x)
                        (@Eq.trans.{1} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                              (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                            (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a))
                          (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) a
                            (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                              (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                          (@Finset.union_singleton.{0} HeytingLean.Noneism.Var instDecidableEqNat a
                            (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                              (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
                          (@Finset.insert_eq_of_mem.{0} HeytingLean.Noneism.Var instDecidableEqNat
                            (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                              (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                            a
                            (@of_eq_true
                              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                                a)
                              (@Eq.trans.{1} Prop
                                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                                  a)
                                (Or
                                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ) a)
                                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a))
                                True
                                (@Finset.mem_union._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
                                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                                (@Eq.trans.{1} Prop
                                  (Or
                                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ) a)
                                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a))
                                  (Or
                                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ) a)
                                    True)
                                  True
                                  (@congrArg.{1, 1} Prop Prop
                                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                                    True
                                    (Or
                                      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var
                                        (Finset.{0} HeytingLean.Noneism.Var)
                                        (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ) a))
                                    (@eq_true
                                      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var
                                        (Finset.{0} HeytingLean.Noneism.Var)
                                        (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                                      hguard.1))
                                  (or_true
                                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ) a))))))))))
                  (@congrArg.{1, 1} (Finset.{0} HeytingLean.Noneism.Var) (HeytingLean.Noneism.Formula σ)
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)))
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
                    (fun (x_1 : Finset.{0} HeytingLean.Noneism.Var) =>
                      @HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                        (@HeytingLean.Noneism.Syntax.renameFormula σ a (HeytingLean.Noneism.Syntax.freshVar x_1) φ))
                    (@Eq.trans.{1} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)))
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                          (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)))
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
                      (@Finset.union_insert.{0} HeytingLean.Noneism.Var instDecidableEqNat x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                        (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a))
                      (@congrArg.{1, 1} (Finset.{0} HeytingLean.Noneism.Var) (Finset.{0} HeytingLean.Noneism.Var)
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                          (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a))
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x)
                        (@Eq.trans.{1} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                              (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                            (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a))
                          (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) a
                            (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                              (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                          (@Finset.union_singleton.{0} HeytingLean.Noneism.Var instDecidableEqNat a
                            (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                              (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
                          (@Finset.insert_eq_of_mem.{0} HeytingLean.Noneism.Var instDecidableEqNat
                            (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                              (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                            a
                            (@of_eq_true
                              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                                a)
                              (@Eq.trans.{1} Prop
                                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                                  a)
                                (Or
                                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ) a)
                                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a))
                                True
                                (@Finset.mem_union._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
                                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                                (@Eq.trans.{1} Prop
                                  (Or
                                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ) a)
                                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a))
                                  (Or
                                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ) a)
                                    True)
                                  True
                                  (@congrArg.{1, 1} Prop Prop
                                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                                    True
                                    (Or
                                      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var
                                        (Finset.{0} HeytingLean.Noneism.Var)
                                        (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ) a))
                                    (@eq_true
                                      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var
                                        (Finset.{0} HeytingLean.Noneism.Var)
                                        (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                                      hguard.1))
                                  (or_true
                                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ) a)))))))))))))))
        (@eq_self.{1} (HeytingLean.Noneism.Formula σ)
          (@HeytingLean.Noneism.Formula.sigma σ
            (HeytingLean.Noneism.Syntax.freshVar
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Syntax.renameFormula σ a
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                φ)))));
  @Iff.intro
    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
        (@HeytingLean.Noneism.Formula.sigma σ a φ)))
    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
      (@HeytingLean.Noneism.Formula.sigma σ a φ))
    (fun
        (hSub :
          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Formula.sigma σ a φ))) =>
      have hSub' :
        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
          (@HeytingLean.Noneism.Formula.sigma σ z'
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))) :=
        @Eq.mp.{0}
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Formula.sigma σ a φ)))
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
            (@HeytingLean.Noneism.Formula.sigma σ z'
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))))
          (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) Prop
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Formula.sigma σ a φ))
            (@HeytingLean.Noneism.Formula.sigma σ z'
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w) hSubstSigma)
          hSub;
      @Exists.casesOn.{1} D
        (fun (d : D) =>
          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) w
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))
        (fun
            (x_1 :
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Formula.sigma σ z'
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                    (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))) =>
          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
            (@HeytingLean.Noneism.Formula.sigma σ a φ))
        hSub'
        fun (d : D)
          (hd :
            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) w
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))) =>
        @Exists.intro.{1} D
          (fun (d : D) =>
            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) w φ)
          d
          (have hRenSub :
            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x
                (@HeytingLean.Noneism.KripkeFO.update D ρ z' d a))
              w (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ) :=
            @Iff.mp
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) w
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                  (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x
                  (@HeytingLean.Noneism.KripkeFO.update D ρ z' d a))
                w (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
              (@HeytingLean.Noneism.KripkeFO.forces_substFormula_var_of_not_mem_boundVars σ W inst D M
                (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) w x a
                (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ) hBoundRen)
              hd;
          have hAVal : @Eq.{1} D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d a) (ρ a) :=
            @of_eq_true
              (@Eq.{1} D (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z') (instDecidableEqNat a z') d (ρ a)) (ρ a))
              (@Eq.trans.{1} Prop
                (@Eq.{1} D (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z') (instDecidableEqNat a z') d (ρ a)) (ρ a))
                (@Eq.{1} D (ρ a) (ρ a)) True
                (@congrArg.{1, 1} D Prop
                  (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z') (instDecidableEqNat a z') d (ρ a)) (ρ a)
                  (fun (x : D) => @Eq.{1} D x (ρ a))
                  (@ite_cond_eq_false.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z') (instDecidableEqNat a z') d (ρ a)
                    (@eq_false (@Eq.{1} HeytingLean.Noneism.Var a z') haNeZ')))
                (@eq_self.{1} D (ρ a)));
          have hRen :
            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x (ρ a)) w
              (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ) :=
            @Eq.mp.{0}
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x
                  (@HeytingLean.Noneism.KripkeFO.update D ρ z' d a))
                w (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x (ρ a)) w
                (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
              (@congrArg.{1, 1} D Prop (@HeytingLean.Noneism.KripkeFO.update D ρ z' d a) (ρ a)
                (fun (x_1 : D) =>
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x x_1) w
                    (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
                hAVal)
              hRenSub;
          have hComm :
            @Eq.{1} (HeytingLean.Noneism.KripkeFO.Valuation D)
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x (ρ a))
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) :=
            @HeytingLean.Noneism.KripkeFO.update_comm D ρ z' x d (ρ a) hz'neX;
          have hRen' :
            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) w
              (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ) :=
            @Eq.mp.{0}
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x (ρ a)) w
                (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) w
                (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
              (@congrArg.{1, 1} (HeytingLean.Noneism.KripkeFO.Valuation D) Prop
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x (ρ a))
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d)
                (fun (x : HeytingLean.Noneism.KripkeFO.Valuation D) =>
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M x w
                    (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
                hComm)
              hRen;
          have hOrigWithFresh :
            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
              (@HeytingLean.Noneism.KripkeFO.update D
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d z'))
              w φ :=
            @Iff.mp
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) w
                (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d z'))
                w φ)
              (@HeytingLean.Noneism.KripkeFO.forces_renameFormula_of_not_mem_varsFormula σ W inst D M
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a z' φ
                hz'NotVars w)
              hRen';
          have hz'Val :
            @Eq.{1} D
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d z') d :=
            @of_eq_true
              (@Eq.{1} D
                (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z' z') (instDecidableEqNat z' z') d
                  (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a) z'))
                d)
              (@Eq.trans.{1} Prop
                (@Eq.{1} D
                  (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z' z') (instDecidableEqNat z' z') d
                    (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a) z'))
                  d)
                (@Eq.{1} D d d) True
                (@congrArg.{1, 1} D Prop
                  (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z' z') (instDecidableEqNat z' z') d
                    (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a) z'))
                  d (fun (x : D) => @Eq.{1} D x d)
                  (@ite_cond_eq_true.{1} D (@Eq.{1} HeytingLean.Noneism.Var z' z') (instDecidableEqNat z' z') d
                    (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a) z') (@eq_self.{1} HeytingLean.Noneism.Var z')))
                (@eq_self.{1} D d));
          have hOrigFresh :
            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
              (@HeytingLean.Noneism.KripkeFO.update D
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a d)
              w φ :=
            @Eq.mp.{0}
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d z'))
                w φ)
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a d)
                w φ)
              (@congrArg.{1, 1} D Prop
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d z') d
                (fun (x_1 : D) =>
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a
                      x_1)
                    w φ)
                (@HeytingLean.Noneism.KripkeFO.update_self D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d))
              hOrigWithFresh;
          have hSwap :
            @Eq.{1} (HeytingLean.Noneism.KripkeFO.Valuation D)
              (@HeytingLean.Noneism.KripkeFO.update D
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a d)
              (@HeytingLean.Noneism.KripkeFO.update D
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) z' d) :=
            @HeytingLean.Noneism.KripkeFO.update_comm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' a d d
              hz'neA;
          have hWithFresh :
            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
              (@HeytingLean.Noneism.KripkeFO.update D
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) z' d)
              w φ :=
            @Eq.mp.{0}
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a d)
                w φ)
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) z' d)
                w φ)
              (@congrArg.{1, 1} (HeytingLean.Noneism.KripkeFO.Valuation D) Prop
                (@HeytingLean.Noneism.KripkeFO.update D
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a d)
                (@HeytingLean.Noneism.KripkeFO.update D
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) z' d)
                (fun (x : HeytingLean.Noneism.KripkeFO.Valuation D) =>
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M x w φ)
                hSwap)
              hOrigFresh;
          @Iff.mp
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
              (@HeytingLean.Noneism.KripkeFO.update D
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) z' d)
              w φ)
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) w φ)
            (@HeytingLean.Noneism.KripkeFO.forces_update_of_not_mem_varsFormula σ W inst D M
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) z' d w φ
              hz'NotVars)
            hWithFresh))
    fun
      (a_1 :
        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
          (@HeytingLean.Noneism.Formula.sigma σ a φ)) =>
    @Exists.casesOn.{1} D
      (fun (d : D) =>
        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) w φ)
      (fun
          (x_1 :
            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
              (@HeytingLean.Noneism.Formula.sigma σ a φ)) =>
        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
            (@HeytingLean.Noneism.Formula.sigma σ a φ)))
      a_1
      fun (d : D)
        (hd :
          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) w φ) =>
      have hWithFresh :
        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
          (@HeytingLean.Noneism.KripkeFO.update D
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) z' d)
          w φ :=
        @Iff.mpr
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) z' d)
            w φ)
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) w φ)
          (@HeytingLean.Noneism.KripkeFO.forces_update_of_not_mem_varsFormula σ W inst D M
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) z' d w φ
            hz'NotVars)
          hd;
      have hSwap :
        @Eq.{1} (HeytingLean.Noneism.KripkeFO.Valuation D)
          (@HeytingLean.Noneism.KripkeFO.update D
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a d)
          (@HeytingLean.Noneism.KripkeFO.update D
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) z' d) :=
        @HeytingLean.Noneism.KripkeFO.update_comm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' a d d hz'neA;
      have hOrigFresh :
        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
          (@HeytingLean.Noneism.KripkeFO.update D
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a d)
          w φ :=
        @Eq.mpr.{0}
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a d)
            w φ)
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) z' d)
            w φ)
          (@id.{0}
            (@Eq.{1} Prop
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a d)
                w φ)
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) z' d)
                w φ))
            (@congrArg.{1, 1} (HeytingLean.Noneism.KripkeFO.Valuation D) Prop
              (@HeytingLean.Noneism.KripkeFO.update D
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a d)
              (@HeytingLean.Noneism.KripkeFO.update D
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) z' d)
              (fun (x : HeytingLean.Noneism.KripkeFO.Valuation D) =>
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M x w φ)
              hSwap))
          hWithFresh;
      have hz'Val :
        @Eq.{1} D (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d z')
          d :=
        @of_eq_true
          (@Eq.{1} D
            (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z' z') (instDecidableEqNat z' z') d
              (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a) z'))
            d)
          (@Eq.trans.{1} Prop
            (@Eq.{1} D
              (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z' z') (instDecidableEqNat z' z') d
                (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a) z'))
              d)
            (@Eq.{1} D d d) True
            (@congrArg.{1, 1} D Prop
              (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z' z') (instDecidableEqNat z' z') d
                (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a) z'))
              d (fun (x : D) => @Eq.{1} D x d)
              (@ite_cond_eq_true.{1} D (@Eq.{1} HeytingLean.Noneism.Var z' z') (instDecidableEqNat z' z') d
                (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a) z') (@eq_self.{1} HeytingLean.Noneism.Var z')))
            (@eq_self.{1} D d));
      have hOrigWithFresh :
        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
          (@HeytingLean.Noneism.KripkeFO.update D
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d z'))
          w φ :=
        @Eq.mpr.{0}
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d z'))
            w φ)
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a d)
            w φ)
          (@id.{0}
            (@Eq.{1} Prop
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d z'))
                w φ)
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a d)
                w φ))
            (@congrArg.{1, 1} D Prop
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d z') d
              (fun (x_1 : D) =>
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a
                    x_1)
                  w φ)
              (@HeytingLean.Noneism.KripkeFO.update_self D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d)))
          hOrigFresh;
      have hRen' :
        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) w
          (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ) :=
        @Iff.mpr
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) w
            (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d z'))
            w φ)
          (@HeytingLean.Noneism.KripkeFO.forces_renameFormula_of_not_mem_varsFormula σ W inst D M
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a z' φ
            hz'NotVars w)
          hOrigWithFresh;
      have hComm :
        @Eq.{1} (HeytingLean.Noneism.KripkeFO.Valuation D)
          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x (ρ a))
          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) :=
        @HeytingLean.Noneism.KripkeFO.update_comm D ρ z' x d (ρ a) hz'neX;
      have hRen :
        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x (ρ a)) w
          (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ) :=
        @Eq.mpr.{0}
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x (ρ a)) w
            (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) w
            (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
          (@id.{0}
            (@Eq.{1} Prop
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x (ρ a)) w
                (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) w
                (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))
            (@congrArg.{1, 1} (HeytingLean.Noneism.KripkeFO.Valuation D) Prop
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x (ρ a))
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d)
              (fun (x : HeytingLean.Noneism.KripkeFO.Valuation D) =>
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M x w
                  (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
              hComm))
          hRen';
      have hAVal : @Eq.{1} D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d a) (ρ a) :=
        @of_eq_true
          (@Eq.{1} D (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z') (instDecidableEqNat a z') d (ρ a)) (ρ a))
          (@Eq.trans.{1} Prop
            (@Eq.{1} D (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z') (instDecidableEqNat a z') d (ρ a)) (ρ a))
            (@Eq.{1} D (ρ a) (ρ a)) True
            (@congrArg.{1, 1} D Prop
              (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z') (instDecidableEqNat a z') d (ρ a)) (ρ a)
              (fun (x : D) => @Eq.{1} D x (ρ a))
              (@ite_cond_eq_false.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z') (instDecidableEqNat a z') d (ρ a)
                (@eq_false (@Eq.{1} HeytingLean.Noneism.Var a z') haNeZ')))
            (@eq_self.{1} D (ρ a)));
      have hRenSub :
        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x
            (@HeytingLean.Noneism.KripkeFO.update D ρ z' d a))
          w (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ) :=
        @Eq.mpr.{0}
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x
              (@HeytingLean.Noneism.KripkeFO.update D ρ z' d a))
            w (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x (ρ a)) w
            (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
          (@id.{0}
            (@Eq.{1} Prop
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x
                  (@HeytingLean.Noneism.KripkeFO.update D ρ z' d a))
                w (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x (ρ a)) w
                (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))
            (@congrArg.{1, 1} D Prop (@HeytingLean.Noneism.KripkeFO.update D ρ z' d a) (ρ a)
              (fun (x_1 : D) =>
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x x_1) w
                  (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
              hAVal))
          hRen;
      have hSubRen :
        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) w
          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
            (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)) :=
        @Iff.mpr
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) w
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x
              (@HeytingLean.Noneism.KripkeFO.update D ρ z' d a))
            w (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
          (@HeytingLean.Noneism.KripkeFO.forces_substFormula_var_of_not_mem_boundVars σ W inst D M
            (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) w x a (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)
            hBoundRen)
          hRenSub;
      have hSub' :
        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
          (@HeytingLean.Noneism.Formula.sigma σ z'
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))) :=
        @Exists.intro.{1} D
          (fun (d : D) =>
            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) w
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))
          d hSubRen;
      @Eq.mpr.{0}
        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
            (@HeytingLean.Noneism.Formula.sigma σ a φ)))
        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
          (@HeytingLean.Noneism.Formula.sigma σ z'
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))))
        (@id.{0}
          (@Eq.{1} Prop
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                (@HeytingLean.Noneism.Formula.sigma σ a φ)))
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
              (@HeytingLean.Noneism.Formula.sigma σ z'
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                  (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))))
          (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) Prop
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Formula.sigma σ a φ))
            (@HeytingLean.Noneism.Formula.sigma σ z'
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w) hSubstSigma))
        hSub'
theorem _root_.HeytingLean.Noneism.KripkeFO.forces_substFormula_var_pi_capture : ∀ {σ W : Type} [inst : Preorder.{0} W]
  {D : Type} (M : @HeytingLean.Noneism.KripkeFO.Model W σ D inst) (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W)
  (x a : HeytingLean.Noneism.Var) (φ : HeytingLean.Noneism.Formula σ) (hax : @Ne.{1} HeytingLean.Noneism.Var a x)
  (hx :
    @Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x),
  Iff
    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
        (@HeytingLean.Noneism.Formula.pi σ a φ)))
    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
      (@HeytingLean.Noneism.Formula.pi σ a φ)) :=
fun {σ W : Type} [inst : Preorder.{0} W] {D : Type} (M : @HeytingLean.Noneism.KripkeFO.Model W σ D inst)
    (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W) (x a : HeytingLean.Noneism.Var)
    (φ : HeytingLean.Noneism.Formula σ) (hax : @Ne.{1} HeytingLean.Noneism.Var a x)
    (hx :
      @Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
        (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x) =>
  let avoid : Finset.{0} HeytingLean.Noneism.Var :=
    @Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)));
  let z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
  have hz'NotAvoid :
    Not
      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
        (@Finset.instMembership.{0} HeytingLean.Noneism.Var) avoid z') :=
    @Eq.mpr.{0}
      (Not
        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
          (@Finset.instMembership.{0} HeytingLean.Noneism.Var) avoid z'))
      (And
        (Not
          (@Eq.{1} HeytingLean.Noneism.Var
            (HeytingLean.Noneism.Syntax.freshVar
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
            x))
        (And
          (Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
              (HeytingLean.Noneism.Syntax.freshVar
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
          (Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
              (HeytingLean.Noneism.Syntax.freshVar
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
      (@id.{0}
        (@Eq.{1} Prop
          (Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var) avoid z'))
          (And
            (Not
              (@Eq.{1} HeytingLean.Noneism.Var
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                x))
            (And
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))))))
        (@Eq.trans.{1} Prop
          (Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
              (HeytingLean.Noneism.Syntax.freshVar
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
          (And
            (Not
              (@Eq.{1} HeytingLean.Noneism.Var
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                x))
            (Not
              (Or
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
          (And
            (Not
              (@Eq.{1} HeytingLean.Noneism.Var
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                x))
            (And
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
          (@Eq.trans.{1} Prop
            (Not
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
            (Not
              (Or
                (@Eq.{1} HeytingLean.Noneism.Var
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                  x)
                (Or
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
            (And
              (Not
                (@Eq.{1} HeytingLean.Noneism.Var
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                  x))
              (Not
                (Or
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
            (@congrArg.{1, 1} Prop Prop
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
              (Or
                (@Eq.{1} HeytingLean.Noneism.Var
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                  x)
                (Or
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))))
              Not
              (@Eq.trans.{1} Prop
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                (Or
                  (@Eq.{1} HeytingLean.Noneism.Var
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                    x)
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
                (Or
                  (@Eq.{1} HeytingLean.Noneism.Var
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                    x)
                  (Or
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.freshVar
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                      (HeytingLean.Noneism.Syntax.freshVar
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))))
                (@Finset.mem_insert._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                  x)
                (@congrArg.{1, 1} Prop Prop
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                  (Or
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.freshVar
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                      (HeytingLean.Noneism.Syntax.freshVar
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
                  (Or
                    (@Eq.{1} HeytingLean.Noneism.Var
                      (HeytingLean.Noneism.Syntax.freshVar
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                      x))
                  (@Finset.mem_union._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
            (@not_or._simp_1
              (@Eq.{1} HeytingLean.Noneism.Var
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                x)
              (Or
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
          (@congrArg.{1, 1} Prop Prop
            (Not
              (Or
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))))
            (And
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))))
            (And
              (Not
                (@Eq.{1} HeytingLean.Noneism.Var
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                  x)))
            (@not_or._simp_1
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))))))
      (@Eq.mp.{0}
        (Not
          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
            (@Finset.instMembership.{0} HeytingLean.Noneism.Var) avoid (HeytingLean.Noneism.Syntax.freshVar avoid)))
        (And
          (Not
            (@Eq.{1} HeytingLean.Noneism.Var
              (HeytingLean.Noneism.Syntax.freshVar
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
              x))
          (And
            (Not
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
            (Not
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
        (@Eq.trans.{1} Prop
          (Not
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
              (HeytingLean.Noneism.Syntax.freshVar
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
          (And
            (Not
              (@Eq.{1} HeytingLean.Noneism.Var
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                x))
            (Not
              (Or
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
          (And
            (Not
              (@Eq.{1} HeytingLean.Noneism.Var
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                x))
            (And
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
          (@Eq.trans.{1} Prop
            (Not
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
            (Not
              (Or
                (@Eq.{1} HeytingLean.Noneism.Var
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                  x)
                (Or
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
            (And
              (Not
                (@Eq.{1} HeytingLean.Noneism.Var
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                  x))
              (Not
                (Or
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
            (@congrArg.{1, 1} Prop Prop
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
              (Or
                (@Eq.{1} HeytingLean.Noneism.Var
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                  x)
                (Or
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))))
              Not
              (@Eq.trans.{1} Prop
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                (Or
                  (@Eq.{1} HeytingLean.Noneism.Var
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                    x)
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
                (Or
                  (@Eq.{1} HeytingLean.Noneism.Var
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                    x)
                  (Or
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.freshVar
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                      (HeytingLean.Noneism.Syntax.freshVar
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))))
                (@Finset.mem_insert._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                  x)
                (@congrArg.{1, 1} Prop Prop
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                  (Or
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.freshVar
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                      (HeytingLean.Noneism.Syntax.freshVar
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
                  (Or
                    (@Eq.{1} HeytingLean.Noneism.Var
                      (HeytingLean.Noneism.Syntax.freshVar
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                      x))
                  (@Finset.mem_union._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
            (@not_or._simp_1
              (@Eq.{1} HeytingLean.Noneism.Var
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                x)
              (Or
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
          (@congrArg.{1, 1} Prop Prop
            (Not
              (Or
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))))
            (And
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))))
            (And
              (Not
                (@Eq.{1} HeytingLean.Noneism.Var
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                  x)))
            (@not_or._simp_1
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))))))
        (HeytingLean.Noneism.Syntax.freshVar_not_mem avoid));
  have hz'NotVars :
    Not
      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
        (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) z') :=
    fun
      (hzv :
        @Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
          (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) z') =>
    hz'NotAvoid
      (@of_eq_true
        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
          (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
            (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
            (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
              (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
          z')
        (@Eq.trans.{1} Prop
          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
            (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
              (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
            z')
          (Or (@Eq.{1} HeytingLean.Noneism.Var z' x)
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
              z'))
          True
          (@Finset.mem_insert._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
            (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
              (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
            z' x)
          (@Eq.trans.{1} Prop
            (Or (@Eq.{1} HeytingLean.Noneism.Var z' x)
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                z'))
            (Or (@Eq.{1} HeytingLean.Noneism.Var z' x) True) True
            (@congrArg.{1, 1} Prop Prop
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                z')
              True (Or (@Eq.{1} HeytingLean.Noneism.Var z' x))
              (@Eq.trans.{1} Prop
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                  z')
                (Or
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    z')
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z'))
                True
                (@Finset.mem_union._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z')
                (@Eq.trans.{1} Prop
                  (Or
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      z')
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z'))
                  (Or True
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z'))
                  True
                  (@congrArg.{1, 1} Prop Prop
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      z')
                    True
                    (fun (x : Prop) =>
                      Or x
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z'))
                    (@eq_true
                      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ) z')
                      hzv))
                  (true_or
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z')))))
            (or_true (@Eq.{1} HeytingLean.Noneism.Var z' x)))));
  have hz'neX : @Ne.{1} HeytingLean.Noneism.Var z' x := fun (hzx' : @Eq.{1} HeytingLean.Noneism.Var z' x) =>
    hz'NotAvoid
      (@of_eq_true
        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
          (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
            (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
            (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
              (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
          z')
        (@Eq.trans.{1} Prop
          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
            (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
              (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
            z')
          (Or (@Eq.{1} HeytingLean.Noneism.Var x x)
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
              x))
          True
          (@Eq.trans.{1} Prop
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
              z')
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
              x)
            (Or (@Eq.{1} HeytingLean.Noneism.Var x x)
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                x))
            (@congrArg.{1, 1} HeytingLean.Noneism.Var Prop z' x
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
              hzx')
            (@Finset.mem_insert._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
              (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
              x x))
          (@Eq.trans.{1} Prop
            (Or (@Eq.{1} HeytingLean.Noneism.Var x x)
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                x))
            (Or True
              (Or
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) x)
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) x)))
            True
            (@congr.{1, 1} Prop Prop (Or (@Eq.{1} HeytingLean.Noneism.Var x x)) (Or True)
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                x)
              (Or
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) x)
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) x))
              (@congrArg.{1, 1} Prop ((b : Prop) → Prop) (@Eq.{1} HeytingLean.Noneism.Var x x) True Or
                (@eq_self.{1} HeytingLean.Noneism.Var x))
              (@Finset.mem_union._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) x))
            (true_or
              (Or
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ) x)
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) x))))));
  have hz'neA : @Ne.{1} HeytingLean.Noneism.Var z' a := fun (hza' : @Eq.{1} HeytingLean.Noneism.Var z' a) =>
    hz'NotAvoid
      (@of_eq_true
        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
          (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
            (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
            (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
              (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
              (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)))
          z')
        (@Eq.trans.{1} Prop
          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
            (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
              (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)))
            z')
          (Or (@Eq.{1} HeytingLean.Noneism.Var a x)
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) a
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
              a))
          True
          (@Eq.trans.{1} Prop
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)))
              z')
            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) a
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)))
              a)
            (Or (@Eq.{1} HeytingLean.Noneism.Var a x)
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) a
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
                a))
            (@congr.{1, 1} HeytingLean.Noneism.Var Prop
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a))))
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) a
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ))))
              z' a
              (@congrArg.{1, 1} (Finset.{0} HeytingLean.Noneism.Var) (HeytingLean.Noneism.Var → Prop)
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a))
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) a
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
                (fun (x_1 : Finset.{0} HeytingLean.Noneism.Var) =>
                  @Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x x_1))
                (@Finset.union_singleton.{0} HeytingLean.Noneism.Var instDecidableEqNat a
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)))
              hza')
            (@Finset.mem_insert._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) a
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
              a x))
          (@Eq.trans.{1} Prop
            (Or (@Eq.{1} HeytingLean.Noneism.Var a x)
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) a
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
                a))
            (Or (@Eq.{1} HeytingLean.Noneism.Var a x) True) True
            (@congrArg.{1, 1} Prop Prop
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) a
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
                a)
              True (Or (@Eq.{1} HeytingLean.Noneism.Var a x))
              (@Eq.trans.{1} Prop
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) a
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ))
                  a)
                (Or (@Eq.{1} HeytingLean.Noneism.Var a a)
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    a))
                True
                (@Finset.mem_insert._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ) a a)
                (@Eq.trans.{1} Prop
                  (Or (@Eq.{1} HeytingLean.Noneism.Var a a)
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      a))
                  (Or True
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      a))
                  True
                  (@congrArg.{1, 1} Prop Prop (@Eq.{1} HeytingLean.Noneism.Var a a) True
                    (fun (x : Prop) =>
                      Or x
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ) a))
                    (@eq_self.{1} HeytingLean.Noneism.Var a))
                  (true_or
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      a)))))
            (or_true (@Eq.{1} HeytingLean.Noneism.Var a x)))));
  have haNeZ' : @Ne.{1} HeytingLean.Noneism.Var a z' := @Ne.symm.{1} HeytingLean.Noneism.Var z' a hz'neA;
  have hBoundRen :
    Not
      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
        (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
        (@HeytingLean.Noneism.Syntax.boundVars σ (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)) a) :=
    _root_.HeytingLean.Noneism.Syntax.not_mem_boundVars_renameFormula_target σ a z' hz'neA φ;
  have hguard :
    And
      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
        (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
        (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x) :=
    @And.intro
      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
        (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
        (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x)
      (@of_eq_true
        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
          (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
            (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)
          a)
        (@Eq.trans.{1} Prop
          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
            (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)
            a)
          (@Eq.{1} HeytingLean.Noneism.Var a a) True (@Finset.mem_singleton._simp_1.{0} HeytingLean.Noneism.Var a a)
          (@eq_self.{1} HeytingLean.Noneism.Var a)))
      hx;
  have hSubstPi :
    @Eq.{1} (HeytingLean.Noneism.Formula σ)
      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
        (@HeytingLean.Noneism.Formula.pi σ a φ))
      (@HeytingLean.Noneism.Formula.pi σ z'
        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
          (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))) :=
    @of_eq_true
      (@Eq.{1} (HeytingLean.Noneism.Formula σ)
        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
          (@HeytingLean.Noneism.Formula.pi σ a φ))
        (@HeytingLean.Noneism.Formula.pi σ
          (HeytingLean.Noneism.Syntax.freshVar
            (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
              (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
              (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
            (@HeytingLean.Noneism.Syntax.renameFormula σ a
              (HeytingLean.Noneism.Syntax.freshVar
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
              φ))))
      (@Eq.trans.{1} Prop
        (@Eq.{1} (HeytingLean.Noneism.Formula σ)
          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
            (@HeytingLean.Noneism.Formula.pi σ a φ))
          (@HeytingLean.Noneism.Formula.pi σ
            (HeytingLean.Noneism.Syntax.freshVar
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Syntax.renameFormula σ a
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                φ))))
        (@Eq.{1} (HeytingLean.Noneism.Formula σ)
          (@HeytingLean.Noneism.Formula.pi σ
            (HeytingLean.Noneism.Syntax.freshVar
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Syntax.renameFormula σ a
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                φ)))
          (@HeytingLean.Noneism.Formula.pi σ
            (HeytingLean.Noneism.Syntax.freshVar
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Syntax.renameFormula σ a
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                φ))))
        True
        (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) Prop
          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
            (@HeytingLean.Noneism.Formula.pi σ a φ))
          (@HeytingLean.Noneism.Formula.pi σ
            (HeytingLean.Noneism.Syntax.freshVar
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Syntax.renameFormula σ a
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                φ)))
          (fun (x_1 : HeytingLean.Noneism.Formula σ) =>
            @Eq.{1} (HeytingLean.Noneism.Formula σ) x_1
              (@HeytingLean.Noneism.Formula.pi σ
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                  (@HeytingLean.Noneism.Syntax.renameFormula σ a
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                    φ))))
          (@Eq.trans.{1} (HeytingLean.Noneism.Formula σ)
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Formula.pi σ a φ))
            (@ite.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var a x) (instDecidableEqNat a x)
              (@HeytingLean.Noneism.Formula.pi σ a φ)
              (@ite.{1} (HeytingLean.Noneism.Formula σ)
                (And
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))
                (@instDecidableAnd
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x)
                  (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat a
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                  (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat x
                    (@HeytingLean.Noneism.Syntax.fvFormula σ φ)))
                (have avoid : Finset.{0} HeytingLean.Noneism.Var :=
                  @Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a));
                have z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
                @HeytingLean.Noneism.Formula.pi σ z'
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                    (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))
                (@HeytingLean.Noneism.Formula.pi σ a
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))))
            (@HeytingLean.Noneism.Formula.pi σ
              (HeytingLean.Noneism.Syntax.freshVar
                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                (@HeytingLean.Noneism.Syntax.renameFormula σ a
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                  φ)))
            (@HeytingLean.Noneism.Syntax.substFormula.eq_10 σ x (HeytingLean.Noneism.Term.var a) a φ)
            (@Eq.trans.{1} (HeytingLean.Noneism.Formula σ)
              (@ite.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var a x) (instDecidableEqNat a x)
                (@HeytingLean.Noneism.Formula.pi σ a φ)
                (@ite.{1} (HeytingLean.Noneism.Formula σ)
                  (And
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ)
                      x))
                  (@instDecidableAnd
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ)
                      x)
                    (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat a
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                    (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat x
                      (@HeytingLean.Noneism.Syntax.fvFormula σ φ)))
                  (have avoid : Finset.{0} HeytingLean.Noneism.Var :=
                    @Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a));
                  have z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
                  @HeytingLean.Noneism.Formula.pi σ z'
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                      (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))
                  (@HeytingLean.Noneism.Formula.pi σ a
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))))
              (@ite.{1} (HeytingLean.Noneism.Formula σ)
                (And
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))
                (@instDecidableAnd
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x)
                  (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat a
                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                  (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat x
                    (@HeytingLean.Noneism.Syntax.fvFormula σ φ)))
                (have avoid : Finset.{0} HeytingLean.Noneism.Var :=
                  @Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a));
                have z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
                @HeytingLean.Noneism.Formula.pi σ z'
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                    (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))
                (@HeytingLean.Noneism.Formula.pi σ a
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))
              (@HeytingLean.Noneism.Formula.pi σ
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                  (@HeytingLean.Noneism.Syntax.renameFormula σ a
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                    φ)))
              (@ite_cond_eq_false.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var a x)
                (instDecidableEqNat a x) (@HeytingLean.Noneism.Formula.pi σ a φ)
                (@ite.{1} (HeytingLean.Noneism.Formula σ)
                  (And
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ)
                      x))
                  (@instDecidableAnd
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ)
                      x)
                    (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat a
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                    (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat x
                      (@HeytingLean.Noneism.Syntax.fvFormula σ φ)))
                  (have avoid : Finset.{0} HeytingLean.Noneism.Var :=
                    @Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a));
                  have z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
                  @HeytingLean.Noneism.Formula.pi σ z'
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                      (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))
                  (@HeytingLean.Noneism.Formula.pi σ a
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))
                (@eq_false (@Eq.{1} HeytingLean.Noneism.Var a x) hax))
              (@Eq.trans.{1} (HeytingLean.Noneism.Formula σ)
                (@ite.{1} (HeytingLean.Noneism.Formula σ)
                  (And
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ)
                      x))
                  (@instDecidableAnd
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ)
                      x)
                    (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat a
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                    (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat x
                      (@HeytingLean.Noneism.Syntax.fvFormula σ φ)))
                  (have avoid : Finset.{0} HeytingLean.Noneism.Var :=
                    @Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a));
                  have z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
                  @HeytingLean.Noneism.Formula.pi σ z'
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                      (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))
                  (@HeytingLean.Noneism.Formula.pi σ a
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))
                (have avoid : Finset.{0} HeytingLean.Noneism.Var :=
                  @Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a));
                have z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
                @HeytingLean.Noneism.Formula.pi σ z'
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                    (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))
                (@HeytingLean.Noneism.Formula.pi σ
                  (HeytingLean.Noneism.Syntax.freshVar
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                    (@HeytingLean.Noneism.Syntax.renameFormula σ a
                      (HeytingLean.Noneism.Syntax.freshVar
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                      φ)))
                (@ite_cond_eq_true.{1} (HeytingLean.Noneism.Formula σ)
                  (And
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ)
                      x))
                  (@instDecidableAnd
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ)
                      x)
                    (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat a
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                    (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat x
                      (@HeytingLean.Noneism.Syntax.fvFormula σ φ)))
                  (have avoid : Finset.{0} HeytingLean.Noneism.Var :=
                    @Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a));
                  have z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
                  @HeytingLean.Noneism.Formula.pi σ z'
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                      (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))
                  (@HeytingLean.Noneism.Formula.pi σ a
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                  (@Eq.trans.{1} Prop
                    (And
                      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ)
                        x))
                    (And True True) True
                    (@congr.{1, 1} Prop Prop
                      (And
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a))
                      (And True)
                      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ)
                        x)
                      True
                      (@congrArg.{1, 1} Prop ((b : Prop) → Prop)
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                        True And
                        (@eq_true
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                          hguard.1))
                      (@eq_true
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x)
                        hguard.2))
                    (and_self True)))
                (@congr.{1, 1} (HeytingLean.Noneism.Formula σ) (HeytingLean.Noneism.Formula σ)
                  (@HeytingLean.Noneism.Formula.pi σ
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)))))
                  (@HeytingLean.Noneism.Formula.pi σ
                    (HeytingLean.Noneism.Syntax.freshVar
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))))
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                    (@HeytingLean.Noneism.Syntax.renameFormula σ a
                      (HeytingLean.Noneism.Syntax.freshVar
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                          (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                            (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a))))
                      φ))
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                    (@HeytingLean.Noneism.Syntax.renameFormula σ a
                      (HeytingLean.Noneism.Syntax.freshVar
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                      φ))
                  (@congrArg.{1, 1} (Finset.{0} HeytingLean.Noneism.Var)
                    ((φ : HeytingLean.Noneism.Formula σ) → HeytingLean.Noneism.Formula σ)
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)))
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
                    (fun (x : Finset.{0} HeytingLean.Noneism.Var) =>
                      @HeytingLean.Noneism.Formula.pi σ (HeytingLean.Noneism.Syntax.freshVar x))
                    (@Eq.trans.{1} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)))
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                          (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)))
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
                      (@Finset.union_insert.{0} HeytingLean.Noneism.Var instDecidableEqNat x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                        (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a))
                      (@congrArg.{1, 1} (Finset.{0} HeytingLean.Noneism.Var) (Finset.{0} HeytingLean.Noneism.Var)
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                          (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a))
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x)
                        (@Eq.trans.{1} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                              (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                            (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a))
                          (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) a
                            (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                              (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                          (@Finset.union_singleton.{0} HeytingLean.Noneism.Var instDecidableEqNat a
                            (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                              (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
                          (@Finset.insert_eq_of_mem.{0} HeytingLean.Noneism.Var instDecidableEqNat
                            (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                              (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                            a
                            (@of_eq_true
                              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                                a)
                              (@Eq.trans.{1} Prop
                                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                                  a)
                                (Or
                                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ) a)
                                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a))
                                True
                                (@Finset.mem_union._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
                                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                                (@Eq.trans.{1} Prop
                                  (Or
                                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ) a)
                                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a))
                                  (Or
                                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ) a)
                                    True)
                                  True
                                  (@congrArg.{1, 1} Prop Prop
                                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                                    True
                                    (Or
                                      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var
                                        (Finset.{0} HeytingLean.Noneism.Var)
                                        (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ) a))
                                    (@eq_true
                                      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var
                                        (Finset.{0} HeytingLean.Noneism.Var)
                                        (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                                      hguard.1))
                                  (or_true
                                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ) a))))))))))
                  (@congrArg.{1, 1} (Finset.{0} HeytingLean.Noneism.Var) (HeytingLean.Noneism.Formula σ)
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)))
                    (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
                    (fun (x_1 : Finset.{0} HeytingLean.Noneism.Var) =>
                      @HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                        (@HeytingLean.Noneism.Syntax.renameFormula σ a (HeytingLean.Noneism.Syntax.freshVar x_1) φ))
                    (@Eq.trans.{1} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                          (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)))
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                          (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)))
                      (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
                      (@Finset.union_insert.{0} HeytingLean.Noneism.Var instDecidableEqNat x
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                        (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a))
                      (@congrArg.{1, 1} (Finset.{0} HeytingLean.Noneism.Var) (Finset.{0} HeytingLean.Noneism.Var)
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                          (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a))
                        (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                        (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x)
                        (@Eq.trans.{1} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                              (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                            (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a))
                          (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) a
                            (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                              (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                          (@Finset.union_singleton.{0} HeytingLean.Noneism.Var instDecidableEqNat a
                            (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                              (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a))))
                          (@Finset.insert_eq_of_mem.{0} HeytingLean.Noneism.Var instDecidableEqNat
                            (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                              (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                            a
                            (@of_eq_true
                              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                                a)
                              (@Eq.trans.{1} Prop
                                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                  (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                                    (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                                  a)
                                (Or
                                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                    (@HeytingLean.Noneism.Syntax.varsFormula σ φ) a)
                                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                    (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a))
                                True
                                (@Finset.mem_union._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat
                                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                                (@Eq.trans.{1} Prop
                                  (Or
                                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ) a)
                                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a))
                                  (Or
                                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ) a)
                                    True)
                                  True
                                  (@congrArg.{1, 1} Prop Prop
                                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                                    True
                                    (Or
                                      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var
                                        (Finset.{0} HeytingLean.Noneism.Var)
                                        (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                        (@HeytingLean.Noneism.Syntax.varsFormula σ φ) a))
                                    (@eq_true
                                      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var
                                        (Finset.{0} HeytingLean.Noneism.Var)
                                        (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                        (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) a)
                                      hguard.1))
                                  (or_true
                                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ) a)))))))))))))))
        (@eq_self.{1} (HeytingLean.Noneism.Formula σ)
          (@HeytingLean.Noneism.Formula.pi σ
            (HeytingLean.Noneism.Syntax.freshVar
              (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Syntax.renameFormula σ a
                (HeytingLean.Noneism.Syntax.freshVar
                  (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                    (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                      (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                      (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))))
                φ)))));
  @Iff.intro
    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
        (@HeytingLean.Noneism.Formula.pi σ a φ)))
    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
      (@HeytingLean.Noneism.Formula.pi σ a φ))
    (fun
        (hSub :
          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Formula.pi σ a φ))) =>
      have hSub' :
        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
          (@HeytingLean.Noneism.Formula.pi σ z'
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))) :=
        @Eq.mp.{0}
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Formula.pi σ a φ)))
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
            (@HeytingLean.Noneism.Formula.pi σ z'
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))))
          (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) Prop
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Formula.pi σ a φ))
            (@HeytingLean.Noneism.Formula.pi σ z'
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w) hSubstPi)
          hSub;
      fun (v : W) (hwv : @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v) (d : D) =>
      have hd :
        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) v
          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
            (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)) :=
        hSub' v hwv d;
      have hRenSub :
        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x
            (@HeytingLean.Noneism.KripkeFO.update D ρ z' d a))
          v (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ) :=
        @Iff.mp
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) v
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x
              (@HeytingLean.Noneism.KripkeFO.update D ρ z' d a))
            v (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
          (@HeytingLean.Noneism.KripkeFO.forces_substFormula_var_of_not_mem_boundVars σ W inst D M
            (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) v x a (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)
            hBoundRen)
          hd;
      have hAVal : @Eq.{1} D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d a) (ρ a) :=
        @of_eq_true
          (@Eq.{1} D (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z') (instDecidableEqNat a z') d (ρ a)) (ρ a))
          (@Eq.trans.{1} Prop
            (@Eq.{1} D (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z') (instDecidableEqNat a z') d (ρ a)) (ρ a))
            (@Eq.{1} D (ρ a) (ρ a)) True
            (@congrArg.{1, 1} D Prop
              (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z') (instDecidableEqNat a z') d (ρ a)) (ρ a)
              (fun (x : D) => @Eq.{1} D x (ρ a))
              (@ite_cond_eq_false.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z') (instDecidableEqNat a z') d (ρ a)
                (@eq_false (@Eq.{1} HeytingLean.Noneism.Var a z') haNeZ')))
            (@eq_self.{1} D (ρ a)));
      have hRen :
        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x (ρ a)) v
          (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ) :=
        @Eq.mp.{0}
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x
              (@HeytingLean.Noneism.KripkeFO.update D ρ z' d a))
            v (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x (ρ a)) v
            (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
          (@congrArg.{1, 1} D Prop (@HeytingLean.Noneism.KripkeFO.update D ρ z' d a) (ρ a)
            (fun (x_1 : D) =>
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x x_1) v
                (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
            hAVal)
          hRenSub;
      have hComm :
        @Eq.{1} (HeytingLean.Noneism.KripkeFO.Valuation D)
          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x (ρ a))
          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) :=
        @HeytingLean.Noneism.KripkeFO.update_comm D ρ z' x d (ρ a) hz'neX;
      have hRen' :
        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) v
          (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ) :=
        @Eq.mp.{0}
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x (ρ a)) v
            (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) v
            (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
          (@congrArg.{1, 1} (HeytingLean.Noneism.KripkeFO.Valuation D) Prop
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x (ρ a))
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d)
            (fun (x : HeytingLean.Noneism.KripkeFO.Valuation D) =>
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M x v
                (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
            hComm)
          hRen;
      have hOrigWithFresh :
        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
          (@HeytingLean.Noneism.KripkeFO.update D
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d z'))
          v φ :=
        @Iff.mp
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) v
            (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d z'))
            v φ)
          (@HeytingLean.Noneism.KripkeFO.forces_renameFormula_of_not_mem_varsFormula σ W inst D M
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a z' φ
            hz'NotVars v)
          hRen';
      have hz'Val :
        @Eq.{1} D (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d z')
          d :=
        @of_eq_true
          (@Eq.{1} D
            (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z' z') (instDecidableEqNat z' z') d
              (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a) z'))
            d)
          (@Eq.trans.{1} Prop
            (@Eq.{1} D
              (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z' z') (instDecidableEqNat z' z') d
                (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a) z'))
              d)
            (@Eq.{1} D d d) True
            (@congrArg.{1, 1} D Prop
              (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z' z') (instDecidableEqNat z' z') d
                (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a) z'))
              d (fun (x : D) => @Eq.{1} D x d)
              (@ite_cond_eq_true.{1} D (@Eq.{1} HeytingLean.Noneism.Var z' z') (instDecidableEqNat z' z') d
                (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a) z') (@eq_self.{1} HeytingLean.Noneism.Var z')))
            (@eq_self.{1} D d));
      have hOrigFresh :
        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
          (@HeytingLean.Noneism.KripkeFO.update D
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a d)
          v φ :=
        @Eq.mp.{0}
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d z'))
            v φ)
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a d)
            v φ)
          (@congrArg.{1, 1} D Prop
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d z') d
            (fun (x_1 : D) =>
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a
                  x_1)
                v φ)
            (@HeytingLean.Noneism.KripkeFO.update_self D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d))
          hOrigWithFresh;
      have hSwap :
        @Eq.{1} (HeytingLean.Noneism.KripkeFO.Valuation D)
          (@HeytingLean.Noneism.KripkeFO.update D
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a d)
          (@HeytingLean.Noneism.KripkeFO.update D
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) z' d) :=
        @HeytingLean.Noneism.KripkeFO.update_comm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' a d d hz'neA;
      have hWithFresh :
        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
          (@HeytingLean.Noneism.KripkeFO.update D
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) z' d)
          v φ :=
        @Eq.mp.{0}
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a d)
            v φ)
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) z' d)
            v φ)
          (@congrArg.{1, 1} (HeytingLean.Noneism.KripkeFO.Valuation D) Prop
            (@HeytingLean.Noneism.KripkeFO.update D
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a d)
            (@HeytingLean.Noneism.KripkeFO.update D
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) z' d)
            (fun (x : HeytingLean.Noneism.KripkeFO.Valuation D) =>
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M x v φ)
            hSwap)
          hOrigFresh;
      @Iff.mp
        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
          (@HeytingLean.Noneism.KripkeFO.update D
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) z' d)
          v φ)
        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) v φ)
        (@HeytingLean.Noneism.KripkeFO.forces_update_of_not_mem_varsFormula σ W inst D M
          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) z' d v φ
          hz'NotVars)
        hWithFresh)
    fun
      (hPi :
        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
          (@HeytingLean.Noneism.Formula.pi σ a φ)) =>
    have hSub' :
      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
        (@HeytingLean.Noneism.Formula.pi σ z'
          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
            (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))) :=
      fun (v : W) (hwv : @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v) (d : D) =>
      have hBody :
        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) v φ :=
        hPi v hwv d;
      have hWithFresh :
        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
          (@HeytingLean.Noneism.KripkeFO.update D
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) z' d)
          v φ :=
        @Iff.mpr
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) z' d)
            v φ)
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) v φ)
          (@HeytingLean.Noneism.KripkeFO.forces_update_of_not_mem_varsFormula σ W inst D M
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) z' d v φ
            hz'NotVars)
          hBody;
      have hSwap :
        @Eq.{1} (HeytingLean.Noneism.KripkeFO.Valuation D)
          (@HeytingLean.Noneism.KripkeFO.update D
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a d)
          (@HeytingLean.Noneism.KripkeFO.update D
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) z' d) :=
        @HeytingLean.Noneism.KripkeFO.update_comm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' a d d hz'neA;
      have hOrigFresh :
        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
          (@HeytingLean.Noneism.KripkeFO.update D
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a d)
          v φ :=
        @Eq.mpr.{0}
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a d)
            v φ)
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) z' d)
            v φ)
          (@id.{0}
            (@Eq.{1} Prop
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a d)
                v φ)
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) z' d)
                v φ))
            (@congrArg.{1, 1} (HeytingLean.Noneism.KripkeFO.Valuation D) Prop
              (@HeytingLean.Noneism.KripkeFO.update D
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a d)
              (@HeytingLean.Noneism.KripkeFO.update D
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a d) z' d)
              (fun (x : HeytingLean.Noneism.KripkeFO.Valuation D) =>
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M x v φ)
              hSwap))
          hWithFresh;
      have hz'Val :
        @Eq.{1} D (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d z')
          d :=
        @of_eq_true
          (@Eq.{1} D
            (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z' z') (instDecidableEqNat z' z') d
              (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a) z'))
            d)
          (@Eq.trans.{1} Prop
            (@Eq.{1} D
              (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z' z') (instDecidableEqNat z' z') d
                (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a) z'))
              d)
            (@Eq.{1} D d d) True
            (@congrArg.{1, 1} D Prop
              (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z' z') (instDecidableEqNat z' z') d
                (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a) z'))
              d (fun (x : D) => @Eq.{1} D x d)
              (@ite_cond_eq_true.{1} D (@Eq.{1} HeytingLean.Noneism.Var z' z') (instDecidableEqNat z' z') d
                (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a) z') (@eq_self.{1} HeytingLean.Noneism.Var z')))
            (@eq_self.{1} D d));
      have hOrigWithFresh :
        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
          (@HeytingLean.Noneism.KripkeFO.update D
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d z'))
          v φ :=
        @Eq.mpr.{0}
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d z'))
            v φ)
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a d)
            v φ)
          (@id.{0}
            (@Eq.{1} Prop
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d z'))
                v φ)
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a d)
                v φ))
            (@congrArg.{1, 1} D Prop
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d z') d
              (fun (x_1 : D) =>
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a
                    x_1)
                  v φ)
              (@HeytingLean.Noneism.KripkeFO.update_self D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d)))
          hOrigFresh;
      have hRen' :
        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) v
          (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ) :=
        @Iff.mpr
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) v
            (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d z'))
            v φ)
          (@HeytingLean.Noneism.KripkeFO.forces_renameFormula_of_not_mem_varsFormula σ W inst D M
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) a z' φ
            hz'NotVars v)
          hOrigWithFresh;
      have hComm :
        @Eq.{1} (HeytingLean.Noneism.KripkeFO.Valuation D)
          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x (ρ a))
          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) :=
        @HeytingLean.Noneism.KripkeFO.update_comm D ρ z' x d (ρ a) hz'neX;
      have hRen :
        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x (ρ a)) v
          (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ) :=
        @Eq.mpr.{0}
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x (ρ a)) v
            (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) v
            (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
          (@id.{0}
            (@Eq.{1} Prop
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x (ρ a)) v
                (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d) v
                (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))
            (@congrArg.{1, 1} (HeytingLean.Noneism.KripkeFO.Valuation D) Prop
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x (ρ a))
              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z' d)
              (fun (x : HeytingLean.Noneism.KripkeFO.Valuation D) =>
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M x v
                  (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
              hComm))
          hRen';
      have hAVal : @Eq.{1} D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d a) (ρ a) :=
        @of_eq_true
          (@Eq.{1} D (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z') (instDecidableEqNat a z') d (ρ a)) (ρ a))
          (@Eq.trans.{1} Prop
            (@Eq.{1} D (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z') (instDecidableEqNat a z') d (ρ a)) (ρ a))
            (@Eq.{1} D (ρ a) (ρ a)) True
            (@congrArg.{1, 1} D Prop
              (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z') (instDecidableEqNat a z') d (ρ a)) (ρ a)
              (fun (x : D) => @Eq.{1} D x (ρ a))
              (@ite_cond_eq_false.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z') (instDecidableEqNat a z') d (ρ a)
                (@eq_false (@Eq.{1} HeytingLean.Noneism.Var a z') haNeZ')))
            (@eq_self.{1} D (ρ a)));
      have hRenSub :
        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x
            (@HeytingLean.Noneism.KripkeFO.update D ρ z' d a))
          v (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ) :=
        @Eq.mpr.{0}
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x
              (@HeytingLean.Noneism.KripkeFO.update D ρ z' d a))
            v (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x (ρ a)) v
            (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
          (@id.{0}
            (@Eq.{1} Prop
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x
                  (@HeytingLean.Noneism.KripkeFO.update D ρ z' d a))
                v (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x (ρ a)) v
                (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))
            (@congrArg.{1, 1} D Prop (@HeytingLean.Noneism.KripkeFO.update D ρ z' d a) (ρ a)
              (fun (x_1 : D) =>
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x x_1) v
                  (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
              hAVal))
          hRen;
      @Iff.mpr
        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) v
          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
            (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))
        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) x
            (@HeytingLean.Noneism.KripkeFO.update D ρ z' d a))
          v (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))
        (@HeytingLean.Noneism.KripkeFO.forces_substFormula_var_of_not_mem_boundVars σ W inst D M
          (@HeytingLean.Noneism.KripkeFO.update D ρ z' d) v x a (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)
          hBoundRen)
        hRenSub;
    @Eq.mpr.{0}
      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
          (@HeytingLean.Noneism.Formula.pi σ a φ)))
      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
        (@HeytingLean.Noneism.Formula.pi σ z'
          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
            (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ))))
      (@id.{0}
        (@Eq.{1} Prop
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Formula.pi σ a φ)))
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
            (@HeytingLean.Noneism.Formula.pi σ z'
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))))
        (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) Prop
          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
            (@HeytingLean.Noneism.Formula.pi σ a φ))
          (@HeytingLean.Noneism.Formula.pi σ z'
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Syntax.renameFormula σ a z' φ)))
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w) hSubstPi))
      hSub'
theorem _root_.HeytingLean.Noneism.KripkeFO.forces_substFormula_var : ∀ {σ W : Type} [inst : Preorder.{0} W] {D : Type}
  (M : @HeytingLean.Noneism.KripkeFO.Model W σ D inst) (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W)
  (x a : HeytingLean.Noneism.Var) (φ : HeytingLean.Noneism.Formula σ),
  Iff
    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w φ) :=
fun {σ W : Type} [inst : Preorder.{0} W] {D : Type} (M : @HeytingLean.Noneism.KripkeFO.Model W σ D inst)
    (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W) (x a : HeytingLean.Noneism.Var)
    (φ : HeytingLean.Noneism.Formula σ) =>
  @HeytingLean.Noneism.Formula.rec.{0} σ
    (fun (φ : HeytingLean.Noneism.Formula σ) =>
      ∀ (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W),
        Iff
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w φ))
    (fun (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W) =>
      @of_eq_true
        (Iff
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Formula.top σ)))
          True)
        (@Eq.trans.{1} Prop
          (Iff
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                (@HeytingLean.Noneism.Formula.top σ)))
            True)
          (Iff (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w (@HeytingLean.Noneism.Formula.top σ)) True) True
          (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) Prop
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Formula.top σ))
            (@HeytingLean.Noneism.Formula.top σ)
            (fun (x : HeytingLean.Noneism.Formula σ) =>
              Iff (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w x) True)
            (@HeytingLean.Noneism.Syntax.substFormula.eq_1 σ x (HeytingLean.Noneism.Term.var a)))
          (iff_self True)))
    (fun (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W) =>
      @of_eq_true
        (Iff
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Formula.bot σ)))
          False)
        (@Eq.trans.{1} Prop
          (Iff
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                (@HeytingLean.Noneism.Formula.bot σ)))
            False)
          (Iff (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w (@HeytingLean.Noneism.Formula.bot σ)) False) True
          (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) Prop
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Formula.bot σ))
            (@HeytingLean.Noneism.Formula.bot σ)
            (fun (x : HeytingLean.Noneism.Formula σ) =>
              Iff (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w x) False)
            (@HeytingLean.Noneism.Syntax.substFormula.eq_2 σ x (HeytingLean.Noneism.Term.var a)))
          (iff_self False)))
    (fun (p : σ) (args : List.{0} HeytingLean.Noneism.Term) (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W) =>
      have hEq :
        @Eq.{1} (List.{0} D)
          (@List.map.{0, 0} HeytingLean.Noneism.Term D
            (@Function.comp.{1, 1, 1} HeytingLean.Noneism.Term HeytingLean.Noneism.Term D
              (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ)
              (HeytingLean.Noneism.Syntax.substTerm x (HeytingLean.Noneism.Term.var a)))
            args)
          (@List.map.{0, 0} HeytingLean.Noneism.Term D
            (@HeytingLean.Noneism.KripkeFO.evalTerm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))) args) :=
        @List.map_congr_left.{0, 0} HeytingLean.Noneism.Term args D
          (@Function.comp.{1, 1, 1} HeytingLean.Noneism.Term HeytingLean.Noneism.Term D
            (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ)
            (HeytingLean.Noneism.Syntax.substTerm x (HeytingLean.Noneism.Term.var a)))
          (@HeytingLean.Noneism.KripkeFO.evalTerm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)))
          fun (t : HeytingLean.Noneism.Term)
            (ht :
              @Membership.mem.{0, 0} HeytingLean.Noneism.Term (List.{0} HeytingLean.Noneism.Term)
                (@List.instMembership.{0} HeytingLean.Noneism.Term) args t) =>
          @HeytingLean.Noneism.Term.casesOn.{0}
            (fun (t_1 : HeytingLean.Noneism.Term) =>
              ∀ (h : @Eq.{1} HeytingLean.Noneism.Term t t_1),
                @Eq.{1} D
                  (@Function.comp.{1, 1, 1} HeytingLean.Noneism.Term HeytingLean.Noneism.Term D
                    (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ)
                    (HeytingLean.Noneism.Syntax.substTerm x (HeytingLean.Noneism.Term.var a)) t)
                  (@HeytingLean.Noneism.KripkeFO.evalTerm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) t))
            t
            (fun (z : HeytingLean.Noneism.Var)
                (h : @Eq.{1} HeytingLean.Noneism.Term t (HeytingLean.Noneism.Term.var z)) =>
              @Eq.ndrec.{0, 1} HeytingLean.Noneism.Term (HeytingLean.Noneism.Term.var z)
                (fun (t : HeytingLean.Noneism.Term) =>
                  ∀
                    (ht :
                      @Membership.mem.{0, 0} HeytingLean.Noneism.Term (List.{0} HeytingLean.Noneism.Term)
                        (@List.instMembership.{0} HeytingLean.Noneism.Term) args t),
                    @Eq.{1} D
                      (@Function.comp.{1, 1, 1} HeytingLean.Noneism.Term HeytingLean.Noneism.Term D
                        (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ)
                        (HeytingLean.Noneism.Syntax.substTerm x (HeytingLean.Noneism.Term.var a)) t)
                      (@HeytingLean.Noneism.KripkeFO.evalTerm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) t))
                (fun
                    (ht :
                      @Membership.mem.{0, 0} HeytingLean.Noneism.Term (List.{0} HeytingLean.Noneism.Term)
                        (@List.instMembership.{0} HeytingLean.Noneism.Term) args (HeytingLean.Noneism.Term.var z)) =>
                  @dite.{0}
                    (@Eq.{1} D
                      (@Function.comp.{1, 1, 1} HeytingLean.Noneism.Term HeytingLean.Noneism.Term D
                        (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ)
                        (HeytingLean.Noneism.Syntax.substTerm x (HeytingLean.Noneism.Term.var a))
                        (HeytingLean.Noneism.Term.var z))
                      (@HeytingLean.Noneism.KripkeFO.evalTerm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))
                        (HeytingLean.Noneism.Term.var z)))
                    (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x)
                    (fun (hzx : @Eq.{1} HeytingLean.Noneism.Var z x) =>
                      @of_eq_true
                        (@Eq.{1} D
                          (@Function.comp.{1, 1, 1} HeytingLean.Noneism.Term HeytingLean.Noneism.Term D
                            (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ)
                            (HeytingLean.Noneism.Syntax.substTerm x (HeytingLean.Noneism.Term.var a))
                            (HeytingLean.Noneism.Term.var z))
                          (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ a) (ρ z)))
                        (@Eq.trans.{1} Prop
                          (@Eq.{1} D
                            (@Function.comp.{1, 1, 1} HeytingLean.Noneism.Term HeytingLean.Noneism.Term D
                              (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ)
                              (HeytingLean.Noneism.Syntax.substTerm x (HeytingLean.Noneism.Term.var a))
                              (HeytingLean.Noneism.Term.var z))
                            (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ a) (ρ z)))
                          (@Eq.{1} D (ρ (HeytingLean.Noneism.Term.var a).1) (ρ a)) True
                          (@congr.{1, 1} D Prop
                            (@Eq.{1} D
                              (@Function.comp.{1, 1, 1} HeytingLean.Noneism.Term HeytingLean.Noneism.Term D
                                (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ)
                                (HeytingLean.Noneism.Syntax.substTerm x (HeytingLean.Noneism.Term.var a))
                                (HeytingLean.Noneism.Term.var z)))
                            (@Eq.{1} D (ρ (HeytingLean.Noneism.Term.var a).1))
                            (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ a) (ρ z))
                            (ρ a)
                            (@congrArg.{1, 1} D (D → Prop)
                              (@Function.comp.{1, 1, 1} HeytingLean.Noneism.Term HeytingLean.Noneism.Term D
                                (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ)
                                (HeytingLean.Noneism.Syntax.substTerm x (HeytingLean.Noneism.Term.var a))
                                (HeytingLean.Noneism.Term.var z))
                              (ρ (HeytingLean.Noneism.Term.var a).1) (@Eq.{1} D)
                              (@Eq.trans.{1} D
                                (@Function.comp.{1, 1, 1} HeytingLean.Noneism.Term HeytingLean.Noneism.Term D
                                  (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ)
                                  (HeytingLean.Noneism.Syntax.substTerm x (HeytingLean.Noneism.Term.var a))
                                  (HeytingLean.Noneism.Term.var z))
                                (@Function.comp.{1, 1, 1} HeytingLean.Noneism.Term HeytingLean.Noneism.Term D
                                  (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ)
                                  (HeytingLean.Noneism.Syntax.substTerm x (HeytingLean.Noneism.Term.var a))
                                  (HeytingLean.Noneism.Term.var x))
                                (ρ (HeytingLean.Noneism.Term.var a).1)
                                (@congrArg.{1, 1} HeytingLean.Noneism.Var D z x
                                  (fun (x_1 : HeytingLean.Noneism.Var) =>
                                    @Function.comp.{1, 1, 1} HeytingLean.Noneism.Term HeytingLean.Noneism.Term D
                                      (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ)
                                      (HeytingLean.Noneism.Syntax.substTerm x (HeytingLean.Noneism.Term.var a))
                                      (HeytingLean.Noneism.Term.var x_1))
                                  hzx)
                                (@congrArg.{1, 1} HeytingLean.Noneism.Var D
                                  (HeytingLean.Noneism.Syntax.substTerm x (HeytingLean.Noneism.Term.var a)
                                      (HeytingLean.Noneism.Term.var x)).1
                                  (HeytingLean.Noneism.Term.var a).1 ρ
                                  (@Eq.ndrec.{0, 1} HeytingLean.Noneism.Term
                                    (@ite.{1} HeytingLean.Noneism.Term (@Eq.{1} HeytingLean.Noneism.Var x x)
                                      (instDecidableEqNat x x) (HeytingLean.Noneism.Term.var a)
                                      (HeytingLean.Noneism.Term.var x))
                                    (fun (s : HeytingLean.Noneism.Term) =>
                                      @Eq.{1} HeytingLean.Noneism.Var
                                        (HeytingLean.Noneism.Syntax.substTerm x (HeytingLean.Noneism.Term.var a)
                                            (HeytingLean.Noneism.Term.var x)).1
                                        s.1)
                                    (@Eq.refl.{1} HeytingLean.Noneism.Var
                                      (HeytingLean.Noneism.Syntax.substTerm x (HeytingLean.Noneism.Term.var a)
                                          (HeytingLean.Noneism.Term.var x)).1)
                                    (HeytingLean.Noneism.Term.var a)
                                    (@ite_cond_eq_true.{1} HeytingLean.Noneism.Term
                                      (@Eq.{1} HeytingLean.Noneism.Var x x) (instDecidableEqNat x x)
                                      (HeytingLean.Noneism.Term.var a) (HeytingLean.Noneism.Term.var x)
                                      (@eq_self.{1} HeytingLean.Noneism.Var x))))))
                            (@ite_cond_eq_true.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x)
                              (ρ a) (ρ z)
                              (@Eq.trans.{1} Prop (@Eq.{1} HeytingLean.Noneism.Var z x)
                                (@Eq.{1} HeytingLean.Noneism.Var x x) True
                                (@congrArg.{1, 1} HeytingLean.Noneism.Var Prop z x
                                  (fun (x_1 : HeytingLean.Noneism.Var) => @Eq.{1} HeytingLean.Noneism.Var x_1 x) hzx)
                                (@eq_self.{1} HeytingLean.Noneism.Var x))))
                          (@eq_self.{1} D (ρ a))))
                    fun (hzx : Not (@Eq.{1} HeytingLean.Noneism.Var z x)) =>
                    @of_eq_true
                      (@Eq.{1} D
                        (ρ
                          (HeytingLean.Noneism.Syntax.substTerm x (HeytingLean.Noneism.Term.var a)
                              (HeytingLean.Noneism.Term.var z)).1)
                        (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ a) (ρ z)))
                      (@Eq.trans.{1} Prop
                        (@Eq.{1} D
                          (ρ
                            (HeytingLean.Noneism.Syntax.substTerm x (HeytingLean.Noneism.Term.var a)
                                (HeytingLean.Noneism.Term.var z)).1)
                          (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ a) (ρ z)))
                        (@Eq.{1} D (ρ (HeytingLean.Noneism.Term.var z).1) (ρ z)) True
                        (@congr.{1, 1} D Prop
                          (@Eq.{1} D
                            (ρ
                              (HeytingLean.Noneism.Syntax.substTerm x (HeytingLean.Noneism.Term.var a)
                                  (HeytingLean.Noneism.Term.var z)).1))
                          (@Eq.{1} D (ρ (HeytingLean.Noneism.Term.var z).1))
                          (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ a) (ρ z)) (ρ z)
                          (@congrArg.{1, 1} HeytingLean.Noneism.Var (D → Prop)
                            (HeytingLean.Noneism.Syntax.substTerm x (HeytingLean.Noneism.Term.var a)
                                (HeytingLean.Noneism.Term.var z)).1
                            (HeytingLean.Noneism.Term.var z).1 (fun (x : HeytingLean.Noneism.Var) => @Eq.{1} D (ρ x))
                            (@Eq.ndrec.{0, 1} HeytingLean.Noneism.Term
                              (@ite.{1} HeytingLean.Noneism.Term (@Eq.{1} HeytingLean.Noneism.Var z x)
                                (instDecidableEqNat z x) (HeytingLean.Noneism.Term.var a)
                                (HeytingLean.Noneism.Term.var z))
                              (fun (s : HeytingLean.Noneism.Term) =>
                                @Eq.{1} HeytingLean.Noneism.Var
                                  (HeytingLean.Noneism.Syntax.substTerm x (HeytingLean.Noneism.Term.var a)
                                      (HeytingLean.Noneism.Term.var z)).1
                                  s.1)
                              (@Eq.refl.{1} HeytingLean.Noneism.Var
                                (HeytingLean.Noneism.Syntax.substTerm x (HeytingLean.Noneism.Term.var a)
                                    (HeytingLean.Noneism.Term.var z)).1)
                              (HeytingLean.Noneism.Term.var z)
                              (@ite_cond_eq_false.{1} HeytingLean.Noneism.Term (@Eq.{1} HeytingLean.Noneism.Var z x)
                                (instDecidableEqNat z x) (HeytingLean.Noneism.Term.var a)
                                (HeytingLean.Noneism.Term.var z)
                                (@eq_false (@Eq.{1} HeytingLean.Noneism.Var z x) hzx))))
                          (@ite_cond_eq_false.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ a)
                            (ρ z) (@eq_false (@Eq.{1} HeytingLean.Noneism.Var z x) hzx)))
                        (@eq_self.{1} D (ρ z))))
                t (@Eq.symm.{1} HeytingLean.Noneism.Term t (HeytingLean.Noneism.Term.var z) h) ht)
            (@Eq.refl.{1} HeytingLean.Noneism.Term t);
      @of_eq_true
        (Iff
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Formula.pred σ p args)))
          (@HeytingLean.Noneism.KripkeFO.Model.valPred W σ D inst M w p
            (@List.map.{0, 0} HeytingLean.Noneism.Term D
              (@HeytingLean.Noneism.KripkeFO.evalTerm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))) args)))
        (@Eq.trans.{1} Prop
          (Iff
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                (@HeytingLean.Noneism.Formula.pred σ p args)))
            (@HeytingLean.Noneism.KripkeFO.Model.valPred W σ D inst M w p
              (@List.map.{0, 0} HeytingLean.Noneism.Term D
                (@HeytingLean.Noneism.KripkeFO.evalTerm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))) args)))
          (Iff
            (@HeytingLean.Noneism.KripkeFO.Model.valPred W σ D inst M w p
              (@List.map.{0, 0} HeytingLean.Noneism.Term D
                (@HeytingLean.Noneism.KripkeFO.evalTerm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))) args))
            (@HeytingLean.Noneism.KripkeFO.Model.valPred W σ D inst M w p
              (@List.map.{0, 0} HeytingLean.Noneism.Term D
                (@HeytingLean.Noneism.KripkeFO.evalTerm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))) args)))
          True
          (@congrArg.{1, 1} Prop Prop
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                (@HeytingLean.Noneism.Formula.pred σ p args)))
            (@HeytingLean.Noneism.KripkeFO.Model.valPred W σ D inst M w p
              (@List.map.{0, 0} HeytingLean.Noneism.Term D
                (@HeytingLean.Noneism.KripkeFO.evalTerm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))) args))
            (fun (x_1 : Prop) =>
              Iff x_1
                (@HeytingLean.Noneism.KripkeFO.Model.valPred W σ D inst M w p
                  (@List.map.{0, 0} HeytingLean.Noneism.Term D
                    (@HeytingLean.Noneism.KripkeFO.evalTerm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)))
                    args)))
            (@Eq.trans.{1} Prop
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                  (@HeytingLean.Noneism.Formula.pred σ p args)))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Formula.pred σ p
                  (HeytingLean.Noneism.Syntax.substTerms x (HeytingLean.Noneism.Term.var a) args)))
              (@HeytingLean.Noneism.KripkeFO.Model.valPred W σ D inst M w p
                (@List.map.{0, 0} HeytingLean.Noneism.Term D
                  (@HeytingLean.Noneism.KripkeFO.evalTerm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))) args))
              (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) Prop
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                  (@HeytingLean.Noneism.Formula.pred σ p args))
                (@HeytingLean.Noneism.Formula.pred σ p
                  (HeytingLean.Noneism.Syntax.substTerms x (HeytingLean.Noneism.Term.var a) args))
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w)
                (@HeytingLean.Noneism.Syntax.substFormula.eq_3 σ x (HeytingLean.Noneism.Term.var a) p args))
              (@congrArg.{1, 1} (List.{0} D) Prop
                (@List.map.{0, 0} HeytingLean.Noneism.Term D (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ)
                  (@List.map.{0, 0} HeytingLean.Noneism.Term HeytingLean.Noneism.Term
                    (HeytingLean.Noneism.Syntax.substTerm x (HeytingLean.Noneism.Term.var a)) args))
                (@List.map.{0, 0} HeytingLean.Noneism.Term D
                  (@HeytingLean.Noneism.KripkeFO.evalTerm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))) args)
                (@HeytingLean.Noneism.KripkeFO.Model.valPred W σ D inst M w p)
                (@Eq.trans.{1} (List.{0} D)
                  (@List.map.{0, 0} HeytingLean.Noneism.Term D (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ)
                    (@List.map.{0, 0} HeytingLean.Noneism.Term HeytingLean.Noneism.Term
                      (HeytingLean.Noneism.Syntax.substTerm x (HeytingLean.Noneism.Term.var a)) args))
                  (@List.map.{0, 0} HeytingLean.Noneism.Term D
                    (@Function.comp.{1, 1, 1} HeytingLean.Noneism.Term HeytingLean.Noneism.Term D
                      (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ)
                      (HeytingLean.Noneism.Syntax.substTerm x (HeytingLean.Noneism.Term.var a)))
                    args)
                  (@List.map.{0, 0} HeytingLean.Noneism.Term D
                    (@HeytingLean.Noneism.KripkeFO.evalTerm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))) args)
                  (@List.map_map.{0, 0, 0} HeytingLean.Noneism.Term D HeytingLean.Noneism.Term
                    (@HeytingLean.Noneism.KripkeFO.evalTerm D ρ)
                    (HeytingLean.Noneism.Syntax.substTerm x (HeytingLean.Noneism.Term.var a)) args)
                  hEq))))
          (iff_self
            (@HeytingLean.Noneism.KripkeFO.Model.valPred W σ D inst M w p
              (@List.map.{0, 0} HeytingLean.Noneism.Term D
                (@HeytingLean.Noneism.KripkeFO.evalTerm D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))) args)))))
    (fun (t : HeytingLean.Noneism.Term) (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W) =>
      @HeytingLean.Noneism.Term.casesOn.{0}
        (fun (t_1 : HeytingLean.Noneism.Term) =>
          ∀ (h : @Eq.{1} HeytingLean.Noneism.Term t t_1),
            Iff
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                  (@HeytingLean.Noneism.Formula.eExists σ t)))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                (@HeytingLean.Noneism.Formula.eExists σ t)))
        t
        (fun (z : HeytingLean.Noneism.Var) (h : @Eq.{1} HeytingLean.Noneism.Term t (HeytingLean.Noneism.Term.var z)) =>
          @Eq.ndrec.{0, 1} HeytingLean.Noneism.Term (HeytingLean.Noneism.Term.var z)
            (fun (t : HeytingLean.Noneism.Term) =>
              Iff
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                    (@HeytingLean.Noneism.Formula.eExists σ t)))
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                  (@HeytingLean.Noneism.Formula.eExists σ t)))
            (@dite.{0}
              (Iff
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                    (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var z))))
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                  (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var z))))
              (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x)
              (fun (hzx : @Eq.{1} HeytingLean.Noneism.Var z x) =>
                @of_eq_true
                  (Iff
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                        (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var z))))
                    (@HeytingLean.Noneism.KripkeFO.Model.valEx W σ D inst M w
                      (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ a) (ρ z))))
                  (@Eq.trans.{1} Prop
                    (Iff
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                          (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var z))))
                      (@HeytingLean.Noneism.KripkeFO.Model.valEx W σ D inst M w
                        (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ a) (ρ z))))
                    (Iff
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                        (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var a)))
                      (@HeytingLean.Noneism.KripkeFO.Model.valEx W σ D inst M w (ρ a)))
                    True
                    (@congr.{1, 1} Prop Prop
                      (Iff
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                            (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var z)))))
                      (Iff
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                          (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var a))))
                      (@HeytingLean.Noneism.KripkeFO.Model.valEx W σ D inst M w
                        (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ a) (ρ z)))
                      (@HeytingLean.Noneism.KripkeFO.Model.valEx W σ D inst M w (ρ a))
                      (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) ((b : Prop) → Prop)
                        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                          (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var z)))
                        (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var a))
                        (fun (x : HeytingLean.Noneism.Formula σ) =>
                          Iff (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w x))
                        (@Eq.trans.{1} (HeytingLean.Noneism.Formula σ)
                          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                            (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var z)))
                          (@HeytingLean.Noneism.Formula.eExists σ
                            (HeytingLean.Noneism.Syntax.substTerm x (HeytingLean.Noneism.Term.var a)
                              (HeytingLean.Noneism.Term.var x)))
                          (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var a))
                          (@Eq.trans.{1} (HeytingLean.Noneism.Formula σ)
                            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                              (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var z)))
                            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                              (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var x)))
                            (@HeytingLean.Noneism.Formula.eExists σ
                              (HeytingLean.Noneism.Syntax.substTerm x (HeytingLean.Noneism.Term.var a)
                                (HeytingLean.Noneism.Term.var x)))
                            (@congrArg.{1, 1} HeytingLean.Noneism.Var (HeytingLean.Noneism.Formula σ) z x
                              (fun (x_1 : HeytingLean.Noneism.Var) =>
                                @HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                                  (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var x_1)))
                              hzx)
                            (@HeytingLean.Noneism.Syntax.substFormula.eq_4 σ x (HeytingLean.Noneism.Term.var a)
                              (HeytingLean.Noneism.Term.var x)))
                          (@congrArg.{1, 1} HeytingLean.Noneism.Term (HeytingLean.Noneism.Formula σ)
                            (@ite.{1} HeytingLean.Noneism.Term (@Eq.{1} HeytingLean.Noneism.Var x x)
                              (instDecidableEqNat x x) (HeytingLean.Noneism.Term.var a)
                              (HeytingLean.Noneism.Term.var x))
                            (HeytingLean.Noneism.Term.var a) (@HeytingLean.Noneism.Formula.eExists σ)
                            (@ite_cond_eq_true.{1} HeytingLean.Noneism.Term (@Eq.{1} HeytingLean.Noneism.Var x x)
                              (instDecidableEqNat x x) (HeytingLean.Noneism.Term.var a) (HeytingLean.Noneism.Term.var x)
                              (@eq_self.{1} HeytingLean.Noneism.Var x)))))
                      (@congrArg.{1, 1} D Prop
                        (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ a) (ρ z)) (ρ a)
                        (@HeytingLean.Noneism.KripkeFO.Model.valEx W σ D inst M w)
                        (@ite_cond_eq_true.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ a)
                          (ρ z)
                          (@Eq.trans.{1} Prop (@Eq.{1} HeytingLean.Noneism.Var z x)
                            (@Eq.{1} HeytingLean.Noneism.Var x x) True
                            (@congrArg.{1, 1} HeytingLean.Noneism.Var Prop z x
                              (fun (x_1 : HeytingLean.Noneism.Var) => @Eq.{1} HeytingLean.Noneism.Var x_1 x) hzx)
                            (@eq_self.{1} HeytingLean.Noneism.Var x)))))
                    (iff_self (@HeytingLean.Noneism.KripkeFO.Model.valEx W σ D inst M w (ρ a)))))
              fun (hzx : Not (@Eq.{1} HeytingLean.Noneism.Var z x)) =>
              @of_eq_true
                (Iff
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                      (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var z))))
                  (@HeytingLean.Noneism.KripkeFO.Model.valEx W σ D inst M w
                    (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ a) (ρ z))))
                (@Eq.trans.{1} Prop
                  (Iff
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                        (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var z))))
                    (@HeytingLean.Noneism.KripkeFO.Model.valEx W σ D inst M w
                      (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ a) (ρ z))))
                  (Iff
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                      (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var z)))
                    (@HeytingLean.Noneism.KripkeFO.Model.valEx W σ D inst M w (ρ z)))
                  True
                  (@congr.{1, 1} Prop Prop
                    (Iff
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                          (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var z)))))
                    (Iff
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                        (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var z))))
                    (@HeytingLean.Noneism.KripkeFO.Model.valEx W σ D inst M w
                      (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ a) (ρ z)))
                    (@HeytingLean.Noneism.KripkeFO.Model.valEx W σ D inst M w (ρ z))
                    (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) ((b : Prop) → Prop)
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                        (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var z)))
                      (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var z))
                      (fun (x : HeytingLean.Noneism.Formula σ) =>
                        Iff (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w x))
                      (@Eq.trans.{1} (HeytingLean.Noneism.Formula σ)
                        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                          (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var z)))
                        (@HeytingLean.Noneism.Formula.eExists σ
                          (HeytingLean.Noneism.Syntax.substTerm x (HeytingLean.Noneism.Term.var a)
                            (HeytingLean.Noneism.Term.var z)))
                        (@HeytingLean.Noneism.Formula.eExists σ (HeytingLean.Noneism.Term.var z))
                        (@HeytingLean.Noneism.Syntax.substFormula.eq_4 σ x (HeytingLean.Noneism.Term.var a)
                          (HeytingLean.Noneism.Term.var z))
                        (@congrArg.{1, 1} HeytingLean.Noneism.Term (HeytingLean.Noneism.Formula σ)
                          (@ite.{1} HeytingLean.Noneism.Term (@Eq.{1} HeytingLean.Noneism.Var z x)
                            (instDecidableEqNat z x) (HeytingLean.Noneism.Term.var a) (HeytingLean.Noneism.Term.var z))
                          (HeytingLean.Noneism.Term.var z) (@HeytingLean.Noneism.Formula.eExists σ)
                          (@ite_cond_eq_false.{1} HeytingLean.Noneism.Term (@Eq.{1} HeytingLean.Noneism.Var z x)
                            (instDecidableEqNat z x) (HeytingLean.Noneism.Term.var a) (HeytingLean.Noneism.Term.var z)
                            (@eq_false (@Eq.{1} HeytingLean.Noneism.Var z x) hzx)))))
                    (@congrArg.{1, 1} D Prop
                      (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ a) (ρ z)) (ρ z)
                      (@HeytingLean.Noneism.KripkeFO.Model.valEx W σ D inst M w)
                      (@ite_cond_eq_false.{1} D (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x) (ρ a)
                        (ρ z) (@eq_false (@Eq.{1} HeytingLean.Noneism.Var z x) hzx))))
                  (iff_self (@HeytingLean.Noneism.KripkeFO.Model.valEx W σ D inst M w (ρ z)))))
            t (@Eq.symm.{1} HeytingLean.Noneism.Term t (HeytingLean.Noneism.Term.var z) h))
        (@Eq.refl.{1} HeytingLean.Noneism.Term t))
    (fun (φ : HeytingLean.Noneism.Formula σ)
        (ih :
          ∀ (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W),
            Iff
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                φ))
        (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W) =>
      @Iff.intro
        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
            (@HeytingLean.Noneism.Formula.not σ φ)))
        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
          (@HeytingLean.Noneism.Formula.not σ φ))
        (fun
            (h :
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                  (@HeytingLean.Noneism.Formula.not σ φ))) =>
          have hNot :
            ∀ (v : W),
              @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ) →
                  False :=
            @Eq.mpr.{0}
              (∀ (v : W),
                @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ) →
                    False)
              (∀ (v : W),
                @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                  Not
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))
              (@id.{0}
                (@Eq.{1} Prop
                  (∀ (v : W),
                    @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ) →
                        False)
                  (∀ (v : W),
                    @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                      Not
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))))
                (@forall_congr.{1} W
                  (fun (a_1 : W) =>
                    @LE.le.{0} W (@Preorder.toLE.{0} W inst) w a_1 →
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ a_1
                          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ) →
                        False)
                  (fun (a_1 : W) =>
                    @LE.le.{0} W (@Preorder.toLE.{0} W inst) w a_1 →
                      Not
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ a_1
                          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))
                  fun (v : W) =>
                  @implies_congr.{0, 0} (@LE.le.{0} W (@Preorder.toLE.{0} W inst) w v)
                    (@LE.le.{0} W (@Preorder.toLE.{0} W inst) w v)
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ) →
                      False)
                    (Not
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))
                    (@Eq.refl.{1} Prop (@LE.le.{0} W (@Preorder.toLE.{0} W inst) w v))
                    (@imp_false._simp_1
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))))
              (@Eq.mp.{0}
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                    (@HeytingLean.Noneism.Formula.not σ φ)))
                (∀ (v : W),
                  @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                    Not
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))
                (@Eq.trans.{1} Prop
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                      (@HeytingLean.Noneism.Formula.not σ φ)))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Formula.not σ
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))
                  (∀ (a_1 : W),
                    @LE.le.{0} W (@Preorder.toLE.{0} W inst) w a_1 →
                      Not
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ a_1
                          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))
                  (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) Prop
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                      (@HeytingLean.Noneism.Formula.not σ φ))
                    (@HeytingLean.Noneism.Formula.not σ
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w)
                    (@HeytingLean.Noneism.Syntax.substFormula.eq_5 σ x (HeytingLean.Noneism.Term.var a) φ))
                  (@forall_congr.{1} W
                    (fun (a_1 : W) =>
                      @LE.le.{0} W (@Preorder.toLE.{0} W inst) w a_1 →
                        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ a_1
                            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ) →
                          False)
                    (fun (a_1 : W) =>
                      @LE.le.{0} W (@Preorder.toLE.{0} W inst) w a_1 →
                        Not
                          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ a_1
                            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))
                    fun (v : W) =>
                    @implies_congr.{0, 0} (@LE.le.{0} W (@Preorder.toLE.{0} W inst) w v)
                      (@LE.le.{0} W (@Preorder.toLE.{0} W inst) w v)
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ) →
                        False)
                      (Not
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))
                      (@Eq.refl.{1} Prop (@LE.le.{0} W (@Preorder.toLE.{0} W inst) w v))
                      (@imp_false._simp_1
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))))
                h);
          fun (v : W) (hwv : @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v)
            (hvφ :
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) v
                φ) =>
          have this :
            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ) :=
            @Iff.mpr
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) v φ)
              (ih ρ v) hvφ;
          hNot v hwv this)
        fun
          (h :
            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
              (@HeytingLean.Noneism.Formula.not σ φ)) =>
        have hNot :
          ∀ (v : W),
            @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) v φ →
                False :=
          @Eq.mpr.{0}
            (∀ (v : W),
              @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) v
                    φ →
                  False)
            (∀ (v : W),
              @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                Not
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))
                    v φ))
            (@id.{0}
              (@Eq.{1} Prop
                (∀ (v : W),
                  @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))
                        v φ →
                      False)
                (∀ (v : W),
                  @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                    Not
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) v φ)))
              (@forall_congr.{1} W
                (fun (a_1 : W) =>
                  @LE.le.{0} W (@Preorder.toLE.{0} W inst) w a_1 →
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))
                        a_1 φ →
                      False)
                (fun (a_1 : W) =>
                  @LE.le.{0} W (@Preorder.toLE.{0} W inst) w a_1 →
                    Not
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a_1 φ))
                fun (v : W) =>
                @implies_congr.{0, 0} (@LE.le.{0} W (@Preorder.toLE.{0} W inst) w v)
                  (@LE.le.{0} W (@Preorder.toLE.{0} W inst) w v)
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))
                      v φ →
                    False)
                  (Not
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) v φ))
                  (@Eq.refl.{1} Prop (@LE.le.{0} W (@Preorder.toLE.{0} W inst) w v))
                  (@imp_false._simp_1
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) v φ))))
            (@Eq.mp.{0}
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                (@HeytingLean.Noneism.Formula.not σ φ))
              (∀ (v : W),
                @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                  Not
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) v φ))
              (@forall_congr.{1} W
                (fun (a_1 : W) =>
                  @LE.le.{0} W (@Preorder.toLE.{0} W inst) w a_1 →
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))
                        a_1 φ →
                      False)
                (fun (a_1 : W) =>
                  @LE.le.{0} W (@Preorder.toLE.{0} W inst) w a_1 →
                    Not
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) a_1 φ))
                fun (v : W) =>
                @implies_congr.{0, 0} (@LE.le.{0} W (@Preorder.toLE.{0} W inst) w v)
                  (@LE.le.{0} W (@Preorder.toLE.{0} W inst) w v)
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))
                      v φ →
                    False)
                  (Not
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) v φ))
                  (@Eq.refl.{1} Prop (@LE.le.{0} W (@Preorder.toLE.{0} W inst) w v))
                  (@imp_false._simp_1
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) v φ)))
              h);
        have this :
          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
            (@HeytingLean.Noneism.Formula.not σ
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)) :=
          fun (v : W) (hwv : @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v)
            (hvSub :
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)) =>
          have hvφ :
            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) v φ :=
            @Iff.mp
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) v φ)
              (ih ρ v) hvSub;
          hNot v hwv hvφ;
        @Eq.mpr.{0}
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Formula.not σ φ)))
          (∀ (v : W),
            @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
              Not
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))
          (@id.{0}
            (@Eq.{1} Prop
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                  (@HeytingLean.Noneism.Formula.not σ φ)))
              (∀ (v : W),
                @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                  Not
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))))
            (@Eq.trans.{1} Prop
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                  (@HeytingLean.Noneism.Formula.not σ φ)))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Formula.not σ
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))
              (∀ (a_1 : W),
                @LE.le.{0} W (@Preorder.toLE.{0} W inst) w a_1 →
                  Not
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ a_1
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))
              (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) Prop
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                  (@HeytingLean.Noneism.Formula.not σ φ))
                (@HeytingLean.Noneism.Formula.not σ
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w)
                (@HeytingLean.Noneism.Syntax.substFormula.eq_5 σ x (HeytingLean.Noneism.Term.var a) φ))
              (@forall_congr.{1} W
                (fun (a_1 : W) =>
                  @LE.le.{0} W (@Preorder.toLE.{0} W inst) w a_1 →
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ a_1
                        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ) →
                      False)
                (fun (a_1 : W) =>
                  @LE.le.{0} W (@Preorder.toLE.{0} W inst) w a_1 →
                    Not
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ a_1
                        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))
                fun (v : W) =>
                @implies_congr.{0, 0} (@LE.le.{0} W (@Preorder.toLE.{0} W inst) w v)
                  (@LE.le.{0} W (@Preorder.toLE.{0} W inst) w v)
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ) →
                    False)
                  (Not
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))
                  (@Eq.refl.{1} Prop (@LE.le.{0} W (@Preorder.toLE.{0} W inst) w v))
                  (@imp_false._simp_1
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))))))
          (@Eq.mp.{0}
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
              (@HeytingLean.Noneism.Formula.not σ
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))
            (∀ (v : W),
              @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                Not
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))
            (@forall_congr.{1} W
              (fun (a_1 : W) =>
                @LE.le.{0} W (@Preorder.toLE.{0} W inst) w a_1 →
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ a_1
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ) →
                    False)
              (fun (a_1 : W) =>
                @LE.le.{0} W (@Preorder.toLE.{0} W inst) w a_1 →
                  Not
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ a_1
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))
              fun (v : W) =>
              @implies_congr.{0, 0} (@LE.le.{0} W (@Preorder.toLE.{0} W inst) w v)
                (@LE.le.{0} W (@Preorder.toLE.{0} W inst) w v)
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ) →
                  False)
                (Not
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))
                (@Eq.refl.{1} Prop (@LE.le.{0} W (@Preorder.toLE.{0} W inst) w v))
                (@imp_false._simp_1
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))))
            this))
    (fun (φ ψ : HeytingLean.Noneism.Formula σ)
        (ihφ :
          ∀ (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W),
            Iff
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                φ))
        (ihψ :
          ∀ (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W),
            Iff
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) ψ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                ψ))
        (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W) =>
      @of_eq_true
        (Iff
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Formula.and σ φ ψ)))
          (And
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w φ)
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w ψ)))
        (@Eq.trans.{1} Prop
          (Iff
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                (@HeytingLean.Noneism.Formula.and σ φ ψ)))
            (And
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w φ)
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                ψ)))
          (Iff
            (And
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w φ)
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                ψ))
            (And
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w φ)
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                ψ)))
          True
          (@congrArg.{1, 1} Prop Prop
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                (@HeytingLean.Noneism.Formula.and σ φ ψ)))
            (And
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w φ)
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                ψ))
            (fun (x_1 : Prop) =>
              Iff x_1
                (And
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))
                    w φ)
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))
                    w ψ)))
            (@Eq.trans.{1} Prop
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                  (@HeytingLean.Noneism.Formula.and σ φ ψ)))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Formula.and σ
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) ψ)))
              (And
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                  φ)
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                  ψ))
              (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) Prop
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                  (@HeytingLean.Noneism.Formula.and σ φ ψ))
                (@HeytingLean.Noneism.Formula.and σ
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) ψ))
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w)
                (@HeytingLean.Noneism.Syntax.substFormula.eq_6 σ x (HeytingLean.Noneism.Term.var a) φ ψ))
              (@congr.{1, 1} Prop Prop
                (And
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))
                (And
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))
                    w φ))
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) ψ))
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                  ψ)
                (@congrArg.{1, 1} Prop ((b : Prop) → Prop)
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))
                    w φ)
                  And
                  (@propext
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w φ)
                    (ihφ ρ w)))
                (@propext
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) ψ))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))
                    w ψ)
                  (ihψ ρ w)))))
          (iff_self
            (And
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w φ)
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                ψ)))))
    (fun (φ ψ : HeytingLean.Noneism.Formula σ)
        (ihφ :
          ∀ (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W),
            Iff
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                φ))
        (ihψ :
          ∀ (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W),
            Iff
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) ψ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                ψ))
        (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W) =>
      @of_eq_true
        (Iff
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Formula.or σ φ ψ)))
          (Or (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w φ)
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w ψ)))
        (@Eq.trans.{1} Prop
          (Iff
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                (@HeytingLean.Noneism.Formula.or σ φ ψ)))
            (Or
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w φ)
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                ψ)))
          (Iff
            (Or
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w φ)
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                ψ))
            (Or
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w φ)
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                ψ)))
          True
          (@congrArg.{1, 1} Prop Prop
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                (@HeytingLean.Noneism.Formula.or σ φ ψ)))
            (Or
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w φ)
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                ψ))
            (fun (x_1 : Prop) =>
              Iff x_1
                (Or
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))
                    w φ)
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))
                    w ψ)))
            (@Eq.trans.{1} Prop
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                  (@HeytingLean.Noneism.Formula.or σ φ ψ)))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Formula.or σ
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) ψ)))
              (Or
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                  φ)
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                  ψ))
              (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) Prop
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                  (@HeytingLean.Noneism.Formula.or σ φ ψ))
                (@HeytingLean.Noneism.Formula.or σ
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) ψ))
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w)
                (@HeytingLean.Noneism.Syntax.substFormula.eq_7 σ x (HeytingLean.Noneism.Term.var a) φ ψ))
              (@congr.{1, 1} Prop Prop
                (Or
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))
                (Or
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))
                    w φ))
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) ψ))
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                  ψ)
                (@congrArg.{1, 1} Prop ((b : Prop) → Prop)
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))
                    w φ)
                  Or
                  (@propext
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w φ)
                    (ihφ ρ w)))
                (@propext
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) ψ))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))
                    w ψ)
                  (ihψ ρ w)))))
          (iff_self
            (Or
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w φ)
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                ψ)))))
    (fun (φ ψ : HeytingLean.Noneism.Formula σ)
        (ihφ :
          ∀ (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W),
            Iff
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                φ))
        (ihψ :
          ∀ (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W),
            Iff
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) ψ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                ψ))
        (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W) =>
      @Iff.intro
        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
            (@HeytingLean.Noneism.Formula.imp σ φ ψ)))
        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
          (@HeytingLean.Noneism.Formula.imp σ φ ψ))
        (fun
            (h :
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                  (@HeytingLean.Noneism.Formula.imp σ φ ψ))) =>
          have hImp :
            ∀ (v : W),
              @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ) →
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) ψ) :=
            @Eq.mp.{0}
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                  (@HeytingLean.Noneism.Formula.imp σ φ ψ)))
              (∀ (v : W),
                @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ) →
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) ψ))
              (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) Prop
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                  (@HeytingLean.Noneism.Formula.imp σ φ ψ))
                (@HeytingLean.Noneism.Formula.imp σ
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) ψ))
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w)
                (@HeytingLean.Noneism.Syntax.substFormula.eq_8 σ x (HeytingLean.Noneism.Term.var a) φ ψ))
              h;
          fun (v : W) (hwv : @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v)
            (hvφ :
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) v
                φ) =>
          have hvφ' :
            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ) :=
            @Iff.mpr
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) v φ)
              (ihφ ρ v) hvφ;
          have hvψ' :
            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) ψ) :=
            hImp v hwv hvφ';
          @Iff.mp
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) ψ))
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) v ψ)
            (ihψ ρ v) hvψ')
        fun
          (h :
            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
              (@HeytingLean.Noneism.Formula.imp σ φ ψ)) =>
        have hImp :
          ∀ (v : W),
            @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) v φ →
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) v
                  ψ :=
          h;
        have this :
          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
            (@HeytingLean.Noneism.Formula.imp σ
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) ψ)) :=
          fun (v : W) (hwv : @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v)
            (hvSubφ :
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)) =>
          have hvφ :
            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) v φ :=
            @Iff.mp
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) v φ)
              (ihφ ρ v) hvSubφ;
          have hvψ :
            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) v ψ :=
            hImp v hwv hvφ;
          @Iff.mpr
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) ψ))
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) v ψ)
            (ihψ ρ v) hvψ;
        @Eq.mpr.{0}
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Formula.imp σ φ ψ)))
          (∀ (v : W),
            @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ) →
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) ψ))
          (@id.{0}
            (@Eq.{1} Prop
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                  (@HeytingLean.Noneism.Formula.imp σ φ ψ)))
              (∀ (v : W),
                @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ) →
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ v
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) ψ)))
            (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) Prop
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                (@HeytingLean.Noneism.Formula.imp σ φ ψ))
              (@HeytingLean.Noneism.Formula.imp σ
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) ψ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w)
              (@HeytingLean.Noneism.Syntax.substFormula.eq_8 σ x (HeytingLean.Noneism.Term.var a) φ ψ)))
          this)
    (fun (z : HeytingLean.Noneism.Var) (φ : HeytingLean.Noneism.Formula σ)
        (ih :
          ∀ (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W),
            Iff
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                φ))
        (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W) =>
      @dite.{0}
        (Iff
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Formula.sigma σ z φ)))
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
            (@HeytingLean.Noneism.Formula.sigma σ z φ)))
        (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x)
        (fun (hzx : @Eq.{1} HeytingLean.Noneism.Var z x) =>
          @Eq.ndrec.{0, 1} HeytingLean.Noneism.Var z
            (fun (x : HeytingLean.Noneism.Var) =>
              ∀
                (ih :
                  ∀ (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W),
                    Iff
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w φ)),
                Iff
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                      (@HeytingLean.Noneism.Formula.sigma σ z φ)))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))
                    w (@HeytingLean.Noneism.Formula.sigma σ z φ)))
            (fun
                (ih :
                  ∀ (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W),
                    Iff
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                        (@HeytingLean.Noneism.Syntax.substFormula σ z (HeytingLean.Noneism.Term.var a) φ))
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D ρ z (ρ a)) w φ)) =>
              @of_eq_true
                (Iff
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.substFormula σ z (HeytingLean.Noneism.Term.var a)
                      (@HeytingLean.Noneism.Formula.sigma σ z φ)))
                  (@Exists.{1} D fun (x : D) =>
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z (ρ a)) z x) w
                      φ))
                (@Eq.trans.{1} Prop
                  (Iff
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                      (@HeytingLean.Noneism.Syntax.substFormula σ z (HeytingLean.Noneism.Term.var a)
                        (@HeytingLean.Noneism.Formula.sigma σ z φ)))
                    (@Exists.{1} D fun (x : D) =>
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z (ρ a)) z x)
                        w φ))
                  (Iff
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w (@HeytingLean.Noneism.Formula.sigma σ z φ))
                    (@Exists.{1} D fun (x : D) =>
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z x) w
                        φ))
                  True
                  (@congr.{1, 1} Prop Prop
                    (Iff
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                        (@HeytingLean.Noneism.Syntax.substFormula σ z (HeytingLean.Noneism.Term.var a)
                          (@HeytingLean.Noneism.Formula.sigma σ z φ))))
                    (Iff
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                        (@HeytingLean.Noneism.Formula.sigma σ z φ)))
                    (@Exists.{1} D fun (x : D) =>
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z (ρ a)) z x)
                        w φ)
                    (@Exists.{1} D fun (x : D) =>
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z x) w
                        φ)
                    (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) ((b : Prop) → Prop)
                      (@HeytingLean.Noneism.Syntax.substFormula σ z (HeytingLean.Noneism.Term.var a)
                        (@HeytingLean.Noneism.Formula.sigma σ z φ))
                      (@HeytingLean.Noneism.Formula.sigma σ z φ)
                      (fun (x : HeytingLean.Noneism.Formula σ) =>
                        Iff (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w x))
                      (@Eq.trans.{1} (HeytingLean.Noneism.Formula σ)
                        (@HeytingLean.Noneism.Syntax.substFormula σ z (HeytingLean.Noneism.Term.var a)
                          (@HeytingLean.Noneism.Formula.sigma σ z φ))
                        (@ite.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var z z)
                          (instDecidableEqNat z z) (@HeytingLean.Noneism.Formula.sigma σ z φ)
                          (@ite.{1} (HeytingLean.Noneism.Formula σ)
                            (And
                              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                (@HeytingLean.Noneism.Syntax.fvFormula σ φ) z))
                            (@instDecidableAnd
                              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                (@HeytingLean.Noneism.Syntax.fvFormula σ φ) z)
                              (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat z
                                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                              (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat z
                                (@HeytingLean.Noneism.Syntax.fvFormula σ φ)))
                            (have avoid : Finset.{0} HeytingLean.Noneism.Var :=
                              @Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                                  (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var
                                    (Finset.{0} HeytingLean.Noneism.Var)
                                    (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) z));
                            have z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
                            @HeytingLean.Noneism.Formula.sigma σ z'
                              (@HeytingLean.Noneism.Syntax.substFormula σ z (HeytingLean.Noneism.Term.var a)
                                (@HeytingLean.Noneism.Syntax.renameFormula σ z z' φ)))
                            (@HeytingLean.Noneism.Formula.sigma σ z
                              (@HeytingLean.Noneism.Syntax.substFormula σ z (HeytingLean.Noneism.Term.var a) φ))))
                        (@HeytingLean.Noneism.Formula.sigma σ z φ)
                        (@HeytingLean.Noneism.Syntax.substFormula.eq_9 σ z (HeytingLean.Noneism.Term.var a) z φ)
                        (@ite_cond_eq_true.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var z z)
                          (instDecidableEqNat z z) (@HeytingLean.Noneism.Formula.sigma σ z φ)
                          (@ite.{1} (HeytingLean.Noneism.Formula σ)
                            (And
                              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                (@HeytingLean.Noneism.Syntax.fvFormula σ φ) z))
                            (@instDecidableAnd
                              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                (@HeytingLean.Noneism.Syntax.fvFormula σ φ) z)
                              (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat z
                                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                              (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat z
                                (@HeytingLean.Noneism.Syntax.fvFormula σ φ)))
                            (have avoid : Finset.{0} HeytingLean.Noneism.Var :=
                              @Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                                  (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var
                                    (Finset.{0} HeytingLean.Noneism.Var)
                                    (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) z));
                            have z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
                            @HeytingLean.Noneism.Formula.sigma σ z'
                              (@HeytingLean.Noneism.Syntax.substFormula σ z (HeytingLean.Noneism.Term.var a)
                                (@HeytingLean.Noneism.Syntax.renameFormula σ z z' φ)))
                            (@HeytingLean.Noneism.Formula.sigma σ z
                              (@HeytingLean.Noneism.Syntax.substFormula σ z (HeytingLean.Noneism.Term.var a) φ)))
                          (@eq_self.{1} HeytingLean.Noneism.Var z))))
                    (@congrArg.{1, 1} (D → Prop) Prop
                      (fun (x : D) =>
                        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z (ρ a)) z
                            x)
                          w φ)
                      (fun (x : D) =>
                        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z x)
                          w φ)
                      (@Exists.{1} D)
                      (@funext.{1, 1} D (fun (x : D) => Prop)
                        (fun (x : D) =>
                          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z (ρ a)) z
                              x)
                            w φ)
                        (fun (x : D) =>
                          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                            (@HeytingLean.Noneism.KripkeFO.update D ρ z x) w φ)
                        fun (d : D) =>
                        @congrArg.{1, 1} (HeytingLean.Noneism.KripkeFO.Valuation D) Prop
                          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z (ρ a)) z
                            d)
                          (@HeytingLean.Noneism.KripkeFO.update D ρ z d)
                          (fun (x : HeytingLean.Noneism.KripkeFO.Valuation D) =>
                            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M x w φ)
                          (@HeytingLean.Noneism.KripkeFO.update_update_same D ρ z (ρ a) d))))
                  (iff_self
                    (@Exists.{1} D fun (d : D) =>
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) w
                        φ))))
            x hzx ih)
        fun (hzx : Not (@Eq.{1} HeytingLean.Noneism.Var z x)) =>
        @dite.{0}
          (Iff
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                (@HeytingLean.Noneism.Formula.sigma σ z φ)))
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
              (@HeytingLean.Noneism.Formula.sigma σ z φ)))
          (@Eq.{1} HeytingLean.Noneism.Var z a) (instDecidableEqNat z a)
          (fun (hza : @Eq.{1} HeytingLean.Noneism.Var z a) =>
            @dite.{0}
              (Iff
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                    (@HeytingLean.Noneism.Formula.sigma σ z φ)))
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                  (@HeytingLean.Noneism.Formula.sigma σ z φ)))
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x)
              (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat x
                (@HeytingLean.Noneism.Syntax.fvFormula σ φ))
              (fun
                  (hxFree :
                    @Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ)
                      x) =>
                have hax : @Ne.{1} HeytingLean.Noneism.Var a x := fun (hax : @Eq.{1} HeytingLean.Noneism.Var a x) =>
                  hzx (@Eq.trans.{1} HeytingLean.Noneism.Var z a x hza hax);
                have hCap :
                  Iff
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                        (@HeytingLean.Noneism.Formula.sigma σ a φ)))
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                      (@HeytingLean.Noneism.Formula.sigma σ a φ)) :=
                  @HeytingLean.Noneism.KripkeFO.forces_substFormula_var_sigma_capture σ W inst D M ρ w x a φ hax hxFree;
                @Eq.mpr.{0}
                  (Iff
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                        (@HeytingLean.Noneism.Formula.sigma σ z φ)))
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w (@HeytingLean.Noneism.Formula.sigma σ z φ)))
                  (Iff
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                        (@HeytingLean.Noneism.Formula.sigma σ a φ)))
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w (@HeytingLean.Noneism.Formula.sigma σ a φ)))
                  (@id.{0}
                    (@Eq.{1} Prop
                      (Iff
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                            (@HeytingLean.Noneism.Formula.sigma σ z φ)))
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                          (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                          (@HeytingLean.Noneism.Formula.sigma σ z φ)))
                      (Iff
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                            (@HeytingLean.Noneism.Formula.sigma σ a φ)))
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                          (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                          (@HeytingLean.Noneism.Formula.sigma σ a φ))))
                    (@congr.{1, 1} Prop Prop
                      (Iff
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                            (@HeytingLean.Noneism.Formula.sigma σ z φ))))
                      (Iff
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                            (@HeytingLean.Noneism.Formula.sigma σ a φ))))
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w (@HeytingLean.Noneism.Formula.sigma σ z φ))
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w (@HeytingLean.Noneism.Formula.sigma σ a φ))
                      (@congrArg.{1, 1} HeytingLean.Noneism.Var ((b : Prop) → Prop) z a
                        (fun (x_1 : HeytingLean.Noneism.Var) =>
                          Iff
                            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                                (@HeytingLean.Noneism.Formula.sigma σ x_1 φ))))
                        hza)
                      (@congrArg.{1, 1} HeytingLean.Noneism.Var Prop z a
                        (fun (x_1 : HeytingLean.Noneism.Var) =>
                          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                            (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                            (@HeytingLean.Noneism.Formula.sigma σ x_1 φ))
                        hza)))
                  hCap)
              fun
                (hxFree :
                  Not
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ)
                      x)) =>
              have hxNotSigma :
                Not
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (@HeytingLean.Noneism.Syntax.fvFormula σ (@HeytingLean.Noneism.Formula.sigma σ z φ)) x) :=
                @of_eq_true
                  (Not
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (@Finset.erase.{0} HeytingLean.Noneism.Var instDecidableEqNat
                        (@HeytingLean.Noneism.Syntax.fvFormula σ φ) z)
                      x))
                  (@Eq.trans.{1} Prop
                    (Not
                      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                        (@Finset.erase.{0} HeytingLean.Noneism.Var instDecidableEqNat
                          (@HeytingLean.Noneism.Syntax.fvFormula σ φ) z)
                        x))
                    (Not False) True
                    (@congrArg.{1, 1} Prop Prop
                      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                        (@Finset.erase.{0} HeytingLean.Noneism.Var instDecidableEqNat
                          (@HeytingLean.Noneism.Syntax.fvFormula σ φ) z)
                        x)
                      False Not
                      (@Eq.trans.{1} Prop
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (@Finset.erase.{0} HeytingLean.Noneism.Var instDecidableEqNat
                            (@HeytingLean.Noneism.Syntax.fvFormula σ φ) z)
                          x)
                        (And (@Ne.{1} HeytingLean.Noneism.Var x a)
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))
                        False
                        (@Eq.trans.{1} Prop
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (@Finset.erase.{0} HeytingLean.Noneism.Var instDecidableEqNat
                              (@HeytingLean.Noneism.Syntax.fvFormula σ φ) z)
                            x)
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (@Finset.erase.{0} HeytingLean.Noneism.Var instDecidableEqNat
                              (@HeytingLean.Noneism.Syntax.fvFormula σ φ) a)
                            x)
                          (And (@Ne.{1} HeytingLean.Noneism.Var x a)
                            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                              (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))
                          (@congrArg.{1, 1} HeytingLean.Noneism.Var Prop z a
                            (fun (x_1 : HeytingLean.Noneism.Var) =>
                              @Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                (@Finset.erase.{0} HeytingLean.Noneism.Var instDecidableEqNat
                                  (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x_1)
                                x)
                            hza)
                          (@Finset.mem_erase._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat x a
                            (@HeytingLean.Noneism.Syntax.fvFormula σ φ)))
                        (@Eq.trans.{1} Prop
                          (And (Not (@Eq.{1} HeytingLean.Noneism.Var x a))
                            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                              (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))
                          (And (Not (@Eq.{1} HeytingLean.Noneism.Var x a)) False) False
                          (@congrArg.{1, 1} Prop Prop
                            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                              (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x)
                            False (And (Not (@Eq.{1} HeytingLean.Noneism.Var x a)))
                            (@eq_false
                              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x)
                              hxFree))
                          (and_false (Not (@Eq.{1} HeytingLean.Noneism.Var x a))))))
                    not_false_eq_true);
              @HeytingLean.Noneism.KripkeFO.forces_substFormula_var_of_not_mem_boundVars_or_not_mem_fvFormula σ W inst D
                M ρ w x a (@HeytingLean.Noneism.Formula.sigma σ z φ)
                (@Or.inr
                  (Not
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (@HeytingLean.Noneism.Syntax.boundVars σ (@HeytingLean.Noneism.Formula.sigma σ z φ)) a))
                  (Not
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (@HeytingLean.Noneism.Syntax.fvFormula σ (@HeytingLean.Noneism.Formula.sigma σ z φ)) x))
                  hxNotSigma))
          fun (hza : Not (@Eq.{1} HeytingLean.Noneism.Var z a)) =>
          have haz : @Ne.{1} HeytingLean.Noneism.Var a z := @Ne.symm.{1} HeytingLean.Noneism.Var z a hza;
          have hfvt :
            Not
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z) :=
            @of_eq_true
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)
                  z))
              (@Eq.trans.{1} Prop
                (Not
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)
                    z))
                (Not False) True
                (@congrArg.{1, 1} Prop Prop
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)
                    z)
                  False Not
                  (@Eq.trans.{1} Prop
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)
                      z)
                    (@Eq.{1} HeytingLean.Noneism.Var z a) False
                    (@Finset.mem_singleton._simp_1.{0} HeytingLean.Noneism.Var a z)
                    (@eq_false (@Eq.{1} HeytingLean.Noneism.Var z a) hza)))
                not_false_eq_true);
          @Eq.mpr.{0}
            (Iff
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                  (@HeytingLean.Noneism.Formula.sigma σ z φ)))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                (@HeytingLean.Noneism.Formula.sigma σ z φ)))
            (Iff
              (@Exists.{1} D fun (d : D) =>
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) w
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
              (@Exists.{1} D fun (d : D) =>
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z d) w φ))
            (@id.{0}
              (@Eq.{1} Prop
                (Iff
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                      (@HeytingLean.Noneism.Formula.sigma σ z φ)))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))
                    w (@HeytingLean.Noneism.Formula.sigma σ z φ)))
                (Iff
                  (@Exists.{1} D fun (d : D) =>
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) w
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                  (@Exists.{1} D fun (d : D) =>
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z d) w
                      φ)))
              (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) Prop
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                  (@HeytingLean.Noneism.Formula.sigma σ z φ))
                (@HeytingLean.Noneism.Formula.sigma σ z
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                (fun (x_1 : HeytingLean.Noneism.Formula σ) =>
                  Iff (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w x_1)
                    (@Exists.{1} D fun (d : D) =>
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z d)
                        w φ))
                (@Eq.trans.{1} (HeytingLean.Noneism.Formula σ)
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                    (@HeytingLean.Noneism.Formula.sigma σ z φ))
                  (@ite.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var z x)
                    (instDecidableEqNat z x) (@HeytingLean.Noneism.Formula.sigma σ z φ)
                    (@ite.{1} (HeytingLean.Noneism.Formula σ)
                      (And
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))
                      (@instDecidableAnd
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x)
                        (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat z
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                        (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat x
                          (@HeytingLean.Noneism.Syntax.fvFormula σ φ)))
                      (have avoid : Finset.{0} HeytingLean.Noneism.Var :=
                        @Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                          (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                            (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) z));
                      have z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
                      @HeytingLean.Noneism.Formula.sigma σ z'
                        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                          (@HeytingLean.Noneism.Syntax.renameFormula σ z z' φ)))
                      (@HeytingLean.Noneism.Formula.sigma σ z
                        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))))
                  (@HeytingLean.Noneism.Formula.sigma σ z
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                  (@HeytingLean.Noneism.Syntax.substFormula.eq_9 σ x (HeytingLean.Noneism.Term.var a) z φ)
                  (@Eq.trans.{1} (HeytingLean.Noneism.Formula σ)
                    (@ite.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var z x)
                      (instDecidableEqNat z x) (@HeytingLean.Noneism.Formula.sigma σ z φ)
                      (@ite.{1} (HeytingLean.Noneism.Formula σ)
                        (And
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))
                        (@instDecidableAnd
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x)
                          (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat z
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                          (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat x
                            (@HeytingLean.Noneism.Syntax.fvFormula σ φ)))
                        (have avoid : Finset.{0} HeytingLean.Noneism.Var :=
                          @Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                              (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                            (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                              (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) z));
                        have z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
                        @HeytingLean.Noneism.Formula.sigma σ z'
                          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                            (@HeytingLean.Noneism.Syntax.renameFormula σ z z' φ)))
                        (@HeytingLean.Noneism.Formula.sigma σ z
                          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))))
                    (@ite.{1} (HeytingLean.Noneism.Formula σ)
                      (And
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))
                      (@instDecidableAnd
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x)
                        (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat z
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                        (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat x
                          (@HeytingLean.Noneism.Syntax.fvFormula σ φ)))
                      (have avoid : Finset.{0} HeytingLean.Noneism.Var :=
                        @Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                          (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                            (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) z));
                      have z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
                      @HeytingLean.Noneism.Formula.sigma σ z'
                        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                          (@HeytingLean.Noneism.Syntax.renameFormula σ z z' φ)))
                      (@HeytingLean.Noneism.Formula.sigma σ z
                        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))
                    (@HeytingLean.Noneism.Formula.sigma σ z
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                    (@ite_cond_eq_false.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var z x)
                      (instDecidableEqNat z x) (@HeytingLean.Noneism.Formula.sigma σ z φ)
                      (@ite.{1} (HeytingLean.Noneism.Formula σ)
                        (And
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))
                        (@instDecidableAnd
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x)
                          (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat z
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                          (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat x
                            (@HeytingLean.Noneism.Syntax.fvFormula σ φ)))
                        (have avoid : Finset.{0} HeytingLean.Noneism.Var :=
                          @Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                              (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                            (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                              (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) z));
                        have z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
                        @HeytingLean.Noneism.Formula.sigma σ z'
                          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                            (@HeytingLean.Noneism.Syntax.renameFormula σ z z' φ)))
                        (@HeytingLean.Noneism.Formula.sigma σ z
                          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))
                      (@eq_false (@Eq.{1} HeytingLean.Noneism.Var z x) hzx))
                    (@ite_cond_eq_false.{1} (HeytingLean.Noneism.Formula σ)
                      (And
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))
                      (@instDecidableAnd
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x)
                        (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat z
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                        (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat x
                          (@HeytingLean.Noneism.Syntax.fvFormula σ φ)))
                      (have avoid : Finset.{0} HeytingLean.Noneism.Var :=
                        @Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                          (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                            (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) z));
                      have z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
                      @HeytingLean.Noneism.Formula.sigma σ z'
                        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                          (@HeytingLean.Noneism.Syntax.renameFormula σ z z' φ)))
                      (@HeytingLean.Noneism.Formula.sigma σ z
                        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                      (@Eq.trans.{1} Prop
                        (And
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))
                        (And False
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))
                        False
                        (@congrArg.{1, 1} Prop Prop
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                          False
                          (fun (x_1 : Prop) =>
                            And x_1
                              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))
                          (@eq_false
                            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                            hfvt))
                        (false_and
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))))))))
            (@Iff.intro
              (@Exists.{1} D fun (d : D) =>
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) w
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
              (@Exists.{1} D fun (d : D) =>
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z d) w φ)
              (fun
                  (a_1 :
                    @Exists.{1} D fun (d : D) =>
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) w
                        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)) =>
                @Exists.casesOn.{1} D
                  (fun (d : D) =>
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) w
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                  (fun
                      (x_1 :
                        @Exists.{1} D fun (d : D) =>
                          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                            (@HeytingLean.Noneism.KripkeFO.update D ρ z d) w
                            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)) =>
                    @Exists.{1} D fun (d : D) =>
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z d)
                        w φ)
                  a_1
                  fun (d : D)
                    (hd :
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) w
                        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)) =>
                  @Exists.intro.{1} D
                    (fun (d : D) =>
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z d)
                        w φ)
                    d
                    (have hih :
                      Iff
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                          (@HeytingLean.Noneism.KripkeFO.update D ρ z d) w
                          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                            (@HeytingLean.Noneism.KripkeFO.update D ρ z d a))
                          w φ) :=
                      ih (@HeytingLean.Noneism.KripkeFO.update D ρ z d) w;
                    have hb :
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                          (@HeytingLean.Noneism.KripkeFO.update D ρ z d a))
                        w φ :=
                      @Iff.mp
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                          (@HeytingLean.Noneism.KripkeFO.update D ρ z d) w
                          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                            (@HeytingLean.Noneism.KripkeFO.update D ρ z d a))
                          w φ)
                        hih hd;
                    have hza' : @Eq.{1} D (@HeytingLean.Noneism.KripkeFO.update D ρ z d a) (ρ a) :=
                      @of_eq_true
                        (@Eq.{1} D (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z) (instDecidableEqNat a z) d (ρ a))
                          (ρ a))
                        (@Eq.trans.{1} Prop
                          (@Eq.{1} D (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z) (instDecidableEqNat a z) d (ρ a))
                            (ρ a))
                          (@Eq.{1} D (ρ a) (ρ a)) True
                          (@congrArg.{1, 1} D Prop
                            (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z) (instDecidableEqNat a z) d (ρ a)) (ρ a)
                            (fun (x : D) => @Eq.{1} D x (ρ a))
                            (@ite_cond_eq_false.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z) (instDecidableEqNat a z) d
                              (ρ a) (@eq_false (@Eq.{1} HeytingLean.Noneism.Var a z) haz)))
                          (@eq_self.{1} D (ρ a)));
                    have hb' :
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ a))
                        w φ :=
                      @Eq.mp.{0}
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                            (@HeytingLean.Noneism.KripkeFO.update D ρ z d a))
                          w φ)
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                            (ρ a))
                          w φ)
                        (@congrArg.{1, 1} D Prop (@HeytingLean.Noneism.KripkeFO.update D ρ z d a) (ρ a)
                          (fun (x_1 : D) =>
                            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                                x_1)
                              w φ)
                          hza')
                        hb;
                    have hcomm :
                      @Eq.{1} (HeytingLean.Noneism.KripkeFO.Valuation D)
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ a))
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z
                          d) :=
                      @HeytingLean.Noneism.KripkeFO.update_comm D ρ z x d (ρ a) hzx;
                    @Eq.mp.{0}
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ a))
                        w φ)
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z d)
                        w φ)
                      (@congrArg.{1, 1} (HeytingLean.Noneism.KripkeFO.Valuation D) Prop
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ a))
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z d)
                        (fun (x : HeytingLean.Noneism.KripkeFO.Valuation D) =>
                          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M x w φ)
                        hcomm)
                      hb'))
              fun
                (a_1 :
                  @Exists.{1} D fun (d : D) =>
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z d) w
                      φ) =>
              @Exists.casesOn.{1} D
                (fun (d : D) =>
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z d) w φ)
                (fun
                    (x_1 :
                      @Exists.{1} D fun (d : D) =>
                        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z
                            d)
                          w φ) =>
                  @Exists.{1} D fun (d : D) =>
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) w
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                a_1
                fun (d : D)
                  (hd :
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z d) w
                      φ) =>
                @Exists.intro.{1} D
                  (fun (d : D) =>
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) w
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                  d
                  (have hih :
                    Iff
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d)
                        w (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                          (@HeytingLean.Noneism.KripkeFO.update D ρ z d a))
                        w φ) :=
                    ih (@HeytingLean.Noneism.KripkeFO.update D ρ z d) w;
                  have hcomm :
                    @Eq.{1} (HeytingLean.Noneism.KripkeFO.Valuation D)
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z d)
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ a)) :=
                    @Eq.symm.{1} (HeytingLean.Noneism.KripkeFO.Valuation D)
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ a))
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z d)
                      (@HeytingLean.Noneism.KripkeFO.update_comm D ρ z x d (ρ a) hzx);
                  have hd' :
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ a)) w
                      φ :=
                    @Eq.mp.{0}
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z d)
                        w φ)
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ a))
                        w φ)
                      (@congrArg.{1, 1} (HeytingLean.Noneism.KripkeFO.Valuation D) Prop
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z d)
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ a))
                        (fun (x : HeytingLean.Noneism.KripkeFO.Valuation D) =>
                          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M x w φ)
                        hcomm)
                      hd;
                  have hza' : @Eq.{1} D (@HeytingLean.Noneism.KripkeFO.update D ρ z d a) (ρ a) :=
                    @of_eq_true
                      (@Eq.{1} D (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z) (instDecidableEqNat a z) d (ρ a))
                        (ρ a))
                      (@Eq.trans.{1} Prop
                        (@Eq.{1} D (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z) (instDecidableEqNat a z) d (ρ a))
                          (ρ a))
                        (@Eq.{1} D (ρ a) (ρ a)) True
                        (@congrArg.{1, 1} D Prop
                          (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z) (instDecidableEqNat a z) d (ρ a)) (ρ a)
                          (fun (x : D) => @Eq.{1} D x (ρ a))
                          (@ite_cond_eq_false.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z) (instDecidableEqNat a z) d
                            (ρ a) (@eq_false (@Eq.{1} HeytingLean.Noneism.Var a z) haz)))
                        (@eq_self.{1} D (ρ a)));
                  have hd'' :
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                        (@HeytingLean.Noneism.KripkeFO.update D ρ z d a))
                      w φ :=
                    @Eq.mpr.{0}
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                          (@HeytingLean.Noneism.KripkeFO.update D ρ z d a))
                        w φ)
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ a))
                        w φ)
                      (@id.{0}
                        (@Eq.{1} Prop
                          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                              (@HeytingLean.Noneism.KripkeFO.update D ρ z d a))
                            w φ)
                          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                              (ρ a))
                            w φ))
                        (@congrArg.{1, 1} D Prop (@HeytingLean.Noneism.KripkeFO.update D ρ z d a) (ρ a)
                          (fun (x_1 : D) =>
                            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                                x_1)
                              w φ)
                          hza'))
                      hd';
                  @Iff.mpr
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) w
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                        (@HeytingLean.Noneism.KripkeFO.update D ρ z d a))
                      w φ)
                    hih hd'')))
    (fun (z : HeytingLean.Noneism.Var) (φ : HeytingLean.Noneism.Formula σ)
        (ih :
          ∀ (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W),
            Iff
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                φ))
        (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W) =>
      @dite.{0}
        (Iff
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
              (@HeytingLean.Noneism.Formula.pi σ z φ)))
          (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
            (@HeytingLean.Noneism.Formula.pi σ z φ)))
        (@Eq.{1} HeytingLean.Noneism.Var z x) (instDecidableEqNat z x)
        (fun (hzx : @Eq.{1} HeytingLean.Noneism.Var z x) =>
          @Eq.ndrec.{0, 1} HeytingLean.Noneism.Var z
            (fun (x : HeytingLean.Noneism.Var) =>
              ∀
                (ih :
                  ∀ (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W),
                    Iff
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w φ)),
                Iff
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                      (@HeytingLean.Noneism.Formula.pi σ z φ)))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))
                    w (@HeytingLean.Noneism.Formula.pi σ z φ)))
            (fun
                (ih :
                  ∀ (ρ : HeytingLean.Noneism.KripkeFO.Valuation D) (w : W),
                    Iff
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                        (@HeytingLean.Noneism.Syntax.substFormula σ z (HeytingLean.Noneism.Term.var a) φ))
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D ρ z (ρ a)) w φ)) =>
              @of_eq_true
                (Iff
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.substFormula σ z (HeytingLean.Noneism.Term.var a)
                      (@HeytingLean.Noneism.Formula.pi σ z φ)))
                  (∀ (a_1 : W),
                    @LE.le.{0} W (@Preorder.toLE.{0} W inst) w a_1 →
                      ∀ (a_3 : D),
                        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z (ρ a)) z
                            a_3)
                          a_1 φ))
                (@Eq.trans.{1} Prop
                  (Iff
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                      (@HeytingLean.Noneism.Syntax.substFormula σ z (HeytingLean.Noneism.Term.var a)
                        (@HeytingLean.Noneism.Formula.pi σ z φ)))
                    (∀ (a_1 : W),
                      @LE.le.{0} W (@Preorder.toLE.{0} W inst) w a_1 →
                        ∀ (a_3 : D),
                          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z (ρ a)) z
                              a_3)
                            a_1 φ))
                  (Iff (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w (@HeytingLean.Noneism.Formula.pi σ z φ))
                    (∀ (a : W),
                      @LE.le.{0} W (@Preorder.toLE.{0} W inst) w a →
                        ∀ (a_2 : D),
                          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                            (@HeytingLean.Noneism.KripkeFO.update D ρ z a_2) a φ))
                  True
                  (@congr.{1, 1} Prop Prop
                    (Iff
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                        (@HeytingLean.Noneism.Syntax.substFormula σ z (HeytingLean.Noneism.Term.var a)
                          (@HeytingLean.Noneism.Formula.pi σ z φ))))
                    (Iff
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w (@HeytingLean.Noneism.Formula.pi σ z φ)))
                    (∀ (a_1 : W),
                      @LE.le.{0} W (@Preorder.toLE.{0} W inst) w a_1 →
                        ∀ (a_3 : D),
                          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z (ρ a)) z
                              a_3)
                            a_1 φ)
                    (∀ (a : W),
                      @LE.le.{0} W (@Preorder.toLE.{0} W inst) w a →
                        ∀ (a_2 : D),
                          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                            (@HeytingLean.Noneism.KripkeFO.update D ρ z a_2) a φ)
                    (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) ((b : Prop) → Prop)
                      (@HeytingLean.Noneism.Syntax.substFormula σ z (HeytingLean.Noneism.Term.var a)
                        (@HeytingLean.Noneism.Formula.pi σ z φ))
                      (@HeytingLean.Noneism.Formula.pi σ z φ)
                      (fun (x : HeytingLean.Noneism.Formula σ) =>
                        Iff (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w x))
                      (@Eq.trans.{1} (HeytingLean.Noneism.Formula σ)
                        (@HeytingLean.Noneism.Syntax.substFormula σ z (HeytingLean.Noneism.Term.var a)
                          (@HeytingLean.Noneism.Formula.pi σ z φ))
                        (@ite.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var z z)
                          (instDecidableEqNat z z) (@HeytingLean.Noneism.Formula.pi σ z φ)
                          (@ite.{1} (HeytingLean.Noneism.Formula σ)
                            (And
                              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                (@HeytingLean.Noneism.Syntax.fvFormula σ φ) z))
                            (@instDecidableAnd
                              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                (@HeytingLean.Noneism.Syntax.fvFormula σ φ) z)
                              (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat z
                                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                              (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat z
                                (@HeytingLean.Noneism.Syntax.fvFormula σ φ)))
                            (have avoid : Finset.{0} HeytingLean.Noneism.Var :=
                              @Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                                  (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var
                                    (Finset.{0} HeytingLean.Noneism.Var)
                                    (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) z));
                            have z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
                            @HeytingLean.Noneism.Formula.pi σ z'
                              (@HeytingLean.Noneism.Syntax.substFormula σ z (HeytingLean.Noneism.Term.var a)
                                (@HeytingLean.Noneism.Syntax.renameFormula σ z z' φ)))
                            (@HeytingLean.Noneism.Formula.pi σ z
                              (@HeytingLean.Noneism.Syntax.substFormula σ z (HeytingLean.Noneism.Term.var a) φ))))
                        (@HeytingLean.Noneism.Formula.pi σ z φ)
                        (@HeytingLean.Noneism.Syntax.substFormula.eq_10 σ z (HeytingLean.Noneism.Term.var a) z φ)
                        (@ite_cond_eq_true.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var z z)
                          (instDecidableEqNat z z) (@HeytingLean.Noneism.Formula.pi σ z φ)
                          (@ite.{1} (HeytingLean.Noneism.Formula σ)
                            (And
                              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                (@HeytingLean.Noneism.Syntax.fvFormula σ φ) z))
                            (@instDecidableAnd
                              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                (@HeytingLean.Noneism.Syntax.fvFormula σ φ) z)
                              (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat z
                                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                              (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat z
                                (@HeytingLean.Noneism.Syntax.fvFormula σ φ)))
                            (have avoid : Finset.{0} HeytingLean.Noneism.Var :=
                              @Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                                (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                                  (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                                  (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                                  (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                                (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                  (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) z
                                  (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var
                                    (Finset.{0} HeytingLean.Noneism.Var)
                                    (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) z));
                            have z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
                            @HeytingLean.Noneism.Formula.pi σ z'
                              (@HeytingLean.Noneism.Syntax.substFormula σ z (HeytingLean.Noneism.Term.var a)
                                (@HeytingLean.Noneism.Syntax.renameFormula σ z z' φ)))
                            (@HeytingLean.Noneism.Formula.pi σ z
                              (@HeytingLean.Noneism.Syntax.substFormula σ z (HeytingLean.Noneism.Term.var a) φ)))
                          (@eq_self.{1} HeytingLean.Noneism.Var z))))
                    (@forall_congr.{1} W
                      (fun (a_1 : W) =>
                        @LE.le.{0} W (@Preorder.toLE.{0} W inst) w a_1 →
                          ∀ (a_3 : D),
                            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z (ρ a))
                                z a_3)
                              a_1 φ)
                      (fun (a : W) =>
                        @LE.le.{0} W (@Preorder.toLE.{0} W inst) w a →
                          ∀ (a_2 : D),
                            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                              (@HeytingLean.Noneism.KripkeFO.update D ρ z a_2) a φ)
                      fun (v : W) =>
                      @implies_congr.{0, 0} (@LE.le.{0} W (@Preorder.toLE.{0} W inst) w v)
                        (@LE.le.{0} W (@Preorder.toLE.{0} W inst) w v)
                        (∀ (a_1 : D),
                          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z (ρ a)) z
                              a_1)
                            v φ)
                        (∀ (a : D),
                          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                            (@HeytingLean.Noneism.KripkeFO.update D ρ z a) v φ)
                        (@Eq.refl.{1} Prop (@LE.le.{0} W (@Preorder.toLE.{0} W inst) w v))
                        (@forall_congr.{1} D
                          (fun (a_1 : D) =>
                            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                              (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z (ρ a))
                                z a_1)
                              v φ)
                          (fun (a : D) =>
                            @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                              (@HeytingLean.Noneism.KripkeFO.update D ρ z a) v φ)
                          fun (d : D) =>
                          @congrArg.{1, 1} (HeytingLean.Noneism.KripkeFO.Valuation D) Prop
                            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z (ρ a)) z
                              d)
                            (@HeytingLean.Noneism.KripkeFO.update D ρ z d)
                            (fun (x : HeytingLean.Noneism.KripkeFO.Valuation D) =>
                              @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M x v φ)
                            (@HeytingLean.Noneism.KripkeFO.update_update_same D ρ z (ρ a) d))))
                  (iff_self
                    (∀ (v : W),
                      @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                        ∀ (d : D),
                          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                            (@HeytingLean.Noneism.KripkeFO.update D ρ z d) v φ))))
            x hzx ih)
        fun (hzx : Not (@Eq.{1} HeytingLean.Noneism.Var z x)) =>
        @dite.{0}
          (Iff
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                (@HeytingLean.Noneism.Formula.pi σ z φ)))
            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
              (@HeytingLean.Noneism.Formula.pi σ z φ)))
          (@Eq.{1} HeytingLean.Noneism.Var z a) (instDecidableEqNat z a)
          (fun (hza : @Eq.{1} HeytingLean.Noneism.Var z a) =>
            @dite.{0}
              (Iff
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                    (@HeytingLean.Noneism.Formula.pi σ z φ)))
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                  (@HeytingLean.Noneism.Formula.pi σ z φ)))
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x)
              (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat x
                (@HeytingLean.Noneism.Syntax.fvFormula σ φ))
              (fun
                  (hxFree :
                    @Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ)
                      x) =>
                have hax : @Ne.{1} HeytingLean.Noneism.Var a x := fun (hax : @Eq.{1} HeytingLean.Noneism.Var a x) =>
                  hzx (@Eq.trans.{1} HeytingLean.Noneism.Var z a x hza hax);
                have hCap :
                  Iff
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                        (@HeytingLean.Noneism.Formula.pi σ a φ)))
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w (@HeytingLean.Noneism.Formula.pi σ a φ)) :=
                  @HeytingLean.Noneism.KripkeFO.forces_substFormula_var_pi_capture σ W inst D M ρ w x a φ hax hxFree;
                @Eq.mpr.{0}
                  (Iff
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                        (@HeytingLean.Noneism.Formula.pi σ z φ)))
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w (@HeytingLean.Noneism.Formula.pi σ z φ)))
                  (Iff
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                        (@HeytingLean.Noneism.Formula.pi σ a φ)))
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w (@HeytingLean.Noneism.Formula.pi σ a φ)))
                  (@id.{0}
                    (@Eq.{1} Prop
                      (Iff
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                            (@HeytingLean.Noneism.Formula.pi σ z φ)))
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                          (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w (@HeytingLean.Noneism.Formula.pi σ z φ)))
                      (Iff
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                            (@HeytingLean.Noneism.Formula.pi σ a φ)))
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                          (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                          (@HeytingLean.Noneism.Formula.pi σ a φ))))
                    (@congr.{1, 1} Prop Prop
                      (Iff
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                            (@HeytingLean.Noneism.Formula.pi σ z φ))))
                      (Iff
                        (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                            (@HeytingLean.Noneism.Formula.pi σ a φ))))
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w (@HeytingLean.Noneism.Formula.pi σ z φ))
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w (@HeytingLean.Noneism.Formula.pi σ a φ))
                      (@congrArg.{1, 1} HeytingLean.Noneism.Var ((b : Prop) → Prop) z a
                        (fun (x_1 : HeytingLean.Noneism.Var) =>
                          Iff
                            (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                              (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                                (@HeytingLean.Noneism.Formula.pi σ x_1 φ))))
                        hza)
                      (@congrArg.{1, 1} HeytingLean.Noneism.Var Prop z a
                        (fun (x_1 : HeytingLean.Noneism.Var) =>
                          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                            (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                            (@HeytingLean.Noneism.Formula.pi σ x_1 φ))
                        hza)))
                  hCap)
              fun
                (hxFree :
                  Not
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var) (@HeytingLean.Noneism.Syntax.fvFormula σ φ)
                      x)) =>
              have hxNotPi :
                Not
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (@HeytingLean.Noneism.Syntax.fvFormula σ (@HeytingLean.Noneism.Formula.pi σ z φ)) x) :=
                @of_eq_true
                  (Not
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (@Finset.erase.{0} HeytingLean.Noneism.Var instDecidableEqNat
                        (@HeytingLean.Noneism.Syntax.fvFormula σ φ) z)
                      x))
                  (@Eq.trans.{1} Prop
                    (Not
                      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                        (@Finset.erase.{0} HeytingLean.Noneism.Var instDecidableEqNat
                          (@HeytingLean.Noneism.Syntax.fvFormula σ φ) z)
                        x))
                    (Not False) True
                    (@congrArg.{1, 1} Prop Prop
                      (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                        (@Finset.erase.{0} HeytingLean.Noneism.Var instDecidableEqNat
                          (@HeytingLean.Noneism.Syntax.fvFormula σ φ) z)
                        x)
                      False Not
                      (@Eq.trans.{1} Prop
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (@Finset.erase.{0} HeytingLean.Noneism.Var instDecidableEqNat
                            (@HeytingLean.Noneism.Syntax.fvFormula σ φ) z)
                          x)
                        (And (@Ne.{1} HeytingLean.Noneism.Var x a)
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))
                        False
                        (@Eq.trans.{1} Prop
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (@Finset.erase.{0} HeytingLean.Noneism.Var instDecidableEqNat
                              (@HeytingLean.Noneism.Syntax.fvFormula σ φ) z)
                            x)
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (@Finset.erase.{0} HeytingLean.Noneism.Var instDecidableEqNat
                              (@HeytingLean.Noneism.Syntax.fvFormula σ φ) a)
                            x)
                          (And (@Ne.{1} HeytingLean.Noneism.Var x a)
                            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                              (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))
                          (@congrArg.{1, 1} HeytingLean.Noneism.Var Prop z a
                            (fun (x_1 : HeytingLean.Noneism.Var) =>
                              @Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                (@Finset.erase.{0} HeytingLean.Noneism.Var instDecidableEqNat
                                  (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x_1)
                                x)
                            hza)
                          (@Finset.mem_erase._simp_1.{0} HeytingLean.Noneism.Var instDecidableEqNat x a
                            (@HeytingLean.Noneism.Syntax.fvFormula σ φ)))
                        (@Eq.trans.{1} Prop
                          (And (Not (@Eq.{1} HeytingLean.Noneism.Var x a))
                            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                              (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))
                          (And (Not (@Eq.{1} HeytingLean.Noneism.Var x a)) False) False
                          (@congrArg.{1, 1} Prop Prop
                            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                              (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x)
                            False (And (Not (@Eq.{1} HeytingLean.Noneism.Var x a)))
                            (@eq_false
                              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x)
                              hxFree))
                          (and_false (Not (@Eq.{1} HeytingLean.Noneism.Var x a))))))
                    not_false_eq_true);
              @HeytingLean.Noneism.KripkeFO.forces_substFormula_var_of_not_mem_boundVars_or_not_mem_fvFormula σ W inst D
                M ρ w x a (@HeytingLean.Noneism.Formula.pi σ z φ)
                (@Or.inr
                  (Not
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (@HeytingLean.Noneism.Syntax.boundVars σ (@HeytingLean.Noneism.Formula.pi σ z φ)) a))
                  (Not
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (@HeytingLean.Noneism.Syntax.fvFormula σ (@HeytingLean.Noneism.Formula.pi σ z φ)) x))
                  hxNotPi))
          fun (hza : Not (@Eq.{1} HeytingLean.Noneism.Var z a)) =>
          have haz : @Ne.{1} HeytingLean.Noneism.Var a z := @Ne.symm.{1} HeytingLean.Noneism.Var z a hza;
          have hfvt :
            Not
              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z) :=
            @of_eq_true
              (Not
                (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                  (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                  (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)
                  z))
              (@Eq.trans.{1} Prop
                (Not
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)
                    z))
                (Not False) True
                (@congrArg.{1, 1} Prop Prop
                  (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                    (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                    (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)
                    z)
                  False Not
                  (@Eq.trans.{1} Prop
                    (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                      (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                      (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                        (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) a)
                      z)
                    (@Eq.{1} HeytingLean.Noneism.Var z a) False
                    (@Finset.mem_singleton._simp_1.{0} HeytingLean.Noneism.Var a z)
                    (@eq_false (@Eq.{1} HeytingLean.Noneism.Var z a) hza)))
                not_false_eq_true);
          @Eq.mpr.{0}
            (Iff
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                  (@HeytingLean.Noneism.Formula.pi σ z φ)))
              (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) w
                (@HeytingLean.Noneism.Formula.pi σ z φ)))
            (Iff
              (∀ (v : W),
                @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                  ∀ (d : D),
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) v
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
              (∀ (v : W),
                @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                  ∀ (d : D),
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z d) v
                      φ))
            (@id.{0}
              (@Eq.{1} Prop
                (Iff
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                      (@HeytingLean.Noneism.Formula.pi σ z φ)))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a))
                    w (@HeytingLean.Noneism.Formula.pi σ z φ)))
                (Iff
                  (∀ (v : W),
                    @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                      ∀ (d : D),
                        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d)
                          v (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                  (∀ (v : W),
                    @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                      ∀ (d : D),
                        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z
                            d)
                          v φ)))
              (@congrArg.{1, 1} (HeytingLean.Noneism.Formula σ) Prop
                (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                  (@HeytingLean.Noneism.Formula.pi σ z φ))
                (@HeytingLean.Noneism.Formula.pi σ z
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                (fun (x_1 : HeytingLean.Noneism.Formula σ) =>
                  Iff (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M ρ w x_1)
                    (∀ (v : W),
                      @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                        ∀ (d : D),
                          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                            (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z
                              d)
                            v φ))
                (@Eq.trans.{1} (HeytingLean.Noneism.Formula σ)
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                    (@HeytingLean.Noneism.Formula.pi σ z φ))
                  (@ite.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var z x)
                    (instDecidableEqNat z x) (@HeytingLean.Noneism.Formula.pi σ z φ)
                    (@ite.{1} (HeytingLean.Noneism.Formula σ)
                      (And
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))
                      (@instDecidableAnd
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x)
                        (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat z
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                        (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat x
                          (@HeytingLean.Noneism.Syntax.fvFormula σ φ)))
                      (have avoid : Finset.{0} HeytingLean.Noneism.Var :=
                        @Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                          (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                            (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) z));
                      have z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
                      @HeytingLean.Noneism.Formula.pi σ z'
                        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                          (@HeytingLean.Noneism.Syntax.renameFormula σ z z' φ)))
                      (@HeytingLean.Noneism.Formula.pi σ z
                        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))))
                  (@HeytingLean.Noneism.Formula.pi σ z
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                  (@HeytingLean.Noneism.Syntax.substFormula.eq_10 σ x (HeytingLean.Noneism.Term.var a) z φ)
                  (@Eq.trans.{1} (HeytingLean.Noneism.Formula σ)
                    (@ite.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var z x)
                      (instDecidableEqNat z x) (@HeytingLean.Noneism.Formula.pi σ z φ)
                      (@ite.{1} (HeytingLean.Noneism.Formula σ)
                        (And
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))
                        (@instDecidableAnd
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x)
                          (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat z
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                          (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat x
                            (@HeytingLean.Noneism.Syntax.fvFormula σ φ)))
                        (have avoid : Finset.{0} HeytingLean.Noneism.Var :=
                          @Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                              (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                            (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                              (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) z));
                        have z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
                        @HeytingLean.Noneism.Formula.pi σ z'
                          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                            (@HeytingLean.Noneism.Syntax.renameFormula σ z z' φ)))
                        (@HeytingLean.Noneism.Formula.pi σ z
                          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))))
                    (@ite.{1} (HeytingLean.Noneism.Formula σ)
                      (And
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))
                      (@instDecidableAnd
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x)
                        (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat z
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                        (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat x
                          (@HeytingLean.Noneism.Syntax.fvFormula σ φ)))
                      (have avoid : Finset.{0} HeytingLean.Noneism.Var :=
                        @Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                          (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                            (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) z));
                      have z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
                      @HeytingLean.Noneism.Formula.pi σ z'
                        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                          (@HeytingLean.Noneism.Syntax.renameFormula σ z z' φ)))
                      (@HeytingLean.Noneism.Formula.pi σ z
                        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))
                    (@HeytingLean.Noneism.Formula.pi σ z
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                    (@ite_cond_eq_false.{1} (HeytingLean.Noneism.Formula σ) (@Eq.{1} HeytingLean.Noneism.Var z x)
                      (instDecidableEqNat z x) (@HeytingLean.Noneism.Formula.pi σ z φ)
                      (@ite.{1} (HeytingLean.Noneism.Formula σ)
                        (And
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))
                        (@instDecidableAnd
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x)
                          (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat z
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                          (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat x
                            (@HeytingLean.Noneism.Syntax.fvFormula σ φ)))
                        (have avoid : Finset.{0} HeytingLean.Noneism.Var :=
                          @Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                              (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                            (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                              (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) z));
                        have z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
                        @HeytingLean.Noneism.Formula.pi σ z'
                          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                            (@HeytingLean.Noneism.Syntax.renameFormula σ z z' φ)))
                        (@HeytingLean.Noneism.Formula.pi σ z
                          (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ)))
                      (@eq_false (@Eq.{1} HeytingLean.Noneism.Var z x) hzx))
                    (@ite_cond_eq_false.{1} (HeytingLean.Noneism.Formula σ)
                      (And
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))
                      (@instDecidableAnd
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                        (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                          (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x)
                        (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat z
                          (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                        (@Finset.decidableMem.{0} HeytingLean.Noneism.Var instDecidableEqNat x
                          (@HeytingLean.Noneism.Syntax.fvFormula σ φ)))
                      (have avoid : Finset.{0} HeytingLean.Noneism.Var :=
                        @Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                          (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                          (@Union.union.{0} (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instUnion.{0} HeytingLean.Noneism.Var instDecidableEqNat)
                            (@HeytingLean.Noneism.Syntax.varsFormula σ φ)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)))
                          (@Insert.insert.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instInsert.{0} HeytingLean.Noneism.Var instDecidableEqNat) x
                            (@Singleton.singleton.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instSingleton.{0} HeytingLean.Noneism.Var) z));
                      have z' : HeytingLean.Noneism.Var := HeytingLean.Noneism.Syntax.freshVar avoid;
                      @HeytingLean.Noneism.Formula.pi σ z'
                        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a)
                          (@HeytingLean.Noneism.Syntax.renameFormula σ z z' φ)))
                      (@HeytingLean.Noneism.Formula.pi σ z
                        (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                      (@Eq.trans.{1} Prop
                        (And
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))
                        (And False
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))
                        False
                        (@congrArg.{1, 1} Prop Prop
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                          False
                          (fun (x_1 : Prop) =>
                            And x_1
                              (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                                (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                                (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))
                          (@eq_false
                            (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                              (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                              (HeytingLean.Noneism.Syntax.fvTerm (HeytingLean.Noneism.Term.var a)) z)
                            hfvt))
                        (false_and
                          (@Membership.mem.{0, 0} HeytingLean.Noneism.Var (Finset.{0} HeytingLean.Noneism.Var)
                            (@Finset.instMembership.{0} HeytingLean.Noneism.Var)
                            (@HeytingLean.Noneism.Syntax.fvFormula σ φ) x))))))))
            (@Iff.intro
              (∀ (v : W),
                @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                  ∀ (d : D),
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) v
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
              (∀ (v : W),
                @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                  ∀ (d : D),
                    @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z d) v
                      φ)
              (fun
                  (h :
                    ∀ (v : W),
                      @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                        ∀ (d : D),
                          @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                            (@HeytingLean.Noneism.KripkeFO.update D ρ z d) v
                            (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                  (v : W) (hwv : @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v) (d : D) =>
                have hih :
                  Iff
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) v
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                        (@HeytingLean.Noneism.KripkeFO.update D ρ z d a))
                      v φ) :=
                  ih (@HeytingLean.Noneism.KripkeFO.update D ρ z d) v;
                have hb :
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                      (@HeytingLean.Noneism.KripkeFO.update D ρ z d a))
                    v φ :=
                  @Iff.mp
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) v
                      (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                        (@HeytingLean.Noneism.KripkeFO.update D ρ z d a))
                      v φ)
                    hih (h v hwv d);
                have hza' : @Eq.{1} D (@HeytingLean.Noneism.KripkeFO.update D ρ z d a) (ρ a) :=
                  @of_eq_true
                    (@Eq.{1} D (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z) (instDecidableEqNat a z) d (ρ a))
                      (ρ a))
                    (@Eq.trans.{1} Prop
                      (@Eq.{1} D (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z) (instDecidableEqNat a z) d (ρ a))
                        (ρ a))
                      (@Eq.{1} D (ρ a) (ρ a)) True
                      (@congrArg.{1, 1} D Prop
                        (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z) (instDecidableEqNat a z) d (ρ a)) (ρ a)
                        (fun (x : D) => @Eq.{1} D x (ρ a))
                        (@ite_cond_eq_false.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z) (instDecidableEqNat a z) d (ρ a)
                          (@eq_false (@Eq.{1} HeytingLean.Noneism.Var a z) haz)))
                      (@eq_self.{1} D (ρ a)));
                have hb' :
                  @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ a)) v
                    φ :=
                  @Eq.mp.{0}
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                        (@HeytingLean.Noneism.KripkeFO.update D ρ z d a))
                      v φ)
                    (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                      (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ a)) v
                      φ)
                    (@congrArg.{1, 1} D Prop (@HeytingLean.Noneism.KripkeFO.update D ρ z d a) (ρ a)
                      (fun (x_1 : D) =>
                        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x x_1)
                          v φ)
                      hza')
                    hb;
                have hcomm :
                  @Eq.{1} (HeytingLean.Noneism.KripkeFO.Valuation D)
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ a))
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z d) :=
                  @HeytingLean.Noneism.KripkeFO.update_comm D ρ z x d (ρ a) hzx;
                @Eq.mp.{0}
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ a)) v φ)
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z d) v φ)
                  (@congrArg.{1, 1} (HeytingLean.Noneism.KripkeFO.Valuation D) Prop
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ a))
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z d)
                    (fun (x : HeytingLean.Noneism.KripkeFO.Valuation D) =>
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M x v φ)
                    hcomm)
                  hb')
              fun
                (h :
                  ∀ (v : W),
                    @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v →
                      ∀ (d : D),
                        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z
                            d)
                          v φ)
                (v : W) (hwv : @LE.le.{0} W (@Preorder.toLE.{0} W inst) w v) (d : D) =>
              have hih :
                Iff
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) v
                    (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                      (@HeytingLean.Noneism.KripkeFO.update D ρ z d a))
                    v φ) :=
                ih (@HeytingLean.Noneism.KripkeFO.update D ρ z d) v;
              have hcomm :
                @Eq.{1} (HeytingLean.Noneism.KripkeFO.Valuation D)
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z d)
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ a)) :=
                @Eq.symm.{1} (HeytingLean.Noneism.KripkeFO.Valuation D)
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ a))
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z d)
                  (@HeytingLean.Noneism.KripkeFO.update_comm D ρ z x d (ρ a) hzx);
              have hb :
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ a)) v φ :=
                @Eq.mp.{0}
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z d) v φ)
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ a)) v φ)
                  (@congrArg.{1, 1} (HeytingLean.Noneism.KripkeFO.Valuation D) Prop
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ x (ρ a)) z d)
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ a))
                    (fun (x : HeytingLean.Noneism.KripkeFO.Valuation D) =>
                      @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M x v φ)
                    hcomm)
                  (h v hwv d);
              have hza' : @Eq.{1} D (@HeytingLean.Noneism.KripkeFO.update D ρ z d a) (ρ a) :=
                @of_eq_true
                  (@Eq.{1} D (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z) (instDecidableEqNat a z) d (ρ a)) (ρ a))
                  (@Eq.trans.{1} Prop
                    (@Eq.{1} D (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z) (instDecidableEqNat a z) d (ρ a))
                      (ρ a))
                    (@Eq.{1} D (ρ a) (ρ a)) True
                    (@congrArg.{1, 1} D Prop
                      (@ite.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z) (instDecidableEqNat a z) d (ρ a)) (ρ a)
                      (fun (x : D) => @Eq.{1} D x (ρ a))
                      (@ite_cond_eq_false.{1} D (@Eq.{1} HeytingLean.Noneism.Var a z) (instDecidableEqNat a z) d (ρ a)
                        (@eq_false (@Eq.{1} HeytingLean.Noneism.Var a z) haz)))
                    (@eq_self.{1} D (ρ a)));
              have hb' :
                @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                    (@HeytingLean.Noneism.KripkeFO.update D ρ z d a))
                  v φ :=
                @Eq.mpr.{0}
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                      (@HeytingLean.Noneism.KripkeFO.update D ρ z d a))
                    v φ)
                  (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                    (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ a)) v φ)
                  (@id.{0}
                    (@Eq.{1} Prop
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                          (@HeytingLean.Noneism.KripkeFO.update D ρ z d a))
                        v φ)
                      (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                        (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x (ρ a))
                        v φ))
                    (@congrArg.{1, 1} D Prop (@HeytingLean.Noneism.KripkeFO.update D ρ z d a) (ρ a)
                      (fun (x_1 : D) =>
                        @HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                          (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x x_1)
                          v φ)
                      hza'))
                  hb;
              @Iff.mpr
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M (@HeytingLean.Noneism.KripkeFO.update D ρ z d) v
                  (@HeytingLean.Noneism.Syntax.substFormula σ x (HeytingLean.Noneism.Term.var a) φ))
                (@HeytingLean.Noneism.KripkeFO.Forces W inst σ D M
                  (@HeytingLean.Noneism.KripkeFO.update D (@HeytingLean.Noneism.KripkeFO.update D ρ z d) x
                    (@HeytingLean.Noneism.KripkeFO.update D ρ z d a))
                  v φ)
                hih hb'))
    φ ρ w

set_option linter.unusedVariables true

/-! ## Helper: eigenvariable freshness in contexts -/

namespace NDHelpers

lemma not_mem_fvFormula_of_not_mem_fvContext {σ : Type} {Γ : List (Formula σ)} {a : Var}
    (ha : a ∉ Noneism.ND.fvContext (σ := σ) Γ) :
    ∀ {ψ : Formula σ}, ψ ∈ Γ → a ∉ Syntax.fvFormula (σ := σ) ψ := by
  exact Syntax.not_mem_fvFormula_of_not_mem_fvContext (σ := σ) ha

end NDHelpers

/-! ## Soundness -/

theorem soundness {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (σ := σ) Γ φ → Entails (σ := σ) Γ φ := by
  intro hDer
  induction hDer with
  | hyp hmem =>
      intro W _ D M ρ w hw
      exact hw _ hmem
  | topI =>
      intro W _ D M ρ w _
      simp [Forces]
  | botE h ih =>
      intro W _ D M ρ w hw
      have hbot : Forces M ρ w (.bot : Formula σ) := ih (W := W) (D := D) (M := M) (ρ := ρ) (w := w) hw
      cases (show False from hbot)
  | andI h1 h2 ih1 ih2 =>
      intro W _ D M ρ w hw
      exact And.intro
        (ih1 (W := W) (D := D) (M := M) (ρ := ρ) (w := w) hw)
        (ih2 (W := W) (D := D) (M := M) (ρ := ρ) (w := w) hw)
  | andEL h ih =>
      intro W _ D M ρ w hw
      have : Forces M ρ w (.and _ _ : Formula σ) := ih (W := W) (D := D) (M := M) (ρ := ρ) (w := w) hw
      exact this.1
  | andER h ih =>
      intro W _ D M ρ w hw
      have : Forces M ρ w (.and _ _ : Formula σ) := ih (W := W) (D := D) (M := M) (ρ := ρ) (w := w) hw
      exact this.2
  | orIL h ih =>
      intro W _ D M ρ w hw
      exact Or.inl (ih (W := W) (D := D) (M := M) (ρ := ρ) (w := w) hw)
  | orIR h ih =>
      intro W _ D M ρ w hw
      exact Or.inr (ih (W := W) (D := D) (M := M) (ρ := ρ) (w := w) hw)
  | orE h h1 h2 ih ih1 ih2 =>
      rename_i Γ φ ψ χ
      intro W _ D M ρ w hw
      have : Forces M ρ w (.or _ _ : Formula σ) :=
        ih (W := W) (D := D) (M := M) (ρ := ρ) (w := w) hw
      cases this with
      | inl hφw =>
          have hw' : ∀ θ ∈ (φ :: Γ), Forces M ρ w θ := by
            intro θ hθ
            rcases List.mem_cons.1 hθ with rfl | hθ
            · exact hφw
            · exact hw θ hθ
          exact ih1 (W := W) (D := D) (M := M) (ρ := ρ) (w := w) hw'
      | inr hψw =>
          have hw' : ∀ θ ∈ (ψ :: Γ), Forces M ρ w θ := by
            intro θ hθ
            rcases List.mem_cons.1 hθ with rfl | hθ
            · exact hψw
            · exact hw θ hθ
          exact ih2 (W := W) (D := D) (M := M) (ρ := ρ) (w := w) hw'
  | impI h ih =>
      rename_i Γ φ ψ
      intro W _ D M ρ w hw v hwv hvφ
      have hwvΓ : ∀ θ ∈ Γ, Forces M ρ v θ := by
        intro θ hθ
        exact forces_mono (σ := σ) (M := M) (ρ := ρ) (w := w) (v := v) hwv (φ := θ) (hw θ hθ)
      have hw' : ∀ θ ∈ (φ :: Γ), Forces M ρ v θ := by
        intro θ hθ
        rcases List.mem_cons.1 hθ with rfl | hθ
        · exact hvφ
        · exact hwvΓ θ hθ
      exact ih (W := W) (D := D) (M := M) (ρ := ρ) (w := v) hw'
  | impE h1 h2 ih1 ih2 =>
      rename_i Γ φ ψ
      intro W _ D M ρ w hw
      have himp : Forces M ρ w (.imp φ ψ) := ih1 (W := W) (D := D) (M := M) (ρ := ρ) (w := w) hw
      have hφw : Forces M ρ w φ := ih2 (W := W) (D := D) (M := M) (ρ := ρ) (w := w) hw
      exact himp w le_rfl hφw
  | notI h ih =>
      rename_i Γ φ
      intro W _ D M ρ w hw v hwv hvφ
      have hwvΓ : ∀ θ ∈ Γ, Forces M ρ v θ := by
        intro θ hθ
        exact forces_mono (σ := σ) (M := M) (ρ := ρ) (w := w) (v := v) hwv (φ := θ) (hw θ hθ)
      have hw' : ∀ θ ∈ (φ :: Γ), Forces M ρ v θ := by
        intro θ hθ
        rcases List.mem_cons.1 hθ with rfl | hθ
        · exact hvφ
        · exact hwvΓ θ hθ
      have hbot : Forces M ρ v (.bot : Formula σ) := ih (W := W) (D := D) (M := M) (ρ := ρ) (w := v) hw'
      cases (show False from hbot)
  | notE h1 h2 ih1 ih2 =>
      rename_i Γ φ
      intro W _ D M ρ w hw
      have hnot : Forces M ρ w (.not φ) := ih1 (W := W) (D := D) (M := M) (ρ := ρ) (w := w) hw
      have hφw : Forces M ρ w φ := ih2 (W := W) (D := D) (M := M) (ρ := ρ) (w := w) hw
      exact (hnot w le_rfl hφw).elim
  | wk h hsub ih =>
      intro W _ D M ρ w hw
      exact ih (W := W) (D := D) (M := M) (ρ := ρ) (w := w) (by
        intro θ hθ
        exact hw θ (hsub hθ))
  | piI hΓa haφ hder ih =>
      rename_i Γ x a φ
      -- Show `w ⊩ ∀x φ` by choosing an arbitrary extension world and domain element.
      intro W _ D M ρ w hw v hwv d
      let ρa : Valuation D := update ρ a d
      have hwvΓ : ∀ θ ∈ Γ, Forces M ρ v θ := by
        intro θ hθ
        exact forces_mono (σ := σ) (M := M) (ρ := ρ) (w := w) (v := v) hwv (φ := θ) (hw θ hθ)
      have hwvΓa : ∀ θ ∈ Γ, Forces M ρa v θ := by
        intro θ hθ
        have hnot : a ∉ Syntax.fvFormula (σ := σ) θ :=
          NDHelpers.not_mem_fvFormula_of_not_mem_fvContext (σ := σ) (Γ := Γ) (a := a) hΓa hθ
        exact (forces_update_of_not_mem_fvFormula (σ := σ) (M := M) (ρ := ρ) (y := a) (d := d) θ hnot v).2
          (hwvΓ θ hθ)
      have hSub : Forces M ρa v (Syntax.substFormula (σ := σ) x (.var a) φ) :=
        ih (W := W) (D := D) (M := M) (ρ := ρa) (w := v) hwvΓa
      have hφv : Forces M (update ρa x (ρa a)) v φ :=
        (forces_substFormula_var_of_not_mem_varsFormula (σ := σ) (M := M) (ρ := ρa) (w := v)
            x a φ haφ).1 hSub
      have htmp : Forces M (update (update ρ a d) x d) v φ := by
        simpa [ρa, update_self] using hφv
      by_cases hax : a = x
      · subst hax
        simpa [update_update_same] using htmp
      ·
        have hcomm : update (update ρ a d) x d = update (update ρ x d) a d := by
          simpa using (update_comm (ρ := ρ) (x := a) (y := x) (dx := d) (dy := d) hax)
        have htmp' : Forces M (update (update ρ x d) a d) v φ := by
          simpa [hcomm] using htmp
        exact (forces_update_of_not_mem_varsFormula (σ := σ) (M := M)
          (ρ := update ρ x d) (y := a) (d := d) (w := v) φ haφ).1 htmp'
  | piE hpi ih =>
      rename_i Γ x a φ
      intro W _ D M ρ w hw
      have hForall : Forces M ρ w (.pi x φ) :=
        ih (W := W) (D := D) (M := M) (ρ := ρ) (w := w) hw
      have hφw : Forces M (update ρ x (ρ a)) w φ := hForall w le_rfl (ρ a)
      exact (HeytingLean.Noneism.KripkeFO.forces_substFormula_var (σ := σ) (M := M) (ρ := ρ) (w := w)
        x a φ).2 hφw
  | sigmaI hder ih =>
      rename_i Γ x a φ
      intro W _ D M ρ w hw
      have hSub : Forces M ρ w (Syntax.substFormula (σ := σ) x (.var a) φ) :=
        ih (W := W) (D := D) (M := M) (ρ := ρ) (w := w) hw
      have hφw : Forces M (update ρ x (ρ a)) w φ :=
        (HeytingLean.Noneism.KripkeFO.forces_substFormula_var (σ := σ) (M := M) (ρ := ρ) (w := w)
          x a φ).1 hSub
      exact ⟨ρ a, hφw⟩
  | sigmaE hs hΓa haφ haχ hder ihs ihder =>
      rename_i Γ x a φ χ
      intro W _ D M ρ w hw
      have hSig : Forces M ρ w (.sigma x φ) :=
        ihs (W := W) (D := D) (M := M) (ρ := ρ) (w := w) hw
      rcases hSig with ⟨d, hφw⟩
      let ρa : Valuation D := update ρ a d
      have hwΓa : ∀ θ ∈ Γ, Forces M ρa w θ := by
        intro θ hθ
        have hnot : a ∉ Syntax.fvFormula (σ := σ) θ :=
          NDHelpers.not_mem_fvFormula_of_not_mem_fvContext (σ := σ) (Γ := Γ) (a := a) hΓa hθ
        exact (forces_update_of_not_mem_fvFormula (σ := σ) (M := M) (ρ := ρ) (y := a) (d := d) θ hnot w).2
          (hw θ hθ)
      have hAssm : Forces M ρa w (Syntax.substFormula (σ := σ) x (.var a) φ) := by
        -- Build `w ⊩ φ[d/x]` in a valuation that also maps the eigenvariable `a ↦ d`.
        have hφ' : Forces M (update ρa x (ρa a)) w φ := by
          by_cases hax : a = x
          · subst hax
            -- `ρa = update ρ x d`, so updating at `x` again is a no-op.
            simpa [ρa, update_update_same, update_self] using hφw
          ·
            -- Add an irrelevant `a`-update (since `a ∉ varsFormula φ`), then commute updates.
            have htmp : Forces M (update (update ρ x d) a d) w φ :=
              (forces_update_of_not_mem_varsFormula (σ := σ) (M := M)
                (ρ := update ρ x d) (y := a) (d := d) (w := w) φ haφ).2 hφw
            have hcomm : update (update ρ x d) a d = update (update ρ a d) x d := by
              simpa using (update_comm (ρ := ρ) (x := x) (y := a) (dx := d) (dy := d) (Ne.symm hax))
            have : Forces M (update (update ρ a d) x d) w φ := by
              simpa [hcomm] using htmp
            simpa [ρa, update_self] using this
        exact (forces_substFormula_var_of_not_mem_varsFormula (σ := σ) (M := M) (ρ := ρa) (w := w)
          x a φ haφ).2 hφ'
      have hwCtx : ∀ θ ∈ (Syntax.substFormula (σ := σ) x (.var a) φ :: Γ), Forces M ρa w θ := by
        intro θ hθ
        rcases List.mem_cons.1 hθ with rfl | hθ
        · exact hAssm
        · exact hwΓa θ hθ
      have hχa : Forces M ρa w χ :=
        ihder (W := W) (D := D) (M := M) (ρ := ρa) (w := w) hwCtx
      exact (forces_update_of_not_mem_fvFormula (σ := σ) (M := M) (ρ := ρ) (y := a) (d := d) χ haχ w).1 hχa

end KripkeFO

end Noneism
end HeytingLean
