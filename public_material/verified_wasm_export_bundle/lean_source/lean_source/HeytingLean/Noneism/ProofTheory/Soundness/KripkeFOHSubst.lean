import HeytingLean.Noneism.ProofTheory.Soundness.KripkeFOH

namespace HeytingLean
namespace Noneism
namespace KripkeFOH

open Syntax.Henkin

variable {W : Type} [Preorder W]
variable {σ κ D : Type}

/-!
Additional semantic lemmas for Henkin forcing used by the completeness layer:

* update-irrelevance when a variable does not occur in a formula,
* semantic renaming (alpha) lemma,
* semantic substitution lemma for general Henkin capture-avoiding substitution.
-/

/--
If `x` does not occur anywhere in `φ` (free or bound), updating the valuation at `x` does not
affect forcing.
-/
theorem forces_update_of_not_mem_varsFormula
    (M : Model W σ D) (ρ : Valuation D) (η : ParamInterp κ D) (w : W)
    (x : Var) (d : D) :
    ∀ φ : FormulaH σ κ,
      x ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) φ →
        (Forces M (HeytingLean.Noneism.KripkeFO.update ρ x d) η w φ ↔ Forces M ρ η w φ) := by
  intro φ hx
  induction φ generalizing ρ w with
  | top =>
      simp [Forces]
  | bot =>
      simp [Forces]
  | pred p args =>
      have hEval :
          List.map (evalTerm (HeytingLean.Noneism.KripkeFO.update ρ x d) η) args =
            List.map (evalTerm ρ η) args := by
        apply List.map_congr_left
        intro t ht
        cases t with
        | var z =>
            by_cases hzx : z = x
            ·
              have hxContra : x ∈ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) (.pred p args) := by
                have hzIn : z ∈ Syntax.Henkin.fvTerms (κ := κ) args := by
                  clear hx
                  revert ht
                  induction args with
                  | nil =>
                      intro ht
                      cases ht
                  | cons t ts ih =>
                      intro ht
                      simp [Syntax.Henkin.fvTerms_cons, Finset.mem_union] at ht ⊢
                      rcases ht with rfl | ht'
                      · simp [Syntax.Henkin.fvTerm]
                      · exact Or.inr (ih ht')
                have : x ∈ Syntax.Henkin.fvTerms (κ := κ) args := by
                  simpa [hzx] using hzIn
                simpa [Syntax.Henkin.varsFormula] using this
              exact False.elim (hx hxContra)
            · simp [evalTerm, HeytingLean.Noneism.KripkeFO.update, hzx]
        | param k =>
            simp [evalTerm]
      simp [Forces, hEval]
  | eExists t =>
      cases t with
      | var z =>
          by_cases hzx : z = x
          ·
            have hxContra :
                x ∈ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) (.eExists (.var z) : FormulaH σ κ) := by
              simp [hzx, Syntax.Henkin.varsFormula, Syntax.Henkin.fvTerm]
            exact False.elim (hx hxContra)
          · simp [Forces, evalTerm, HeytingLean.Noneism.KripkeFO.update, hzx]
      | param k =>
          simp [Forces, evalTerm]
  | not φ ih =>
      have hxφ : x ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) φ := by
        simpa [Syntax.Henkin.varsFormula] using hx
      constructor
      · intro h v hwv hφ
        have : Forces M (HeytingLean.Noneism.KripkeFO.update ρ x d) η v φ :=
          (ih (ρ := ρ) (w := v) hxφ).2 hφ
        exact h v hwv this
      · intro h v hwv hφ
        have : Forces M ρ η v φ := (ih (ρ := ρ) (w := v) hxφ).1 hφ
        exact h v hwv this
  | and φ ψ ihφ ihψ =>
      have hx' :
          x ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) φ ∧
            x ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) ψ := by
        simpa [Syntax.Henkin.varsFormula, Finset.mem_union] using hx
      simp [Forces, (ihφ (ρ := ρ) (w := w) hx'.1), (ihψ (ρ := ρ) (w := w) hx'.2)]
  | or φ ψ ihφ ihψ =>
      have hx' :
          x ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) φ ∧
            x ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) ψ := by
        simpa [Syntax.Henkin.varsFormula, Finset.mem_union] using hx
      simp [Forces, (ihφ (ρ := ρ) (w := w) hx'.1), (ihψ (ρ := ρ) (w := w) hx'.2)]
  | imp φ ψ ihφ ihψ =>
      have hx' :
          x ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) φ ∧
            x ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) ψ := by
        simpa [Syntax.Henkin.varsFormula, Finset.mem_union] using hx
      constructor
      · intro h v hwv hφ
        have hφ' : Forces M (HeytingLean.Noneism.KripkeFO.update ρ x d) η v φ :=
          (ihφ (ρ := ρ) (w := v) hx'.1).2 hφ
        have hψ' : Forces M (HeytingLean.Noneism.KripkeFO.update ρ x d) η v ψ := h v hwv hφ'
        exact (ihψ (ρ := ρ) (w := v) hx'.2).1 hψ'
      · intro h v hwv hφ
        have hφ' : Forces M ρ η v φ := (ihφ (ρ := ρ) (w := v) hx'.1).1 hφ
        have hψ' : Forces M ρ η v ψ := h v hwv hφ'
        exact (ihψ (ρ := ρ) (w := v) hx'.2).2 hψ'
  | sigma z φ ih =>
      have hx' : x ≠ z ∧ x ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) φ := by
        simpa [Syntax.Henkin.varsFormula, Finset.mem_insert, Finset.mem_union] using hx
      have hxz : x ≠ z := hx'.1
      have hxφ : x ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) φ := hx'.2
      constructor
      · rintro ⟨d', hd'⟩
        refine ⟨d', ?_⟩
        have hcomm :
            HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x d) z d' =
              HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d') x d := by
          simpa using
            (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := x) (y := z)
              (dx := d) (dy := d') hxz)
        have : Forces M (HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d') x d) η w φ := by
          simpa [hcomm] using hd'
        exact (ih (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d') (w := w) hxφ).1 this
      · rintro ⟨d', hd'⟩
        refine ⟨d', ?_⟩
        have hcomm :
            HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x d) z d' =
              HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d') x d := by
          simpa using
            (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := x) (y := z)
              (dx := d) (dy := d') hxz)
        have : Forces M (HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d') x d) η w φ :=
          (ih (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d') (w := w) hxφ).2 hd'
        simpa [hcomm] using this
  | pi z φ ih =>
      have hx' : x ≠ z ∧ x ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) φ := by
        simpa [Syntax.Henkin.varsFormula, Finset.mem_insert, Finset.mem_union] using hx
      have hxz : x ≠ z := hx'.1
      have hxφ : x ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) φ := hx'.2
      constructor
      · intro h v hwv d'
        have hcomm :
            HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x d) z d' =
              HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d') x d := by
          simpa using
            (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := x) (y := z)
              (dx := d) (dy := d') hxz)
        have : Forces M (HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d') x d) η v φ := by
          simpa [hcomm] using h v hwv d'
        exact (ih (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d') (w := v) hxφ).1 this
      · intro h v hwv d'
        have hcomm :
            HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x d) z d' =
              HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d') x d := by
          simpa using
            (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := x) (y := z)
              (dx := d) (dy := d') hxz)
        have : Forces M (HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d') x d) η v φ :=
          (ih (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d') (w := v) hxφ).2 (h v hwv d')
        simpa [hcomm] using this

/--
Semantic renaming lemma: if the target variable `y` does not occur in `φ`, forcing of
`renameFormula x y φ` under `ρ` matches forcing of `φ` under `ρ[x := ρ y]`.
-/
theorem forces_renameFormula_of_not_mem_varsFormula
    (M : Model W σ D) (ρ : Valuation D) (η : ParamInterp κ D) (w : W)
    (x y : Var) :
    ∀ φ : FormulaH σ κ,
      y ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) φ →
        (Forces M ρ η w (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) x y φ) ↔
          Forces M (HeytingLean.Noneism.KripkeFO.update ρ x (ρ y)) η w φ) := by
  intro φ hy
  induction φ generalizing ρ w with
  | top =>
      simp [Syntax.Henkin.renameFormula, Forces]
  | bot =>
      simp [Syntax.Henkin.renameFormula, Forces]
  | pred p args =>
      have hMap :
          List.map (evalTerm ρ η ∘ Syntax.Henkin.renameTerm (κ := κ) x y) args =
            List.map (evalTerm (HeytingLean.Noneism.KripkeFO.update ρ x (ρ y)) η) args := by
        apply List.map_congr_left
        intro t _ht
        cases t with
        | var z =>
            by_cases hzx : z = x <;>
              simp [Syntax.Henkin.renameTerm, evalTerm, HeytingLean.Noneism.KripkeFO.update, hzx]
        | param k =>
            simp [Syntax.Henkin.renameTerm, evalTerm]
      simp [Syntax.Henkin.renameFormula, Syntax.Henkin.renameTerms, Forces, List.map_map, hMap]
  | eExists t =>
      cases t with
      | var z =>
          by_cases hzx : z = x <;>
            simp [Syntax.Henkin.renameFormula, Syntax.Henkin.renameTerm, Forces, evalTerm,
              HeytingLean.Noneism.KripkeFO.update, hzx]
      | param k =>
          simp [Syntax.Henkin.renameFormula, Syntax.Henkin.renameTerm, Forces, evalTerm]
  | not φ ih =>
      have hyφ : y ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) φ := by
        simpa [Syntax.Henkin.varsFormula] using hy
      constructor
      · intro h v hwv hv
        have : Forces M ρ η v (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) x y φ) :=
          (ih (ρ := ρ) (w := v) hyφ).2 hv
        exact h v hwv this
      · intro h v hwv hv
        have : Forces M (HeytingLean.Noneism.KripkeFO.update ρ x (ρ y)) η v φ :=
          (ih (ρ := ρ) (w := v) hyφ).1 hv
        exact h v hwv this
  | and φ ψ ihφ ihψ =>
      have hy' :
          y ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) φ ∧
            y ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) ψ := by
        simpa [Syntax.Henkin.varsFormula, Finset.mem_union] using hy
      simp [Syntax.Henkin.renameFormula, Forces,
        ihφ (ρ := ρ) (w := w) hy'.1,
        ihψ (ρ := ρ) (w := w) hy'.2]
  | or φ ψ ihφ ihψ =>
      have hy' :
          y ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) φ ∧
            y ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) ψ := by
        simpa [Syntax.Henkin.varsFormula, Finset.mem_union] using hy
      simp [Syntax.Henkin.renameFormula, Forces,
        ihφ (ρ := ρ) (w := w) hy'.1,
        ihψ (ρ := ρ) (w := w) hy'.2]
  | imp φ ψ ihφ ihψ =>
      have hy' :
          y ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) φ ∧
            y ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) ψ := by
        simpa [Syntax.Henkin.varsFormula, Finset.mem_union] using hy
      constructor
      · intro h v hwv hv
        have : Forces M ρ η v (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) x y φ) :=
          (ihφ (ρ := ρ) (w := v) hy'.1).2 hv
        exact (ihψ (ρ := ρ) (w := v) hy'.2).1 (h v hwv this)
      · intro h v hwv hv
        have : Forces M (HeytingLean.Noneism.KripkeFO.update ρ x (ρ y)) η v φ :=
          (ihφ (ρ := ρ) (w := v) hy'.1).1 hv
        exact (ihψ (ρ := ρ) (w := v) hy'.2).2 (h v hwv this)
  | sigma z φ ih =>
      have hy' : y ≠ z ∧ y ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) φ := by
        simpa [Syntax.Henkin.varsFormula, Finset.mem_insert, Finset.mem_union] using hy
      have hyz : y ≠ z := hy'.1
      have hyφ : y ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) φ := hy'.2
      by_cases hzx : z = x
      ·
        have hyx : y ≠ x := by
          simpa [hzx] using hyz
        constructor
        · intro h
          rcases (by simpa [Syntax.Henkin.renameFormula, Forces, hzx] using h) with ⟨d', hd'⟩
          have hd'' :
              Forces M
                (HeytingLean.Noneism.KripkeFO.update
                  (HeytingLean.Noneism.KripkeFO.update ρ y d') x d')
                η w φ := by
            have := (ih (ρ := HeytingLean.Noneism.KripkeFO.update ρ y d') (w := w) hyφ).1 hd'
            simpa [HeytingLean.Noneism.KripkeFO.update, hyz] using this
          have hcomm :
              HeytingLean.Noneism.KripkeFO.update
                  (HeytingLean.Noneism.KripkeFO.update ρ y d') x d' =
                HeytingLean.Noneism.KripkeFO.update
                  (HeytingLean.Noneism.KripkeFO.update ρ x d') y d' := by
            simpa using
              (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := y) (y := x) (dx := d') (dy := d') hyx)
          have hd''' :
              Forces M (HeytingLean.Noneism.KripkeFO.update ρ x d') η w φ := by
            have := (forces_update_of_not_mem_varsFormula (σ := σ) (κ := κ)
              (M := M) (ρ := HeytingLean.Noneism.KripkeFO.update ρ x d') (η := η) (w := w)
              (x := y) (d := d') φ hyφ).1 (by simpa [hcomm] using hd'')
            simpa using this
          -- pack the witness into forcing of the RHS sigma (binder `x`)
          simpa [Forces, hzx, HeytingLean.Noneism.KripkeFO.update_update_same] using (show ∃ d : D,
            Forces M (HeytingLean.Noneism.KripkeFO.update ρ x d) η w φ from ⟨d', hd'''⟩)
        · intro h
          rcases (by simpa [Forces, hzx, HeytingLean.Noneism.KripkeFO.update_update_same] using h) with ⟨d', hd'⟩
          have hdExt :
              Forces M (HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x d') y d') η w φ :=
            (forces_update_of_not_mem_varsFormula (σ := σ) (κ := κ)
              (M := M) (ρ := HeytingLean.Noneism.KripkeFO.update ρ x d') (η := η) (w := w)
              (x := y) (d := d') φ hyφ).2 hd'
          have hcomm :
              HeytingLean.Noneism.KripkeFO.update
                  (HeytingLean.Noneism.KripkeFO.update ρ x d') y d' =
                HeytingLean.Noneism.KripkeFO.update
                  (HeytingLean.Noneism.KripkeFO.update ρ y d') x d' := by
            simpa using
              (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := y) (y := x) (dx := d') (dy := d') hyx).symm
          have hd'' :
              Forces M (HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ y d') x d') η w φ := by
            simpa [hcomm] using hdExt
          have hdRen :
              Forces M (HeytingLean.Noneism.KripkeFO.update ρ y d') η w
                (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) x y φ) :=
            (ih (ρ := HeytingLean.Noneism.KripkeFO.update ρ y d') (w := w) hyφ).2 (by
              simpa [HeytingLean.Noneism.KripkeFO.update, hyz] using hd'')
          simpa [Syntax.Henkin.renameFormula, Forces, hzx] using (show ∃ d : D,
            Forces M (HeytingLean.Noneism.KripkeFO.update ρ y d) η w
              (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) x y φ) from ⟨d', hdRen⟩)
      ·
        constructor
        · intro h
          rcases (by simpa [Syntax.Henkin.renameFormula, Forces, hzx] using h) with ⟨d', hd'⟩
          have hd'' :
              Forces M
                (HeytingLean.Noneism.KripkeFO.update
                  (HeytingLean.Noneism.KripkeFO.update ρ z d') x (ρ y))
                η w φ := by
            have := (ih (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d') (w := w) hyφ).1 hd'
            have hyVal : HeytingLean.Noneism.KripkeFO.update ρ z d' y = ρ y := by
              simp [HeytingLean.Noneism.KripkeFO.update, hyz]
            simpa [hyVal] using this
          have hcomm :
              HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d') x (ρ y) =
                HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (ρ y)) z d' := by
            simpa using
              (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := z) (y := x) (dx := d') (dy := ρ y) hzx)
          have : Forces M (HeytingLean.Noneism.KripkeFO.update ρ x (ρ y)) η w (.sigma z φ) := by
            refine ⟨d', ?_⟩
            simpa [hcomm] using hd''
          exact this
        · intro h
          rcases (by simpa [Forces] using h) with ⟨d', hd'⟩
          have hcomm :
              HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (ρ y)) z d' =
                HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d') x (ρ y) := by
            simpa using
              (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := z) (y := x) (dx := d') (dy := ρ y) hzx).symm
          have hd'' :
              Forces M (HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d') x (ρ y)) η w φ := by
            simpa [hcomm] using hd'
          have hyVal : HeytingLean.Noneism.KripkeFO.update ρ z d' y = ρ y := by
            simp [HeytingLean.Noneism.KripkeFO.update, hyz]
          have hdRen :
              Forces M (HeytingLean.Noneism.KripkeFO.update ρ z d') η w
                (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) x y φ) :=
            (ih (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d') (w := w) hyφ).2 (by
              simpa [hyVal] using hd'')
          simpa [Syntax.Henkin.renameFormula, Forces, hzx] using (show ∃ d : D,
            Forces M (HeytingLean.Noneism.KripkeFO.update ρ z d) η w
              (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) x y φ) from ⟨d', hdRen⟩)
  | pi z φ ih =>
      have hy' : y ≠ z ∧ y ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) φ := by
        simpa [Syntax.Henkin.varsFormula, Finset.mem_insert, Finset.mem_union] using hy
      have hyz : y ≠ z := hy'.1
      have hyφ : y ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) φ := hy'.2
      by_cases hzx : z = x
      ·
        have hyx : y ≠ x := by
          simpa [hzx] using hyz
        constructor
        · intro h v hwv d'
          have hFor :
              ∀ v, w ≤ v → ∀ d : D,
                Forces M (HeytingLean.Noneism.KripkeFO.update ρ y d) η v
                  (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) x y φ) := by
            simpa [Syntax.Henkin.renameFormula, Forces, hzx] using h
          have hdRen := hFor v hwv d'
          have hd'' :
              Forces M
                (HeytingLean.Noneism.KripkeFO.update
                  (HeytingLean.Noneism.KripkeFO.update ρ y d') x d')
                η v φ := by
            have := (ih (ρ := HeytingLean.Noneism.KripkeFO.update ρ y d') (w := v) hyφ).1 hdRen
            simpa [HeytingLean.Noneism.KripkeFO.update, hyz] using this
          have hcomm :
              HeytingLean.Noneism.KripkeFO.update
                  (HeytingLean.Noneism.KripkeFO.update ρ y d') x d' =
                HeytingLean.Noneism.KripkeFO.update
                  (HeytingLean.Noneism.KripkeFO.update ρ x d') y d' := by
            simpa using
              (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := y) (y := x) (dx := d') (dy := d') hyx)
          have hd''' :
              Forces M (HeytingLean.Noneism.KripkeFO.update ρ x d') η v φ := by
            have := (forces_update_of_not_mem_varsFormula (σ := σ) (κ := κ)
              (M := M) (ρ := HeytingLean.Noneism.KripkeFO.update ρ x d') (η := η) (w := v)
              (x := y) (d := d') φ hyφ).1 (by simpa [hcomm] using hd'')
            simpa using this
          simpa [Forces, hzx, HeytingLean.Noneism.KripkeFO.update_update_same] using hd'''
        · intro h
          have hFor :
              ∀ v, w ≤ v → ∀ d : D, Forces M (HeytingLean.Noneism.KripkeFO.update ρ x d) η v φ := by
            simpa [Forces, hzx, HeytingLean.Noneism.KripkeFO.update_update_same] using h
          have : Forces M ρ η w (.pi y (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) x y φ)) := by
            intro v hwv d'
            have hd' : Forces M (HeytingLean.Noneism.KripkeFO.update ρ x d') η v φ := hFor v hwv d'
            have hdExt :
                Forces M (HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x d') y d') η v φ :=
              (forces_update_of_not_mem_varsFormula (σ := σ) (κ := κ)
                (M := M) (ρ := HeytingLean.Noneism.KripkeFO.update ρ x d') (η := η) (w := v)
                (x := y) (d := d') φ hyφ).2 hd'
            have hcomm :
                HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x d') y d' =
                  HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ y d') x d' := by
              simpa using
                (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := y) (y := x) (dx := d') (dy := d') hyx).symm
            have hd'' :
                Forces M (HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ y d') x d') η v φ := by
              simpa [hcomm] using hdExt
            exact (ih (ρ := HeytingLean.Noneism.KripkeFO.update ρ y d') (w := v) hyφ).2 (by
              simpa [HeytingLean.Noneism.KripkeFO.update, hyz] using hd'')
          simpa [Syntax.Henkin.renameFormula, Forces, hzx] using this
      ·
        have hzx' : z ≠ x := hzx
        constructor
        · intro h
          have hFor :
              ∀ v, w ≤ v → ∀ d : D,
                Forces M (HeytingLean.Noneism.KripkeFO.update ρ z d) η v
                  (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) x y φ) := by
            simpa [Syntax.Henkin.renameFormula, Forces, hzx'] using h
          intro v hwv d'
          have hdRen :
              Forces M (HeytingLean.Noneism.KripkeFO.update ρ z d') η v
                (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) x y φ) :=
            hFor v hwv d'
          have hd'' :
              Forces M
                (HeytingLean.Noneism.KripkeFO.update
                  (HeytingLean.Noneism.KripkeFO.update ρ z d') x
                  (HeytingLean.Noneism.KripkeFO.update ρ z d' y))
                η v φ :=
            (ih (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d') (w := v) hyφ).1 hdRen
          have hyVal : HeytingLean.Noneism.KripkeFO.update ρ z d' y = ρ y := by
            simp [HeytingLean.Noneism.KripkeFO.update, hyz]
          have hd'' :
              Forces M
                (HeytingLean.Noneism.KripkeFO.update
                  (HeytingLean.Noneism.KripkeFO.update ρ z d') x (ρ y))
                η v φ := by
            simpa [hyVal] using hd''
          have hcomm :
              HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d') x (ρ y) =
                HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (ρ y)) z d' := by
            simpa using
              (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := z) (y := x)
                (dx := d') (dy := ρ y) hzx')
          simpa [Forces, hcomm] using hd''
        · intro h
          have hFor :
              ∀ v, w ≤ v → ∀ d : D,
                Forces M
                  (HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (ρ y)) z d) η v φ := by
            simpa [Forces] using h
          have : Forces M ρ η w (.pi z (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) x y φ)) := by
            intro v hwv d'
            have hd :
                Forces M
                  (HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (ρ y)) z d')
                  η v φ :=
              hFor v hwv d'
            have hcomm :
                HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (ρ y)) z d' =
                  HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d') x (ρ y) := by
              simpa using
                (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := z) (y := x)
                  (dx := d') (dy := ρ y) hzx').symm
            have hd'' :
                Forces M (HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d') x (ρ y)) η v φ := by
              simpa [hcomm] using hd
            have hyVal : HeytingLean.Noneism.KripkeFO.update ρ z d' y = ρ y := by
              simp [HeytingLean.Noneism.KripkeFO.update, hyz]
            have hd'' :
                Forces M
                  (HeytingLean.Noneism.KripkeFO.update
                    (HeytingLean.Noneism.KripkeFO.update ρ z d') x
                    (HeytingLean.Noneism.KripkeFO.update ρ z d' y))
                  η v φ := by
              simpa [hyVal] using hd''
            exact (ih (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d') (w := v) hyφ).2 hd''
          simpa [Syntax.Henkin.renameFormula, Forces, hzx'] using this

/--
If `x` is not free in `φ`, updating the valuation at `x` does not affect forcing.
-/
theorem forces_update_of_not_mem_fvFormula
    (M : Model W σ D) (ρ : Valuation D) (η : ParamInterp κ D) (w : W)
    (x : Var) (d : D) :
    ∀ φ : FormulaH σ κ,
      x ∉ Syntax.Henkin.fvFormula (σ := σ) (κ := κ) φ →
        (Forces M (HeytingLean.Noneism.KripkeFO.update ρ x d) η w φ ↔ Forces M ρ η w φ) := by
  intro φ hx
  induction φ generalizing ρ w with
  | top =>
      simp [Forces]
  | bot =>
      simp [Forces]
  | pred p args =>
      have hEval :
          List.map (evalTerm (HeytingLean.Noneism.KripkeFO.update ρ x d) η) args =
            List.map (evalTerm ρ η) args := by
        apply List.map_congr_left
        intro t ht
        cases t with
        | var z =>
            by_cases hzx : z = x
            ·
              have hxContra : x ∈ Syntax.Henkin.fvFormula (σ := σ) (κ := κ) (.pred p args) := by
                have hzIn : z ∈ Syntax.Henkin.fvTerms (κ := κ) args := by
                  clear hx
                  revert ht
                  induction args with
                  | nil =>
                      intro ht
                      cases ht
                  | cons t ts ih =>
                      intro ht
                      simp [Syntax.Henkin.fvTerms_cons, Finset.mem_union] at ht ⊢
                      rcases ht with rfl | ht'
                      · simp [Syntax.Henkin.fvTerm]
                      · exact Or.inr (ih ht')
                have : x ∈ Syntax.Henkin.fvTerms (κ := κ) args := by
                  simpa [hzx] using hzIn
                simpa [Syntax.Henkin.fvFormula] using this
              exact False.elim (hx hxContra)
            · simp [evalTerm, HeytingLean.Noneism.KripkeFO.update, hzx]
        | param k =>
            simp [evalTerm]
      simp [Forces, hEval]
  | eExists t =>
      cases t with
      | var z =>
          by_cases hzx : z = x
          ·
            have hxContra :
                x ∈ Syntax.Henkin.fvFormula (σ := σ) (κ := κ) (.eExists (.var z) : FormulaH σ κ) := by
              simp [hzx, Syntax.Henkin.fvFormula, Syntax.Henkin.fvTerm]
            exact False.elim (hx hxContra)
          · simp [Forces, evalTerm, HeytingLean.Noneism.KripkeFO.update, hzx]
      | param k =>
          simp [Forces, evalTerm]
  | not φ ih =>
      have hxφ : x ∉ Syntax.Henkin.fvFormula (σ := σ) (κ := κ) φ := by
        simpa [Syntax.Henkin.fvFormula] using hx
      constructor
      · intro h v hwv hφ
        have : Forces M (HeytingLean.Noneism.KripkeFO.update ρ x d) η v φ :=
          (ih (ρ := ρ) (w := v) hxφ).2 hφ
        exact h v hwv this
      · intro h v hwv hφ
        have : Forces M ρ η v φ := (ih (ρ := ρ) (w := v) hxφ).1 hφ
        exact h v hwv this
  | and φ ψ ihφ ihψ =>
      have hx' :
          x ∉ Syntax.Henkin.fvFormula (σ := σ) (κ := κ) φ ∧
            x ∉ Syntax.Henkin.fvFormula (σ := σ) (κ := κ) ψ := by
        simpa [Syntax.Henkin.fvFormula, Finset.mem_union] using hx
      simp [Forces, (ihφ (ρ := ρ) (w := w) hx'.1), (ihψ (ρ := ρ) (w := w) hx'.2)]
  | or φ ψ ihφ ihψ =>
      have hx' :
          x ∉ Syntax.Henkin.fvFormula (σ := σ) (κ := κ) φ ∧
            x ∉ Syntax.Henkin.fvFormula (σ := σ) (κ := κ) ψ := by
        simpa [Syntax.Henkin.fvFormula, Finset.mem_union] using hx
      simp [Forces, (ihφ (ρ := ρ) (w := w) hx'.1), (ihψ (ρ := ρ) (w := w) hx'.2)]
  | imp φ ψ ihφ ihψ =>
      have hx' :
          x ∉ Syntax.Henkin.fvFormula (σ := σ) (κ := κ) φ ∧
            x ∉ Syntax.Henkin.fvFormula (σ := σ) (κ := κ) ψ := by
        simpa [Syntax.Henkin.fvFormula, Finset.mem_union] using hx
      constructor
      · intro h v hwv hφ
        have hφ' : Forces M (HeytingLean.Noneism.KripkeFO.update ρ x d) η v φ :=
          (ihφ (ρ := ρ) (w := v) hx'.1).2 hφ
        have hψ' : Forces M (HeytingLean.Noneism.KripkeFO.update ρ x d) η v ψ := h v hwv hφ'
        exact (ihψ (ρ := ρ) (w := v) hx'.2).1 hψ'
      · intro h v hwv hφ
        have hφ' : Forces M ρ η v φ := (ihφ (ρ := ρ) (w := v) hx'.1).1 hφ
        have hψ' : Forces M ρ η v ψ := h v hwv hφ'
        exact (ihψ (ρ := ρ) (w := v) hx'.2).2 hψ'
  | sigma z φ ih =>
      have hxErase : x ∉ (Syntax.Henkin.fvFormula (σ := σ) (κ := κ) φ).erase z := by
        simpa [Syntax.Henkin.fvFormula] using hx
      by_cases hxz : x = z
      · subst hxz
        simp [Forces, HeytingLean.Noneism.KripkeFO.update_update_same]
      ·
        have hxφ : x ∉ Syntax.Henkin.fvFormula (σ := σ) (κ := κ) φ := by
          intro hxφ
          exact hxErase (by simpa [Finset.mem_erase, hxz] using hxφ)
        constructor
        · rintro ⟨d', hd'⟩
          refine ⟨d', ?_⟩
          have hcomm :
              HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x d) z d' =
                HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d') x d := by
            simpa using
              (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := x) (y := z) (dx := d) (dy := d') hxz)
          have : Forces M (HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d') x d) η w φ := by
            simpa [hcomm] using hd'
          exact (ih (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d') (w := w) hxφ).1 this
        · rintro ⟨d', hd'⟩
          refine ⟨d', ?_⟩
          have hcomm :
              HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x d) z d' =
                HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d') x d := by
            simpa using
              (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := x) (y := z) (dx := d) (dy := d') hxz)
          have : Forces M (HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d') x d) η w φ :=
            (ih (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d') (w := w) hxφ).2 hd'
          simpa [hcomm] using this
  | pi z φ ih =>
      have hxErase : x ∉ (Syntax.Henkin.fvFormula (σ := σ) (κ := κ) φ).erase z := by
        simpa [Syntax.Henkin.fvFormula] using hx
      by_cases hxz : x = z
      · subst hxz
        constructor
        · intro h v hwv d'
          have := h v hwv d'
          simpa [Forces, HeytingLean.Noneism.KripkeFO.update_update_same] using this
        · intro h v hwv d'
          have := h v hwv d'
          simpa [Forces, HeytingLean.Noneism.KripkeFO.update_update_same] using this
      ·
        have hxφ : x ∉ Syntax.Henkin.fvFormula (σ := σ) (κ := κ) φ := by
          intro hxφ
          exact hxErase (by simpa [Finset.mem_erase, hxz] using hxφ)
        constructor
        · intro h v hwv d'
          have hcomm :
              HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x d) z d' =
                HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d') x d := by
            simpa using
              (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := x) (y := z) (dx := d) (dy := d') hxz)
          have : Forces M (HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d') x d) η v φ := by
            simpa [hcomm] using h v hwv d'
          exact (ih (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d') (w := v) hxφ).1 this
        · intro h v hwv d'
          have hcomm :
              HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x d) z d' =
                HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d') x d := by
            simpa using
              (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := x) (y := z) (dx := d) (dy := d') hxz)
          have : Forces M (HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d') x d) η v φ :=
            (ih (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d') (w := v) hxφ).2 (h v hwv d')
          simpa [hcomm] using this

/--
Semantic substitution lemma for Henkin forcing: forcing of the capture-avoiding substitution
instance `φ[t/x]` under `ρ` matches forcing of `φ` under the updated valuation `ρ[x := ⟦t⟧]`.
-/
theorem forces_substFormula
    (M : Model W σ D) :
    ∀ (ρ : Valuation D) (η : ParamInterp κ D) (w : W)
      (x : Var) (t : TermH κ) (φ : FormulaH σ κ),
      Forces M ρ η w (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) ↔
        Forces M (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) η w φ := by
  classical
  have hwf : WellFounded (fun a b : FormulaH σ κ =>
      Syntax.Henkin.fSize (σ := σ) (κ := κ) a < Syntax.Henkin.fSize (σ := σ) (κ := κ) b) :=
    (InvImage.wf
      (f := fun ψ : FormulaH σ κ => Syntax.Henkin.fSize (σ := σ) (κ := κ) ψ)
      (r := fun a b : Nat => a < b) Nat.lt_wfRel.wf)
  let C : FormulaH σ κ → Prop :=
    fun φ =>
      ∀ (ρ : Valuation D) (η : ParamInterp κ D) (w : W)
        (x : Var) (t : TermH κ),
        Forces M ρ η w (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) ↔
          Forces M (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) η w φ
  intro ρ η w x t φ
  have hC : C φ := by
    refine hwf.induction (C := C) φ ?_
    intro φ ih ρ η w x t
    have hEvalSubstTerm :
        ∀ u : TermH κ,
          evalTerm ρ η (Syntax.Henkin.substTerm (κ := κ) x t u) =
            evalTerm (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) η u := by
      intro u
      cases u with
      | var z =>
          by_cases hzx : z = x <;>
            simp [Syntax.Henkin.substTerm, evalTerm, HeytingLean.Noneism.KripkeFO.update, hzx]
      | param k =>
          simp [Syntax.Henkin.substTerm, evalTerm]
    -- helper: evalTerm invariant under updating a variable not in `fvTerm t`
    have evalTerm_update_of_not_mem_fvTerm (z : Var) (d : D)
        (hz : z ∉ Syntax.Henkin.fvTerm (κ := κ) t) :
        evalTerm (HeytingLean.Noneism.KripkeFO.update ρ z d) η t = evalTerm ρ η t := by
      cases t with
      | param k =>
          simp [evalTerm]
      | var y =>
          have hzy : z ≠ y := by
            simpa [Syntax.Henkin.fvTerm] using hz
          have hyz : y ≠ z := Ne.symm hzy
          simp [evalTerm, HeytingLean.Noneism.KripkeFO.update, hyz]
    cases φ with
    | top =>
        simp [Syntax.Henkin.substFormula, Forces]
    | bot =>
        simp [Syntax.Henkin.substFormula, Forces]
    | pred p args =>
        have hMap :
            List.map (evalTerm ρ η) (Syntax.Henkin.substTerms (κ := κ) x t args) =
              List.map (evalTerm (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) η) args := by
          simp [Syntax.Henkin.substTerms, List.map_map, Function.comp, hEvalSubstTerm]
        simp [Syntax.Henkin.substFormula, Forces, hMap]
    | eExists u =>
        have hEval :
            evalTerm ρ η (Syntax.Henkin.substTerm (κ := κ) x t u) =
              evalTerm (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) η u :=
          hEvalSubstTerm u
        simp [Syntax.Henkin.substFormula, Forces, hEval]
    | not φ =>
        have ihφ := ih φ (by simp [Syntax.Henkin.fSize])
        constructor
        · intro h
          have hNot :
              ∀ v, w ≤ v →
                Forces M ρ η v (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) → False := by
            simpa [Syntax.Henkin.substFormula, Forces] using h
          intro v hwv hvφ
          have hvSub :
              Forces M ρ η v (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) :=
            (ihφ (ρ := ρ) (η := η) (w := v) (x := x) (t := t)).2 hvφ
          exact hNot v hwv hvSub
        · intro h
          have hNot :
              ∀ v, w ≤ v →
                Forces M (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) η v φ → False := by
            simpa [Forces] using h
          have : Forces M ρ η w
              (.not (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ)) := by
            intro v hwv hvSub
            have hvφ :
                Forces M (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) η v φ :=
              (ihφ (ρ := ρ) (η := η) (w := v) (x := x) (t := t)).1 hvSub
            exact hNot v hwv hvφ
          simpa [Syntax.Henkin.substFormula, Forces] using this
    | and φ ψ =>
        have ihφ := ih φ (by
          simp [Syntax.Henkin.fSize]
          have hle :
              Syntax.Henkin.fSize (σ := σ) (κ := κ) φ ≤
                Syntax.Henkin.fSize (σ := σ) (κ := κ) φ + Syntax.Henkin.fSize (σ := σ) (κ := κ) ψ :=
            Nat.le_add_right _ _
          have hlt :
              Syntax.Henkin.fSize (σ := σ) (κ := κ) φ <
                (Syntax.Henkin.fSize (σ := σ) (κ := κ) φ + Syntax.Henkin.fSize (σ := σ) (κ := κ) ψ).succ :=
            Nat.lt_succ_of_le hle
          exact hlt)
        have ihψ := ih ψ (by
          simp [Syntax.Henkin.fSize]
          have hle :
              Syntax.Henkin.fSize (σ := σ) (κ := κ) ψ ≤
                Syntax.Henkin.fSize (σ := σ) (κ := κ) φ + Syntax.Henkin.fSize (σ := σ) (κ := κ) ψ :=
            Nat.le_add_left _ _
          have hlt :
              Syntax.Henkin.fSize (σ := σ) (κ := κ) ψ <
                (Syntax.Henkin.fSize (σ := σ) (κ := κ) φ + Syntax.Henkin.fSize (σ := σ) (κ := κ) ψ).succ :=
            Nat.lt_succ_of_le hle
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hlt)
        simp [Syntax.Henkin.substFormula, Forces,
          ihφ (ρ := ρ) (η := η) (w := w) (x := x) (t := t),
          ihψ (ρ := ρ) (η := η) (w := w) (x := x) (t := t)]
    | or φ ψ =>
        have ihφ := ih φ (by
          simp [Syntax.Henkin.fSize]
          have hle :
              Syntax.Henkin.fSize (σ := σ) (κ := κ) φ ≤
                Syntax.Henkin.fSize (σ := σ) (κ := κ) φ + Syntax.Henkin.fSize (σ := σ) (κ := κ) ψ :=
            Nat.le_add_right _ _
          have hlt :
              Syntax.Henkin.fSize (σ := σ) (κ := κ) φ <
                (Syntax.Henkin.fSize (σ := σ) (κ := κ) φ + Syntax.Henkin.fSize (σ := σ) (κ := κ) ψ).succ :=
            Nat.lt_succ_of_le hle
          exact hlt)
        have ihψ := ih ψ (by
          simp [Syntax.Henkin.fSize]
          have hle :
              Syntax.Henkin.fSize (σ := σ) (κ := κ) ψ ≤
                Syntax.Henkin.fSize (σ := σ) (κ := κ) φ + Syntax.Henkin.fSize (σ := σ) (κ := κ) ψ :=
            Nat.le_add_left _ _
          have hlt :
              Syntax.Henkin.fSize (σ := σ) (κ := κ) ψ <
                (Syntax.Henkin.fSize (σ := σ) (κ := κ) φ + Syntax.Henkin.fSize (σ := σ) (κ := κ) ψ).succ :=
            Nat.lt_succ_of_le hle
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hlt)
        simp [Syntax.Henkin.substFormula, Forces,
          ihφ (ρ := ρ) (η := η) (w := w) (x := x) (t := t),
          ihψ (ρ := ρ) (η := η) (w := w) (x := x) (t := t)]
    | imp φ ψ =>
        have ihφ := ih φ (by
          simp [Syntax.Henkin.fSize]
          have hle :
              Syntax.Henkin.fSize (σ := σ) (κ := κ) φ ≤
                Syntax.Henkin.fSize (σ := σ) (κ := κ) φ + Syntax.Henkin.fSize (σ := σ) (κ := κ) ψ :=
            Nat.le_add_right _ _
          have hlt :
              Syntax.Henkin.fSize (σ := σ) (κ := κ) φ <
                (Syntax.Henkin.fSize (σ := σ) (κ := κ) φ + Syntax.Henkin.fSize (σ := σ) (κ := κ) ψ).succ :=
            Nat.lt_succ_of_le hle
          exact hlt)
        have ihψ := ih ψ (by
          simp [Syntax.Henkin.fSize]
          have hle :
              Syntax.Henkin.fSize (σ := σ) (κ := κ) ψ ≤
                Syntax.Henkin.fSize (σ := σ) (κ := κ) φ + Syntax.Henkin.fSize (σ := σ) (κ := κ) ψ :=
            Nat.le_add_left _ _
          have hlt :
              Syntax.Henkin.fSize (σ := σ) (κ := κ) ψ <
                (Syntax.Henkin.fSize (σ := σ) (κ := κ) φ + Syntax.Henkin.fSize (σ := σ) (κ := κ) ψ).succ :=
            Nat.lt_succ_of_le hle
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hlt)
        constructor
        · intro h
          have hImp :
              ∀ v, w ≤ v →
                Forces M ρ η v (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) →
                  Forces M ρ η v (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t ψ) := by
            simpa [Syntax.Henkin.substFormula, Forces] using h
          intro v hwv hvφ
          have hvSubφ :
              Forces M ρ η v (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) :=
            (ihφ (ρ := ρ) (η := η) (w := v) (x := x) (t := t)).2 hvφ
          have hvSubψ :
              Forces M ρ η v (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t ψ) :=
            hImp v hwv hvSubφ
          exact (ihψ (ρ := ρ) (η := η) (w := v) (x := x) (t := t)).1 hvSubψ
        · intro h
          have hImp :
              ∀ v, w ≤ v →
                Forces M (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) η v φ →
                  Forces M (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) η v ψ := by
            simpa [Forces] using h
          have : Forces M ρ η w
              (.imp
                (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ)
                (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t ψ)) := by
            intro v hwv hvSubφ
            have hvφ :
                Forces M (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) η v φ :=
              (ihφ (ρ := ρ) (η := η) (w := v) (x := x) (t := t)).1 hvSubφ
            have hvψ :
                Forces M (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) η v ψ :=
              hImp v hwv hvφ
            exact (ihψ (ρ := ρ) (η := η) (w := v) (x := x) (t := t)).2 hvψ
          simpa [Syntax.Henkin.substFormula, Forces] using this
    | sigma z φ =>
        by_cases hzx : z = x
        · simp [Syntax.Henkin.substFormula, Forces, hzx, HeytingLean.Noneism.KripkeFO.update_update_same]
        · by_cases hcap : z ∈ Syntax.Henkin.fvTerm (κ := κ) t ∧ x ∈ Syntax.Henkin.fvFormula (σ := σ) (κ := κ) φ
          · -- capture: rename binder away
            -- Under `hcap`, we have `z ∈ fvTerm t`, so the `avoid` set from `substFormula`
            -- simplifies to `insert x (varsFormula φ ∪ fvTerm t)`. We match that normal form so
            -- `simp [substFormula, ...]` uses our `z'`.
            let avoid : Finset Var :=
              insert x (Syntax.Henkin.varsFormula (σ := σ) (κ := κ) φ ∪ Syntax.Henkin.fvTerm (κ := κ) t)
            let z' : Var := HeytingLean.Noneism.Syntax.freshVar avoid
            have hz'notAvoid : z' ∉ avoid := HeytingLean.Noneism.Syntax.freshVar_not_mem avoid
            have hz'notVars : z' ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) φ := by
              intro hmem
              have : z' ∈ avoid := by
                apply Finset.mem_insert_of_mem
                exact Finset.mem_union_left _ hmem
              exact hz'notAvoid this
            have hz'notFvTerm : z' ∉ Syntax.Henkin.fvTerm (κ := κ) t := by
              intro hmem
              have : z' ∈ avoid := by
                apply Finset.mem_insert_of_mem
                exact Finset.mem_union_right _ hmem
              exact hz'notAvoid this
            have hz'neX : z' ≠ x := by
              intro hEq
              have hx : x ∈ avoid := by
                simp [avoid]
              exact hz'notAvoid (by simpa [hEq] using hx)
            have hz'neZ : z' ≠ z := by
              intro hEq
              have hzIn : z ∈ avoid := by
                apply Finset.mem_insert_of_mem
                exact Finset.mem_union_right _ hcap.1
              exact hz'notAvoid (by simpa [hEq] using hzIn)
            have hlt :
                Syntax.Henkin.fSize (σ := σ) (κ := κ)
                    (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) z z' φ) <
                  Syntax.Henkin.fSize (σ := σ) (κ := κ) (.sigma z φ : FormulaH σ κ) := by
              simp [Syntax.Henkin.fSize, Syntax.Henkin.fSize_renameFormula]
            have ihRen := ih (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) z z' φ) hlt
            constructor
            · intro h
              rcases (by
                simpa [Syntax.Henkin.substFormula, Forces, hzx, hcap, avoid, z'] using h) with ⟨d, hd⟩
              have hSub :
                  Forces M
                    (HeytingLean.Noneism.KripkeFO.update
                      (HeytingLean.Noneism.KripkeFO.update ρ z' d) x
                      (evalTerm (HeytingLean.Noneism.KripkeFO.update ρ z' d) η t))
                    η w (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) z z' φ) :=
                (ihRen (ρ := HeytingLean.Noneism.KripkeFO.update ρ z' d) (η := η) (w := w) (x := x) (t := t)).1
                  (by simpa [avoid, z'] using hd)
              have hEvalT : evalTerm (HeytingLean.Noneism.KripkeFO.update ρ z' d) η t = evalTerm ρ η t :=
                evalTerm_update_of_not_mem_fvTerm z' d hz'notFvTerm
              have hSub :
                  Forces M
                    (HeytingLean.Noneism.KripkeFO.update
                      (HeytingLean.Noneism.KripkeFO.update ρ z' d) x (evalTerm ρ η t))
                    η w (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) z z' φ) := by
                simpa [hEvalT] using hSub
              have hcommxz' :
                  HeytingLean.Noneism.KripkeFO.update
                      (HeytingLean.Noneism.KripkeFO.update ρ z' d) x (evalTerm ρ η t) =
                    HeytingLean.Noneism.KripkeFO.update
                      (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z' d := by
                simpa using
                  (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := z') (y := x)
                    (dx := d) (dy := evalTerm ρ η t) hz'neX)
              have hSub' :
                  Forces M
                    (HeytingLean.Noneism.KripkeFO.update
                      (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z' d)
                    η w (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) z z' φ) := by
                simpa [hcommxz'] using hSub
              have hRen0 :
                  Forces M
                    (HeytingLean.Noneism.KripkeFO.update
                      (HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z' d) z d)
                    η w φ := by
                have := (forces_renameFormula_of_not_mem_varsFormula (σ := σ) (κ := κ)
                  (M := M)
                  (ρ := HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z' d)
                  (η := η) (w := w)
                  (x := z) (y := z') φ hz'notVars).1 hSub'
                have hz'val :
                    HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z' d z' = d := by
                  simp [HeytingLean.Noneism.KripkeFO.update]
                simpa [HeytingLean.Noneism.KripkeFO.update, hz'val] using this
              have hRen := hRen0
              have hcommzz' :
                  HeytingLean.Noneism.KripkeFO.update
                      (HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z' d) z d =
                    HeytingLean.Noneism.KripkeFO.update
                      (HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z d) z' d := by
                simpa using
                  (HeytingLean.Noneism.KripkeFO.update_comm
                    (ρ := HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t))
                    (x := z') (y := z) (dx := d) (dy := d) hz'neZ)
              have hRen' :
                  Forces M
                    (HeytingLean.Noneism.KripkeFO.update
                      (HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z d) z' d)
                    η w φ := by
                simpa [hcommzz'] using hRen
              have hDrop :
                  Forces M
                    (HeytingLean.Noneism.KripkeFO.update
                      (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z d)
                    η w φ :=
                (forces_update_of_not_mem_varsFormula (σ := σ) (κ := κ)
                  (M := M)
                  (ρ := HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z d)
                  (η := η) (w := w)
                  (x := z') (d := d) φ hz'notVars).1 hRen'
              refine ⟨d, ?_⟩
              simpa [Forces] using hDrop
            · intro h
              rcases (by simpa [Forces] using h) with ⟨d, hd⟩
              have hdExt :
                  Forces M
                    (HeytingLean.Noneism.KripkeFO.update
                      (HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z d) z' d)
                    η w φ :=
                (forces_update_of_not_mem_varsFormula (σ := σ) (κ := κ)
                  (M := M)
                  (ρ := HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z d)
                  (η := η) (w := w)
                  (x := z') (d := d) φ hz'notVars).2 hd
              have hcommzz' :
                  HeytingLean.Noneism.KripkeFO.update
                      (HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z d) z' d =
                    HeytingLean.Noneism.KripkeFO.update
                      (HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z' d) z d := by
                simpa using
                  (HeytingLean.Noneism.KripkeFO.update_comm
                    (ρ := HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t))
                    (x := z') (y := z) (dx := d) (dy := d) hz'neZ).symm
              have hdExt :
                  Forces M
                    (HeytingLean.Noneism.KripkeFO.update
                      (HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z' d) z d)
                    η w φ := by
                simpa [hcommzz'] using hdExt
              let ρ1 : Valuation D :=
                HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z' d
              have hρ1z' : ρ1 z' = d := by
                simp [ρ1]
              have : Forces M (HeytingLean.Noneism.KripkeFO.update ρ1 z (ρ1 z')) η w φ := by
                simpa [ρ1, hρ1z'] using hdExt
              have hRen :
                  Forces M ρ1 η w (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) z z' φ) :=
                (forces_renameFormula_of_not_mem_varsFormula (σ := σ) (κ := κ)
                  (M := M) (ρ := ρ1) (η := η) (w := w)
                  (x := z) (y := z') φ hz'notVars).2 this
              have hcommxz' :
                  HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z' d =
                    HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z' d) x (evalTerm ρ η t) := by
                simpa using
                  (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := z') (y := x)
                    (dx := d) (dy := evalTerm ρ η t) hz'neX).symm
              have hRen :
                  Forces M
                    (HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z' d) x (evalTerm ρ η t))
                    η w (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) z z' φ) := by
                simpa [ρ1, hcommxz'] using hRen
              have hEvalT : evalTerm (HeytingLean.Noneism.KripkeFO.update ρ z' d) η t = evalTerm ρ η t :=
                evalTerm_update_of_not_mem_fvTerm z' d hz'notFvTerm
              have hRen :
                  Forces M
                    (HeytingLean.Noneism.KripkeFO.update
                      (HeytingLean.Noneism.KripkeFO.update ρ z' d) x
                      (evalTerm (HeytingLean.Noneism.KripkeFO.update ρ z' d) η t))
                    η w (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) z z' φ) := by
                simpa [hEvalT] using hRen
              have hdSub :
                  Forces M (HeytingLean.Noneism.KripkeFO.update ρ z' d) η w
                    (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) z z' φ)) :=
                (ihRen (ρ := HeytingLean.Noneism.KripkeFO.update ρ z' d) (η := η) (w := w) (x := x) (t := t)).2 hRen
              simpa [Syntax.Henkin.substFormula, Forces, hzx, hcap, avoid, z'] using (show ∃ d : D,
                Forces M (HeytingLean.Noneism.KripkeFO.update ρ z' d) η w
                  (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) z z' φ)) from ⟨d, hdSub⟩)
          · -- no capture
            have hlt : Syntax.Henkin.fSize (σ := σ) (κ := κ) φ <
                Syntax.Henkin.fSize (σ := σ) (κ := κ) (.sigma z φ : FormulaH σ κ) := by
              simp [Syntax.Henkin.fSize]
            have ihφ := ih φ hlt
            by_cases hzFree : z ∈ Syntax.Henkin.fvTerm (κ := κ) t
            · have hxNotFree : x ∉ Syntax.Henkin.fvFormula (σ := σ) (κ := κ) φ := by
                have : x ∉ Syntax.Henkin.fvFormula (σ := σ) (κ := κ) φ := by
                  intro hx'
                  exact (hcap ⟨hzFree, hx'⟩)
                exact this
              constructor
              · intro h
                rcases (by simpa [Syntax.Henkin.substFormula, Forces, hzx, hcap] using h) with ⟨d, hd⟩
                refine ⟨d, ?_⟩
                have hd' :
                    Forces M
                      (HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ z d) x
                        (evalTerm (HeytingLean.Noneism.KripkeFO.update ρ z d) η t))
                      η w φ :=
                  (ihφ (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d) (η := η) (w := w) (x := x) (t := t)).1 hd
                -- drop the update at `x` since `x` is not free in `φ`
                have hd'' : Forces M (HeytingLean.Noneism.KripkeFO.update ρ z d) η w φ :=
                  (forces_update_of_not_mem_fvFormula (σ := σ) (κ := κ)
                    (M := M) (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d) (η := η) (w := w)
                    (x := x) (d := evalTerm (HeytingLean.Noneism.KripkeFO.update ρ z d) η t) φ hxNotFree).1 hd'
                -- commute updates and re-add the canonical update at `x`
                have hcomm :
                    HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z d =
                      HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ z d) x (evalTerm ρ η t) := by
                  simpa using
                    (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := z) (y := x)
                      (dx := d) (dy := evalTerm ρ η t) hzx).symm
                have hd''' :
                    Forces M
                      (HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ z d) x (evalTerm ρ η t))
                      η w φ :=
                  (forces_update_of_not_mem_fvFormula (σ := σ) (κ := κ)
                    (M := M) (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d) (η := η) (w := w)
                    (x := x) (d := evalTerm ρ η t) φ hxNotFree).2 hd''
                simpa [Forces, hcomm] using hd'''
              · intro h
                rcases (by simpa [Forces] using h) with ⟨d, hd⟩
                have hcomm :
                    HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z d =
                      HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ z d) x (evalTerm ρ η t) := by
                  simpa using
                    (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := z) (y := x)
                      (dx := d) (dy := evalTerm ρ η t) hzx).symm
                have hd' :
                    Forces M
                      (HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ z d) x (evalTerm ρ η t))
                      η w φ := by
                  simpa [hcomm] using hd
                -- drop update at x, apply IH backwards, then rebuild sigma
                have hd'' : Forces M (HeytingLean.Noneism.KripkeFO.update ρ z d) η w φ :=
                  (forces_update_of_not_mem_fvFormula (σ := σ) (κ := κ)
                    (M := M) (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d) (η := η) (w := w)
                    (x := x) (d := evalTerm ρ η t) φ hxNotFree).1 hd'
                have hd''' :
                    Forces M
                      (HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ z d) x
                        (evalTerm (HeytingLean.Noneism.KripkeFO.update ρ z d) η t))
                      η w φ :=
                  (forces_update_of_not_mem_fvFormula (σ := σ) (κ := κ)
                    (M := M) (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d) (η := η) (w := w)
                    (x := x) (d := evalTerm (HeytingLean.Noneism.KripkeFO.update ρ z d) η t) φ hxNotFree).2 hd''
                have hdSub :
                    Forces M (HeytingLean.Noneism.KripkeFO.update ρ z d) η w
                      (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) :=
                  (ihφ (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d) (η := η) (w := w) (x := x) (t := t)).2 hd'''
                simpa [Syntax.Henkin.substFormula, Forces, hzx, hcap] using (show ∃ d : D,
                  Forces M (HeytingLean.Noneism.KripkeFO.update ρ z d) η w
                    (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) from ⟨d, hdSub⟩)
            · -- z not in fvTerm t: evalTerm invariant
              constructor
              · intro h
                rcases (by simpa [Syntax.Henkin.substFormula, Forces, hzx, hcap] using h) with ⟨d, hd⟩
                refine ⟨d, ?_⟩
                have hd' :
                    Forces M
                      (HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ z d) x
                        (evalTerm (HeytingLean.Noneism.KripkeFO.update ρ z d) η t))
                      η w φ :=
                  (ihφ (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d) (η := η) (w := w) (x := x) (t := t)).1 hd
                have hEvalT : evalTerm (HeytingLean.Noneism.KripkeFO.update ρ z d) η t = evalTerm ρ η t :=
                  evalTerm_update_of_not_mem_fvTerm z d hzFree
                have hd' :
                    Forces M
                      (HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ z d) x (evalTerm ρ η t))
                      η w φ := by
                  simpa [hEvalT] using hd'
                have hcomm :
                    HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d) x (evalTerm ρ η t) =
                      HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z d := by
                  simpa using
                    (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := z) (y := x)
                      (dx := d) (dy := evalTerm ρ η t) hzx)
                simpa [Forces, hcomm] using hd'
              · intro h
                rcases (by simpa [Forces] using h) with ⟨d, hd⟩
                have hcomm :
                    HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z d =
                      HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d) x (evalTerm ρ η t) := by
                  simpa using
                    (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := z) (y := x)
                      (dx := d) (dy := evalTerm ρ η t) hzx).symm
                have hd' :
                    Forces M
                      (HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ z d) x (evalTerm ρ η t))
                      η w φ := by
                  simpa [hcomm] using hd
                have hEvalT : evalTerm (HeytingLean.Noneism.KripkeFO.update ρ z d) η t = evalTerm ρ η t :=
                  evalTerm_update_of_not_mem_fvTerm z d hzFree
                have hd' :
                    Forces M
                      (HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ z d) x
                        (evalTerm (HeytingLean.Noneism.KripkeFO.update ρ z d) η t))
                      η w φ := by
                  simpa [hEvalT] using hd'
                have hdSub :
                    Forces M (HeytingLean.Noneism.KripkeFO.update ρ z d) η w
                      (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) :=
                  (ihφ (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d) (η := η) (w := w) (x := x) (t := t)).2 hd'
                simpa [Syntax.Henkin.substFormula, Forces, hzx, hcap] using (show ∃ d : D,
                  Forces M (HeytingLean.Noneism.KripkeFO.update ρ z d) η w
                    (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) from ⟨d, hdSub⟩)
    | pi z φ =>
        by_cases hzx : z = x
        ·
          simp [Syntax.Henkin.substFormula, Forces, hzx, HeytingLean.Noneism.KripkeFO.update_update_same]
        · by_cases hcap : z ∈ Syntax.Henkin.fvTerm (κ := κ) t ∧ x ∈ Syntax.Henkin.fvFormula (σ := σ) (κ := κ) φ
          · -- capture: rename binder away
            let avoid : Finset Var :=
              insert x (Syntax.Henkin.varsFormula (σ := σ) (κ := κ) φ ∪ Syntax.Henkin.fvTerm (κ := κ) t)
            let z' : Var := HeytingLean.Noneism.Syntax.freshVar avoid
            have hz'notAvoid : z' ∉ avoid := HeytingLean.Noneism.Syntax.freshVar_not_mem avoid
            have hz'notVars : z' ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) φ := by
              intro hmem
              have : z' ∈ avoid := by
                apply Finset.mem_insert_of_mem
                exact Finset.mem_union_left _ hmem
              exact hz'notAvoid this
            have hz'notFvTerm : z' ∉ Syntax.Henkin.fvTerm (κ := κ) t := by
              intro hmem
              have : z' ∈ avoid := by
                apply Finset.mem_insert_of_mem
                exact Finset.mem_union_right _ hmem
              exact hz'notAvoid this
            have hz'neX : z' ≠ x := by
              intro hEq
              have hx : x ∈ avoid := by
                simp [avoid]
              exact hz'notAvoid (by simpa [hEq] using hx)
            have hz'neZ : z' ≠ z := by
              intro hEq
              have hzIn : z ∈ avoid := by
                apply Finset.mem_insert_of_mem
                exact Finset.mem_union_right _ hcap.1
              exact hz'notAvoid (by simpa [hEq] using hzIn)
            have hlt :
                Syntax.Henkin.fSize (σ := σ) (κ := κ)
                    (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) z z' φ) <
                  Syntax.Henkin.fSize (σ := σ) (κ := κ) (.pi z φ : FormulaH σ κ) := by
              simp [Syntax.Henkin.fSize, Syntax.Henkin.fSize_renameFormula]
            have ihRen := ih (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) z z' φ) hlt
            constructor
            · intro h v hwv d
              have hdSub :
                  Forces M (HeytingLean.Noneism.KripkeFO.update ρ z' d) η v
                    (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t
                      (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) z z' φ)) := by
                have hFor :
                    ∀ v, w ≤ v → ∀ d : D,
                      Forces M (HeytingLean.Noneism.KripkeFO.update ρ z' d) η v
                        (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t
                          (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) z z' φ)) := by
                  simpa [Syntax.Henkin.substFormula, Forces, hzx, hcap, avoid, z'] using h
                exact hFor v hwv d
              have hSub :
                  Forces M
                    (HeytingLean.Noneism.KripkeFO.update
                      (HeytingLean.Noneism.KripkeFO.update ρ z' d) x
                      (evalTerm (HeytingLean.Noneism.KripkeFO.update ρ z' d) η t))
                    η v (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) z z' φ) :=
                (ihRen (ρ := HeytingLean.Noneism.KripkeFO.update ρ z' d) (η := η) (w := v) (x := x) (t := t)).1 hdSub
              have hEvalT : evalTerm (HeytingLean.Noneism.KripkeFO.update ρ z' d) η t = evalTerm ρ η t :=
                evalTerm_update_of_not_mem_fvTerm z' d hz'notFvTerm
              have hSub :
                  Forces M
                    (HeytingLean.Noneism.KripkeFO.update
                      (HeytingLean.Noneism.KripkeFO.update ρ z' d) x (evalTerm ρ η t))
                    η v (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) z z' φ) := by
                simpa [hEvalT] using hSub
              have hcommxz' :
                  HeytingLean.Noneism.KripkeFO.update
                      (HeytingLean.Noneism.KripkeFO.update ρ z' d) x (evalTerm ρ η t) =
                    HeytingLean.Noneism.KripkeFO.update
                      (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z' d := by
                simpa using
                  (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := z') (y := x)
                    (dx := d) (dy := evalTerm ρ η t) hz'neX)
              have hSub' :
                  Forces M
                    (HeytingLean.Noneism.KripkeFO.update
                      (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z' d)
                    η v (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) z z' φ) := by
                simpa [hcommxz'] using hSub
              have hRen0 :
                  Forces M
                    (HeytingLean.Noneism.KripkeFO.update
                      (HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z' d) z d)
                    η v φ := by
                have :=
                  (forces_renameFormula_of_not_mem_varsFormula (σ := σ) (κ := κ)
                    (M := M)
                    (ρ := HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z' d)
                    (η := η) (w := v)
                    (x := z) (y := z') φ hz'notVars).1 hSub'
                have hz'val :
                    HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z' d z' = d := by
                  simp [HeytingLean.Noneism.KripkeFO.update]
                simpa [HeytingLean.Noneism.KripkeFO.update, hz'val] using this
              have hRen := hRen0
              have hcommzz' :
                  HeytingLean.Noneism.KripkeFO.update
                      (HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z' d) z d =
                    HeytingLean.Noneism.KripkeFO.update
                      (HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z d) z' d := by
                simpa using
                  (HeytingLean.Noneism.KripkeFO.update_comm
                    (ρ := HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t))
                    (x := z') (y := z) (dx := d) (dy := d) hz'neZ)
              have hRen' :
                  Forces M
                    (HeytingLean.Noneism.KripkeFO.update
                      (HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z d) z' d)
                    η v φ := by
                simpa [hcommzz'] using hRen
              have hDrop :
                  Forces M
                    (HeytingLean.Noneism.KripkeFO.update
                      (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z d)
                    η v φ :=
                (forces_update_of_not_mem_varsFormula (σ := σ) (κ := κ)
                  (M := M)
                  (ρ := HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z d)
                  (η := η) (w := v)
                  (x := z') (d := d) φ hz'notVars).1 hRen'
              simpa [Forces] using hDrop
            · intro h
              have hFor :
                  ∀ v, w ≤ v → ∀ d : D,
                    Forces M
                      (HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z d)
                      η v φ := by
                simpa [Forces] using h
              have : Forces M ρ η w
                  (.pi z'
                    (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t
                      (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) z z' φ)) : FormulaH σ κ) := by
                intro v hwv d
                have hd :
                    Forces M
                      (HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z d)
                      η v φ :=
                  hFor v hwv d
                have hdExt :
                    Forces M
                      (HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update
                          (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z d) z' d)
                      η v φ :=
                  (forces_update_of_not_mem_varsFormula (σ := σ) (κ := κ)
                    (M := M)
                    (ρ := HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z d)
                    (η := η) (w := v)
                    (x := z') (d := d) φ hz'notVars).2 hd
                have hcommzz' :
                    HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update
                          (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z d) z' d =
                      HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update
                          (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z' d) z d := by
                  simpa using
                    (HeytingLean.Noneism.KripkeFO.update_comm
                      (ρ := HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t))
                      (x := z') (y := z) (dx := d) (dy := d) hz'neZ).symm
                have hdExt :
                    Forces M
                      (HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update
                          (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z' d) z d)
                      η v φ := by
                  simpa [hcommzz'] using hdExt
                let ρ1 : Valuation D :=
                  HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z' d
                have hρ1z' : ρ1 z' = d := by
                  simp [ρ1]
                have : Forces M (HeytingLean.Noneism.KripkeFO.update ρ1 z (ρ1 z')) η v φ := by
                  simpa [ρ1, hρ1z'] using hdExt
                have hRen :
                    Forces M ρ1 η v (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) z z' φ) :=
                  (forces_renameFormula_of_not_mem_varsFormula (σ := σ) (κ := κ)
                    (M := M) (ρ := ρ1) (η := η) (w := v)
                    (x := z) (y := z') φ hz'notVars).2 this
                have hcommxz' :
                    HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z' d =
                      HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z' d) x (evalTerm ρ η t) := by
                  simpa using
                    (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := z') (y := x)
                      (dx := d) (dy := evalTerm ρ η t) hz'neX).symm
                have hRen :
                    Forces M
                      (HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z' d) x (evalTerm ρ η t))
                      η v (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) z z' φ) := by
                  simpa [ρ1, hcommxz'] using hRen
                have hEvalT : evalTerm (HeytingLean.Noneism.KripkeFO.update ρ z' d) η t = evalTerm ρ η t :=
                  evalTerm_update_of_not_mem_fvTerm z' d hz'notFvTerm
                have hRen :
                    Forces M
                      (HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ z' d) x
                        (evalTerm (HeytingLean.Noneism.KripkeFO.update ρ z' d) η t))
                      η v (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) z z' φ) := by
                  simpa [hEvalT] using hRen
                have hdSub :
                    Forces M (HeytingLean.Noneism.KripkeFO.update ρ z' d) η v
                      (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t
                        (Syntax.Henkin.renameFormula (σ := σ) (κ := κ) z z' φ)) :=
                  (ihRen (ρ := HeytingLean.Noneism.KripkeFO.update ρ z' d) (η := η) (w := v) (x := x) (t := t)).2 hRen
                exact hdSub
              simpa [Syntax.Henkin.substFormula, Forces, hzx, hcap, avoid, z'] using this
          · -- no capture
            have hlt : Syntax.Henkin.fSize (σ := σ) (κ := κ) φ <
                Syntax.Henkin.fSize (σ := σ) (κ := κ) (.pi z φ : FormulaH σ κ) := by
              simp [Syntax.Henkin.fSize]
            have ihφ := ih φ hlt
            by_cases hzFree : z ∈ Syntax.Henkin.fvTerm (κ := κ) t
            · have hxNotFree : x ∉ Syntax.Henkin.fvFormula (σ := σ) (κ := κ) φ := by
                intro hx'
                exact (hcap ⟨hzFree, hx'⟩)
              constructor
              · intro h
                have hFor :
                    ∀ v, w ≤ v → ∀ d : D,
                      Forces M (HeytingLean.Noneism.KripkeFO.update ρ z d) η v
                        (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) := by
                  simpa [Syntax.Henkin.substFormula, Forces, hzx, hcap] using h
                intro v hwv d
                have hdSub :
                    Forces M (HeytingLean.Noneism.KripkeFO.update ρ z d) η v
                      (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) :=
                  hFor v hwv d
                have hd' :
                    Forces M
                      (HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ z d) x
                        (evalTerm (HeytingLean.Noneism.KripkeFO.update ρ z d) η t))
                      η v φ :=
                  (ihφ (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d) (η := η) (w := v) (x := x) (t := t)).1 hdSub
                have hd'' :
                    Forces M (HeytingLean.Noneism.KripkeFO.update ρ z d) η v φ :=
                  (forces_update_of_not_mem_fvFormula (σ := σ) (κ := κ)
                    (M := M) (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d) (η := η) (w := v)
                    (x := x) (d := evalTerm (HeytingLean.Noneism.KripkeFO.update ρ z d) η t) φ hxNotFree).1 hd'
                have hd''' :
                    Forces M (HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d) x (evalTerm ρ η t)) η v φ :=
                  (forces_update_of_not_mem_fvFormula (σ := σ) (κ := κ)
                    (M := M) (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d) (η := η) (w := v)
                    (x := x) (d := evalTerm ρ η t) φ hxNotFree).2 hd''
                have hcomm :
                    HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ z d) x (evalTerm ρ η t) =
                      HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z d := by
                  simpa using
                    (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := z) (y := x)
                      (dx := d) (dy := evalTerm ρ η t) hzx)
                simpa [Forces, hcomm] using hd'''
              · intro h
                have hFor :
                    ∀ v, w ≤ v → ∀ d : D,
                      Forces M
                        (HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z d)
                        η v φ := by
                  simpa [Forces] using h
                have : Forces M ρ η w (.pi z (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ)) := by
                  intro v hwv d
                  have hd :
                      Forces M
                        (HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z d)
                        η v φ :=
                    hFor v hwv d
                  have hcomm :
                      HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z d =
                        HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d) x (evalTerm ρ η t) := by
                    simpa using
                      (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := z) (y := x)
                        (dx := d) (dy := evalTerm ρ η t) hzx).symm
                  have hd' :
                      Forces M (HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d) x (evalTerm ρ η t)) η v φ := by
                    simpa [hcomm] using hd
                  have hd'' :
                      Forces M (HeytingLean.Noneism.KripkeFO.update ρ z d) η v φ :=
                    (forces_update_of_not_mem_fvFormula (σ := σ) (κ := κ)
                      (M := M) (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d) (η := η) (w := v)
                      (x := x) (d := evalTerm ρ η t) φ hxNotFree).1 hd'
                  have hd''' :
                      Forces M
                        (HeytingLean.Noneism.KripkeFO.update
                          (HeytingLean.Noneism.KripkeFO.update ρ z d) x
                          (evalTerm (HeytingLean.Noneism.KripkeFO.update ρ z d) η t))
                        η v φ :=
                    (forces_update_of_not_mem_fvFormula (σ := σ) (κ := κ)
                      (M := M) (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d) (η := η) (w := v)
                      (x := x) (d := evalTerm (HeytingLean.Noneism.KripkeFO.update ρ z d) η t) φ hxNotFree).2 hd''
                  have hdSub :
                      Forces M (HeytingLean.Noneism.KripkeFO.update ρ z d) η v
                        (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) :=
                    (ihφ (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d) (η := η) (w := v) (x := x) (t := t)).2 hd'''
                  exact hdSub
                simpa [Syntax.Henkin.substFormula, Forces, hzx, hcap] using this
            · -- z not in fvTerm t: evalTerm invariant
              constructor
              · intro h
                have hFor :
                    ∀ v, w ≤ v → ∀ d : D,
                      Forces M (HeytingLean.Noneism.KripkeFO.update ρ z d) η v
                        (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) := by
                  simpa [Syntax.Henkin.substFormula, Forces, hzx, hcap] using h
                intro v hwv d
                have hdSub :
                    Forces M (HeytingLean.Noneism.KripkeFO.update ρ z d) η v
                      (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) :=
                  hFor v hwv d
                have hd' :
                    Forces M
                      (HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ z d) x
                        (evalTerm (HeytingLean.Noneism.KripkeFO.update ρ z d) η t))
                      η v φ :=
                  (ihφ (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d) (η := η) (w := v) (x := x) (t := t)).1 hdSub
                have hEvalT : evalTerm (HeytingLean.Noneism.KripkeFO.update ρ z d) η t = evalTerm ρ η t :=
                  evalTerm_update_of_not_mem_fvTerm z d hzFree
                have hd' :
                    Forces M
                      (HeytingLean.Noneism.KripkeFO.update
                        (HeytingLean.Noneism.KripkeFO.update ρ z d) x (evalTerm ρ η t))
                      η v φ := by
                  simpa [hEvalT] using hd'
                have hcomm :
                    HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d) x (evalTerm ρ η t) =
                      HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z d := by
                  simpa using
                    (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := z) (y := x)
                      (dx := d) (dy := evalTerm ρ η t) hzx)
                simpa [Forces, hcomm] using hd'
              · intro h
                have hFor :
                    ∀ v, w ≤ v → ∀ d : D,
                      Forces M
                        (HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z d)
                        η v φ := by
                  simpa [Forces] using h
                have : Forces M ρ η w (.pi z (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ)) := by
                  intro v hwv d
                  have hd :
                      Forces M
                        (HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z d)
                        η v φ :=
                    hFor v hwv d
                  have hcomm :
                      HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ x (evalTerm ρ η t)) z d =
                        HeytingLean.Noneism.KripkeFO.update (HeytingLean.Noneism.KripkeFO.update ρ z d) x (evalTerm ρ η t) := by
                    simpa using
                      (HeytingLean.Noneism.KripkeFO.update_comm (ρ := ρ) (x := z) (y := x)
                        (dx := d) (dy := evalTerm ρ η t) hzx).symm
                  have hd' :
                      Forces M
                        (HeytingLean.Noneism.KripkeFO.update
                          (HeytingLean.Noneism.KripkeFO.update ρ z d) x (evalTerm ρ η t))
                        η v φ := by
                    simpa [hcomm] using hd
                  have hEvalT : evalTerm (HeytingLean.Noneism.KripkeFO.update ρ z d) η t = evalTerm ρ η t :=
                    evalTerm_update_of_not_mem_fvTerm z d hzFree
                  have hd' :
                      Forces M
                        (HeytingLean.Noneism.KripkeFO.update
                          (HeytingLean.Noneism.KripkeFO.update ρ z d) x
                          (evalTerm (HeytingLean.Noneism.KripkeFO.update ρ z d) η t))
                        η v φ := by
                    simpa [hEvalT] using hd'
                  have hdSub :
                      Forces M (HeytingLean.Noneism.KripkeFO.update ρ z d) η v
                        (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) :=
                    (ihφ (ρ := HeytingLean.Noneism.KripkeFO.update ρ z d) (η := η) (w := v) (x := x) (t := t)).2 hd'
                  exact hdSub
                simpa [Syntax.Henkin.substFormula, Forces, hzx, hcap] using this
  exact hC ρ η w x t

end KripkeFOH
end Noneism
end HeytingLean
