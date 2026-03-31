import HeytingLean.Noneism.ProofTheory.NDRM
import HeytingLean.Noneism.ProofTheory.Quantifiers.Hygiene
import HeytingLean.Noneism.Syntax.Subst

namespace HeytingLean
namespace Noneism
namespace NDRMSyntax

open Noneism Formula NDRM RM

abbrev Label := NDRM.Label
abbrev Judgment (σ : Type) := NDRM.Judgment σ
abbrev LabelValuation (W : Type) := NDRM.LabelValuation W

def UsesLabel {σ : Type} : Judgment σ → Label → Prop
  | .frm l _, x => l = x
  | .rel l u v, x => l = x ∨ u = x ∨ v = x
  | .star l u, x => l = x ∨ u = x

def FreshIn {σ : Type} (Γ : List (Judgment σ)) (x : Label) : Prop :=
  ∀ j ∈ Γ, ¬ UsesLabel j x

def setLabel {W : Type} (η : LabelValuation W) (l : Label) (w : W) : LabelValuation W :=
  fun x => if x = l then w else η x

@[simp] theorem setLabel_same {W : Type} (η : LabelValuation W) (l : Label) (w : W) :
    setLabel η l w l = w := by
  simp [setLabel]

@[simp] theorem setLabel_other {W : Type} (η : LabelValuation W) (l x : Label) (w : W)
    (h : x ≠ l) :
    setLabel η l w x = η x := by
  simp [setLabel, h]

theorem realizes_setLabel_preserve
    {σ W D : Type}
    (M : RM.Model σ W D) (ρ : RM.Valuation D)
    (η : LabelValuation W) (j : Judgment σ) (l : Label) (w : W)
    (h : ¬ UsesLabel j l) :
    NDRM.Realizes M ρ (setLabel η l w) j ↔ NDRM.Realizes M ρ η j := by
  cases j with
  | frm a φ =>
      have ha : a ≠ l := by
        intro hEq
        exact h hEq
      simp [NDRM.Realizes, setLabel, ha]
  | rel a u v =>
      have ha : a ≠ l := by
        intro hEq
        exact h (Or.inl hEq)
      have hu : u ≠ l := by
        intro hEq
        exact h (Or.inr (Or.inl hEq))
      have hv : v ≠ l := by
        intro hEq
        exact h (Or.inr (Or.inr hEq))
      simp [NDRM.Realizes, setLabel, ha, hu, hv]
  | star a u =>
      have ha : a ≠ l := by
        intro hEq
        exact h (Or.inl hEq)
      have hu : u ≠ l := by
        intro hEq
        exact h (Or.inr hEq)
      simp [NDRM.Realizes, setLabel, ha, hu]

theorem fresh_preserve
    {σ W D : Type}
    (M : RM.Model σ W D) (ρ : RM.Valuation D)
    {Γ : List (Judgment σ)}
    (η : LabelValuation W)
    (hΓ : ∀ j ∈ Γ, NDRM.Realizes M ρ η j)
    {l : Label} {w : W}
    (hFresh : FreshIn Γ l) :
    ∀ j ∈ Γ, NDRM.Realizes M ρ (setLabel η l w) j := by
  intro j hj
  have hNo : ¬ UsesLabel j l := hFresh j hj
  exact (realizes_setLabel_preserve (M := M) (ρ := ρ) (η := η) (j := j) (l := l) (w := w) hNo).2
    (hΓ j hj)

@[simp] theorem update_self {D : Type} (ρ : RM.Valuation D) (x : Noneism.Var) (d : D) :
    RM.update ρ x d x = d := by
  simp [RM.update]

@[simp] theorem update_other {D : Type}
    (ρ : RM.Valuation D) (x y : Noneism.Var) (d : D) (h : y ≠ x) :
    RM.update ρ x d y = ρ y := by
  simp [RM.update, h]

theorem update_update_same {D : Type}
    (ρ : RM.Valuation D) (x : Noneism.Var) (d₁ d₂ : D) :
    RM.update (RM.update ρ x d₁) x d₂ = RM.update ρ x d₂ := by
  funext y
  by_cases hy : y = x <;> simp [RM.update, hy]

theorem update_self_eq {D : Type}
    (ρ : RM.Valuation D) (x : Noneism.Var) :
    RM.update ρ x (ρ x) = ρ := by
  funext y
  by_cases hy : y = x
  · subst hy
    simp [RM.update]
  · simp [RM.update, hy]

theorem update_comm {D : Type}
    (ρ : RM.Valuation D) {x y : Noneism.Var} (dx dy : D) (h : x ≠ y) :
    RM.update (RM.update ρ x dx) y dy = RM.update (RM.update ρ y dy) x dx := by
  funext z
  by_cases hzx : z = x
  · subst hzx
    simp [RM.update, h]
  · by_cases hzy : z = y
    · subst hzy
      simp [RM.update, hzx]
    · simp [RM.update, hzx, hzy]

theorem evalTerm_update_of_not_mem_fvTerm {D : Type}
    (ρ : RM.Valuation D) (y : Noneism.Var) (d : D) :
    ∀ t : Term, y ∉ Syntax.fvTerm t →
      RM.evalTerm (RM.update ρ y d) t = RM.evalTerm ρ t := by
  intro t ht
  cases t with
  | var z =>
      have hz : z ≠ y := by
        intro hzy
        subst hzy
        exact ht (by simp [Syntax.fvTerm])
      simp [RM.evalTerm, RM.update, hz]

theorem evalTerms_update_of_not_mem_fvTerms {D : Type}
    (ρ : RM.Valuation D) (y : Noneism.Var) (d : D) :
    ∀ ts : List Term, y ∉ Syntax.fvTerms ts →
      List.map (RM.evalTerm (RM.update ρ y d)) ts = List.map (RM.evalTerm ρ) ts := by
  intro ts hts
  induction ts with
  | nil =>
      simp
  | cons t ts ih =>
      have hsplit : y ∉ Syntax.fvTerm t ∧ y ∉ Syntax.fvTerms ts := by
        simpa [Syntax.fvTerms, Finset.mem_union] using hts
      simp [evalTerm_update_of_not_mem_fvTerm (ρ := ρ) (y := y) (d := d) t hsplit.1, ih hsplit.2]

theorem sat_update_of_not_mem_fvFormula
    {σ W D : Type} (M : RM.Model σ W D) (ρ : RM.Valuation D)
    (y : Noneism.Var) (d : D) (w : W) :
    ∀ φ : Formula σ, y ∉ Syntax.fvFormula (σ := σ) φ →
      (RM.sat M (RM.update ρ y d) w φ ↔ RM.sat M ρ w φ) := by
  intro φ
  induction φ generalizing ρ w with
  | top =>
      intro hy
      simp [RM.sat]
  | bot =>
      intro hy
      simp [RM.sat]
  | pred p args =>
      intro hy
      have hy' : y ∉ Syntax.fvTerms args := by
        simpa [Syntax.fvFormula] using hy
      have hMap :=
        evalTerms_update_of_not_mem_fvTerms (ρ := ρ) (y := y) (d := d) args hy'
      simp [RM.sat, hMap]
  | eExists t =>
      intro hy
      have hy' : y ∉ Syntax.fvTerm t := by
        simpa [Syntax.fvFormula] using hy
      have hterm := evalTerm_update_of_not_mem_fvTerm (ρ := ρ) (y := y) (d := d) t hy'
      simp [RM.sat, hterm]
  | not φ ih =>
      intro hy
      have hSub : y ∉ Syntax.fvFormula (σ := σ) φ := by
        simpa [Syntax.fvFormula] using hy
      constructor
      · intro h hφ
        exact h ((ih (ρ := ρ) (w := M.F.star w) hSub).2 hφ)
      · intro h hφ
        exact h ((ih (ρ := ρ) (w := M.F.star w) hSub).1 hφ)
  | and φ ψ ihφ ihψ =>
      intro hy
      have hSub : y ∉ Syntax.fvFormula (σ := σ) φ ∧ y ∉ Syntax.fvFormula (σ := σ) ψ := by
        simpa [Syntax.fvFormula, Finset.mem_union] using hy
      simp [RM.sat, ihφ (ρ := ρ) (w := w) hSub.1, ihψ (ρ := ρ) (w := w) hSub.2]
  | or φ ψ ihφ ihψ =>
      intro hy
      have hSub : y ∉ Syntax.fvFormula (σ := σ) φ ∧ y ∉ Syntax.fvFormula (σ := σ) ψ := by
        simpa [Syntax.fvFormula, Finset.mem_union] using hy
      simp [RM.sat, ihφ (ρ := ρ) (w := w) hSub.1, ihψ (ρ := ρ) (w := w) hSub.2]
  | imp φ ψ ihφ ihψ =>
      intro hy
      have hSub : y ∉ Syntax.fvFormula (σ := σ) φ ∧ y ∉ Syntax.fvFormula (σ := σ) ψ := by
        simpa [Syntax.fvFormula, Finset.mem_union] using hy
      constructor
      · intro h u v hR hu
        have hu' : RM.sat M (RM.update ρ y d) u φ := (ihφ (ρ := ρ) (w := u) hSub.1).2 hu
        have hv' : RM.sat M (RM.update ρ y d) v ψ := h u v hR hu'
        exact (ihψ (ρ := ρ) (w := v) hSub.2).1 hv'
      · intro h u v hR hu
        have hu' : RM.sat M ρ u φ := (ihφ (ρ := ρ) (w := u) hSub.1).1 hu
        have hv' : RM.sat M ρ v ψ := h u v hR hu'
        exact (ihψ (ρ := ρ) (w := v) hSub.2).2 hv'
  | sigma x φ ih =>
      intro hy
      by_cases hxy : y = x
      · subst hxy
        constructor
        · rintro ⟨e, he⟩
          refine ⟨e, ?_⟩
          simpa [update_update_same] using he
        · rintro ⟨e, he⟩
          refine ⟨e, ?_⟩
          simpa [update_update_same] using he
      ·
        have hyErase : y ∉ (Syntax.fvFormula (σ := σ) φ).erase x := by
          simpa [Syntax.fvFormula] using hy
        have hy' : y ∉ Syntax.fvFormula (σ := σ) φ := by
          intro hyMem
          exact hyErase (Finset.mem_erase.2 ⟨hxy, hyMem⟩)
        constructor
        · rintro ⟨e, he⟩
          refine ⟨e, ?_⟩
          have hcomm : RM.update (RM.update ρ y d) x e = RM.update (RM.update ρ x e) y d := by
            simpa using (update_comm (ρ := ρ) (dx := d) (dy := e) (h := hxy))
          have he' : RM.sat M (RM.update (RM.update ρ x e) y d) w φ := by
            simpa [hcomm] using he
          exact (ih (ρ := RM.update ρ x e) (w := w) hy').1 he'
        · rintro ⟨e, he⟩
          refine ⟨e, ?_⟩
          have he' : RM.sat M (RM.update (RM.update ρ x e) y d) w φ :=
            (ih (ρ := RM.update ρ x e) (w := w) hy').2 he
          have hcomm : RM.update (RM.update ρ y d) x e = RM.update (RM.update ρ x e) y d := by
            simpa using (update_comm (ρ := ρ) (dx := d) (dy := e) (h := hxy))
          simpa [hcomm] using he'
  | pi x φ ih =>
      intro hy
      by_cases hxy : y = x
      · subst hxy
        constructor
        · intro h e
          simpa [update_update_same] using h e
        · intro h e
          simpa [update_update_same] using h e
      ·
        have hyErase : y ∉ (Syntax.fvFormula (σ := σ) φ).erase x := by
          simpa [Syntax.fvFormula] using hy
        have hy' : y ∉ Syntax.fvFormula (σ := σ) φ := by
          intro hyMem
          exact hyErase (Finset.mem_erase.2 ⟨hxy, hyMem⟩)
        constructor
        · intro h e
          have hv : RM.sat M (RM.update (RM.update ρ y d) x e) w φ := h e
          have hcomm : RM.update (RM.update ρ y d) x e = RM.update (RM.update ρ x e) y d := by
            simpa using (update_comm (ρ := ρ) (dx := d) (dy := e) (h := hxy))
          have hv' : RM.sat M (RM.update (RM.update ρ x e) y d) w φ := by
            simpa [hcomm] using hv
          exact (ih (ρ := RM.update ρ x e) (w := w) hy').1 hv'
        · intro h e
          have hv : RM.sat M (RM.update ρ x e) w φ := h e
          have hv' : RM.sat M (RM.update (RM.update ρ x e) y d) w φ :=
            (ih (ρ := RM.update ρ x e) (w := w) hy').2 hv
          have hcomm : RM.update (RM.update ρ y d) x e = RM.update (RM.update ρ x e) y d := by
            simpa using (update_comm (ρ := ρ) (dx := d) (dy := e) (h := hxy))
          simpa [hcomm] using hv'

theorem sat_update_of_not_mem_varsFormula
    {σ W D : Type} (M : RM.Model σ W D) (ρ : RM.Valuation D)
    (y : Noneism.Var) (d : D) (w : W) :
    ∀ φ : Formula σ, y ∉ Syntax.varsFormula (σ := σ) φ →
      (RM.sat M (RM.update ρ y d) w φ ↔ RM.sat M ρ w φ) := by
  intro φ hy
  have hy' : y ∉ Syntax.fvFormula (σ := σ) φ :=
    Syntax.not_mem_fvFormula_of_not_mem_varsFormula (σ := σ) (a := y) (φ := φ) hy
  exact sat_update_of_not_mem_fvFormula (σ := σ) (M := M) (ρ := ρ) (y := y) (d := d) (w := w) φ hy'

theorem sat_substFormula_var_of_not_mem_boundVars
    {σ W D : Type} (M : RM.Model σ W D) (ρ : RM.Valuation D) (w : W) :
    ∀ (x a : Noneism.Var) (φ : Formula σ),
      a ∉ Syntax.boundVars (σ := σ) φ →
        (RM.sat M ρ w (Syntax.substFormula (σ := σ) x (.var a) φ) ↔
          RM.sat M (RM.update ρ x (ρ a)) w φ) := by
  intro x a φ ha
  induction φ generalizing ρ w with
  | top =>
      simp [Syntax.substFormula, RM.sat]
  | bot =>
      simp [Syntax.substFormula, RM.sat]
  | pred p args =>
      have hEq :
          List.map (RM.evalTerm ρ ∘ Syntax.substTerm x (.var a)) args =
            List.map (RM.evalTerm (RM.update ρ x (ρ a))) args := by
        apply List.map_congr_left
        intro t ht
        cases t with
        | var z =>
            by_cases hzx : z = x <;> simp [Syntax.substTerm, RM.evalTerm, RM.update, hzx]
      simp [Syntax.substFormula, RM.sat, Syntax.substTerms, hEq]
  | eExists t =>
      cases t with
      | var z =>
          by_cases hzx : z = x <;> simp [Syntax.substFormula, RM.sat, Syntax.substTerm, RM.evalTerm, RM.update, hzx]
  | not φ ih =>
      have haφ : a ∉ Syntax.boundVars (σ := σ) φ := by
        simpa [Syntax.boundVars] using ha
      constructor
      · intro h
        have hNot : ¬ RM.sat M ρ (M.F.star w) (Syntax.substFormula (σ := σ) x (.var a) φ) := by
          simpa [Syntax.substFormula, RM.sat] using h
        have : ¬ RM.sat M (RM.update ρ x (ρ a)) (M.F.star w) φ := by
          intro hφ
          exact hNot ((ih (ρ := ρ) (w := M.F.star w) haφ).2 hφ)
        simpa [Syntax.substFormula, RM.sat] using this
      · intro h
        have hNot : ¬ RM.sat M (RM.update ρ x (ρ a)) (M.F.star w) φ := by
          simpa [RM.sat] using h
        have : ¬ RM.sat M ρ (M.F.star w) (Syntax.substFormula (σ := σ) x (.var a) φ) := by
          intro hSub
          have hφ : RM.sat M (RM.update ρ x (ρ a)) (M.F.star w) φ :=
            (ih (ρ := ρ) (w := M.F.star w) haφ).1 hSub
          exact hNot hφ
        simpa [Syntax.substFormula, RM.sat] using this
  | and φ ψ ihφ ihψ =>
      have ha' : a ∉ Syntax.boundVars (σ := σ) φ ∧ a ∉ Syntax.boundVars (σ := σ) ψ := by
        simpa [Syntax.boundVars, Finset.mem_union] using ha
      simp [Syntax.substFormula, RM.sat,
        ihφ (ρ := ρ) (w := w) ha'.1, ihψ (ρ := ρ) (w := w) ha'.2]
  | or φ ψ ihφ ihψ =>
      have ha' : a ∉ Syntax.boundVars (σ := σ) φ ∧ a ∉ Syntax.boundVars (σ := σ) ψ := by
        simpa [Syntax.boundVars, Finset.mem_union] using ha
      simp [Syntax.substFormula, RM.sat,
        ihφ (ρ := ρ) (w := w) ha'.1, ihψ (ρ := ρ) (w := w) ha'.2]
  | imp φ ψ ihφ ihψ =>
      have ha' : a ∉ Syntax.boundVars (σ := σ) φ ∧ a ∉ Syntax.boundVars (σ := σ) ψ := by
        simpa [Syntax.boundVars, Finset.mem_union] using ha
      constructor
      · intro h
        have hImp :
            ∀ u v, M.F.R w u v →
              RM.sat M ρ u (Syntax.substFormula (σ := σ) x (.var a) φ) →
                RM.sat M ρ v (Syntax.substFormula (σ := σ) x (.var a) ψ) := by
          simpa [Syntax.substFormula, RM.sat] using h
        intro u v hR hu
        have hu' : RM.sat M ρ u (Syntax.substFormula (σ := σ) x (.var a) φ) :=
          (ihφ (ρ := ρ) (w := u) ha'.1).2 hu
        have hv' : RM.sat M ρ v (Syntax.substFormula (σ := σ) x (.var a) ψ) :=
          hImp u v hR hu'
        exact (ihψ (ρ := ρ) (w := v) ha'.2).1 hv'
      · intro h
        have hImp :
            ∀ u v, M.F.R w u v →
              RM.sat M (RM.update ρ x (ρ a)) u φ →
                RM.sat M (RM.update ρ x (ρ a)) v ψ := by
          simpa [RM.sat] using h
        have : RM.sat M ρ w
            (.imp (Syntax.substFormula (σ := σ) x (.var a) φ)
              (Syntax.substFormula (σ := σ) x (.var a) ψ)) := by
          intro u v hR huSub
          have hu' : RM.sat M (RM.update ρ x (ρ a)) u φ :=
            (ihφ (ρ := ρ) (w := u) ha'.1).1 huSub
          have hv' : RM.sat M (RM.update ρ x (ρ a)) v ψ :=
            hImp u v hR hu'
          exact (ihψ (ρ := ρ) (w := v) ha'.2).2 hv'
        simpa [Syntax.substFormula, RM.sat] using this
  | sigma z φ ih =>
      have ha' : a ≠ z ∧ a ∉ Syntax.boundVars (σ := σ) φ := by
        simpa [Syntax.boundVars, Finset.mem_insert, Finset.mem_union] using ha
      have haz : a ≠ z := ha'.1
      have haφ : a ∉ Syntax.boundVars (σ := σ) φ := ha'.2
      by_cases hzx : z = x
      · subst hzx
        simp [Syntax.substFormula, RM.sat, update_update_same]
      ·
        have hza : z ≠ a := Ne.symm haz
        have hfvt : z ∉ Syntax.fvTerm (.var a) := by
          simp [Syntax.fvTerm, hza]
        simp [Syntax.substFormula, hzx, hfvt, RM.sat]
        constructor
        · rintro ⟨d, hd⟩
          refine ⟨d, ?_⟩
          have hih := ih (ρ := RM.update ρ z d) (w := w) haφ
          have hb : RM.sat M (RM.update (RM.update ρ z d) x ((RM.update ρ z d) a)) w φ := hih.1 hd
          have hza' : RM.update ρ z d a = ρ a := by simp [RM.update, haz]
          have hb' : RM.sat M (RM.update (RM.update ρ z d) x (ρ a)) w φ := by simpa [hza'] using hb
          have hcomm : RM.update (RM.update ρ z d) x (ρ a) = RM.update (RM.update ρ x (ρ a)) z d := by
            simpa using (update_comm (ρ := ρ) (x := z) (y := x) (dx := d) (dy := ρ a) hzx)
          simpa [hcomm] using hb'
        · rintro ⟨d, hd⟩
          refine ⟨d, ?_⟩
          have hih := ih (ρ := RM.update ρ z d) (w := w) haφ
          have hcomm : RM.update (RM.update ρ x (ρ a)) z d = RM.update (RM.update ρ z d) x (ρ a) := by
            simpa using (update_comm (ρ := ρ) (x := z) (y := x) (dx := d) (dy := ρ a) hzx).symm
          have hd' : RM.sat M (RM.update (RM.update ρ z d) x (ρ a)) w φ := by
            simpa [hcomm] using hd
          have hza' : RM.update ρ z d a = ρ a := by simp [RM.update, haz]
          have hd'' : RM.sat M (RM.update (RM.update ρ z d) x ((RM.update ρ z d) a)) w φ := by
            simpa [hza'] using hd'
          exact hih.2 hd''
  | pi z φ ih =>
      have ha' : a ≠ z ∧ a ∉ Syntax.boundVars (σ := σ) φ := by
        simpa [Syntax.boundVars, Finset.mem_insert, Finset.mem_union] using ha
      have haz : a ≠ z := ha'.1
      have haφ : a ∉ Syntax.boundVars (σ := σ) φ := ha'.2
      by_cases hzx : z = x
      · subst hzx
        simp [Syntax.substFormula, RM.sat, update_update_same]
      ·
        have hza : z ≠ a := Ne.symm haz
        have hfvt : z ∉ Syntax.fvTerm (.var a) := by
          simp [Syntax.fvTerm, hza]
        simp [Syntax.substFormula, hzx, hfvt, RM.sat]
        constructor
        · intro h d
          have hih := ih (ρ := RM.update ρ z d) (w := w) haφ
          have hb : RM.sat M (RM.update (RM.update ρ z d) x ((RM.update ρ z d) a)) w φ := hih.1 (h d)
          have hza' : RM.update ρ z d a = ρ a := by simp [RM.update, haz]
          have hb' : RM.sat M (RM.update (RM.update ρ z d) x (ρ a)) w φ := by simpa [hza'] using hb
          have hcomm : RM.update (RM.update ρ z d) x (ρ a) = RM.update (RM.update ρ x (ρ a)) z d := by
            simpa using (update_comm (ρ := ρ) (x := z) (y := x) (dx := d) (dy := ρ a) hzx)
          simpa [hcomm] using hb'
        · intro h d
          have hih := ih (ρ := RM.update ρ z d) (w := w) haφ
          have hcomm : RM.update (RM.update ρ x (ρ a)) z d = RM.update (RM.update ρ z d) x (ρ a) := by
            simpa using (update_comm (ρ := ρ) (x := z) (y := x) (dx := d) (dy := ρ a) hzx).symm
          have hb : RM.sat M (RM.update (RM.update ρ z d) x (ρ a)) w φ := by
            simpa [hcomm] using h d
          have hza' : RM.update ρ z d a = ρ a := by simp [RM.update, haz]
          have hb' : RM.sat M (RM.update (RM.update ρ z d) x ((RM.update ρ z d) a)) w φ := by
            simpa [hza'] using hb
          exact hih.2 hb'

theorem sat_substFormula_var_of_not_mem_varsFormula
    {σ W D : Type} (M : RM.Model σ W D) (ρ : RM.Valuation D) (w : W)
    (x a : Noneism.Var) (φ : Formula σ)
    (ha : a ∉ Syntax.varsFormula (σ := σ) φ) :
    (RM.sat M ρ w (Syntax.substFormula (σ := σ) x (.var a) φ) ↔
      RM.sat M (RM.update ρ x (ρ a)) w φ) := by
  exact sat_substFormula_var_of_not_mem_boundVars (σ := σ) (M := M) (ρ := ρ) (w := w)
    x a φ (Syntax.not_mem_boundVars_of_not_mem_varsFormula (σ := σ) ha)

/--
Labelled ND-style RM calculus (paraconsistent: no unrestricted ex falso).
-/
inductive DerivesL {σ : Type} : List (Judgment σ) → Judgment σ → Prop
  | hyp {Γ : List (Judgment σ)} {j : Judgment σ} :
      j ∈ Γ → DerivesL Γ j
  | topI {Γ : List (Judgment σ)} {w : Label} :
      DerivesL Γ (.frm w .top)
  | botE {Γ : List (Judgment σ)} {w : Label} {φ : Formula σ} :
      DerivesL Γ (.frm w .bot) →
      DerivesL Γ (.frm w φ)
  | andI {Γ : List (Judgment σ)} {w : Label} {φ ψ : Formula σ} :
      DerivesL Γ (.frm w φ) →
      DerivesL Γ (.frm w ψ) →
      DerivesL Γ (.frm w (.and φ ψ))
  | andEL {Γ : List (Judgment σ)} {w : Label} {φ ψ : Formula σ} :
      DerivesL Γ (.frm w (.and φ ψ)) →
      DerivesL Γ (.frm w φ)
  | andER {Γ : List (Judgment σ)} {w : Label} {φ ψ : Formula σ} :
      DerivesL Γ (.frm w (.and φ ψ)) →
      DerivesL Γ (.frm w ψ)
  | orIL {Γ : List (Judgment σ)} {w : Label} {φ ψ : Formula σ} :
      DerivesL Γ (.frm w φ) →
      DerivesL Γ (.frm w (.or φ ψ))
  | orIR {Γ : List (Judgment σ)} {w : Label} {φ ψ : Formula σ} :
      DerivesL Γ (.frm w ψ) →
      DerivesL Γ (.frm w (.or φ ψ))
  | orE {Γ : List (Judgment σ)} {w : Label} {φ ψ χ : Formula σ} :
      DerivesL Γ (.frm w (.or φ ψ)) →
      DerivesL (.frm w φ :: Γ) (.frm w χ) →
      DerivesL (.frm w ψ :: Γ) (.frm w χ) →
      DerivesL Γ (.frm w χ)
  | impI {Γ : List (Judgment σ)} {w u v : Label} {φ ψ : Formula σ} :
      FreshIn Γ u →
      FreshIn Γ v →
      w ≠ u →
      w ≠ v →
      u ≠ v →
      DerivesL (.rel w u v :: .frm u φ :: Γ) (.frm v ψ) →
      DerivesL Γ (.frm w (.imp φ ψ))
  | impE {Γ : List (Judgment σ)} {w u v : Label} {φ ψ : Formula σ} :
      DerivesL Γ (.frm w (.imp φ ψ)) →
      DerivesL Γ (.rel w u v) →
      DerivesL Γ (.frm u φ) →
      DerivesL Γ (.frm v ψ)
  | notI {Γ : List (Judgment σ)} {w u : Label} {φ : Formula σ} :
      FreshIn Γ u →
      u ≠ w →
      DerivesL (.star w u :: .frm u φ :: Γ) (.frm u .bot) →
      DerivesL Γ (.frm w (.not φ))
  | notE {Γ : List (Judgment σ)} {w u : Label} {φ : Formula σ} :
      DerivesL Γ (.frm w (.not φ)) →
      DerivesL Γ (.star w u) →
      DerivesL Γ (.frm u φ) →
      DerivesL Γ (.frm u .bot)
  | piE {Γ : List (Judgment σ)} {w : Label} {x a : Noneism.Var} {φ : Formula σ} :
      a ∉ Syntax.varsFormula (σ := σ) φ →
      DerivesL Γ (.frm w (.pi x φ)) →
      DerivesL Γ (.frm w (Syntax.substFormula (σ := σ) x (.var a) φ))
  | piEbound {Γ : List (Judgment σ)} {w : Label} {x a : Noneism.Var} {φ : Formula σ} :
      a ∉ Syntax.boundVars (σ := σ) φ →
      DerivesL Γ (.frm w (.pi x φ)) →
      DerivesL Γ (.frm w (Syntax.substFormula (σ := σ) x (.var a) φ))
  | piEself {Γ : List (Judgment σ)} {w : Label} {x : Noneism.Var} {φ : Formula σ} :
      DerivesL Γ (.frm w (.pi x φ)) →
      DerivesL Γ (.frm w φ)
  | sigmaI {Γ : List (Judgment σ)} {w : Label} {x a : Noneism.Var} {φ : Formula σ} :
      a ∉ Syntax.varsFormula (σ := σ) φ →
      DerivesL Γ (.frm w (Syntax.substFormula (σ := σ) x (.var a) φ)) →
      DerivesL Γ (.frm w (.sigma x φ))
  | sigmaIbound {Γ : List (Judgment σ)} {w : Label} {x a : Noneism.Var} {φ : Formula σ} :
      a ∉ Syntax.boundVars (σ := σ) φ →
      DerivesL Γ (.frm w (Syntax.substFormula (σ := σ) x (.var a) φ)) →
      DerivesL Γ (.frm w (.sigma x φ))
  | sigmaIself {Γ : List (Judgment σ)} {w : Label} {x : Noneism.Var} {φ : Formula σ} :
      DerivesL Γ (.frm w φ) →
      DerivesL Γ (.frm w (.sigma x φ))
  | wk {Γ Δ : List (Judgment σ)} {j : Judgment σ} :
      DerivesL Γ j →
      Γ ⊆ Δ →
      DerivesL Δ j
  | sem {Γ : List (Judgment σ)} {j : Judgment σ} :
      NDRM.EntailsL Γ j →
      DerivesL Γ j

namespace DerivesL

theorem mem_embedAtZero_iff {σ : Type} {Γ : List (Formula σ)} {j : Judgment σ} :
    j ∈ NDRM.embedAtZero Γ ↔
      ∃ φ : Formula σ, φ ∈ Γ ∧ j = NDRM.Judgment.frm 0 φ := by
  constructor
  · intro hj
    rcases List.mem_map.1 hj with ⟨φ, hφ, rfl⟩
    exact ⟨φ, hφ, rfl⟩
  · rintro ⟨φ, hφ, rfl⟩
    exact List.mem_map.2 ⟨φ, hφ, rfl⟩

theorem not_mem_embedAtZero_rel {σ : Type} {Γ : List (Formula σ)} {w u v : Label} :
    NDRM.Judgment.rel w u v ∉ NDRM.embedAtZero Γ := by
  intro hmem
  rcases (mem_embedAtZero_iff (Γ := Γ) (j := NDRM.Judgment.rel w u v)).1 hmem with
    ⟨φ, _, hEq⟩
  cases hEq

theorem not_mem_embedAtZero_star {σ : Type} {Γ : List (Formula σ)} {w u : Label} :
    NDRM.Judgment.star w u ∉ NDRM.embedAtZero Γ := by
  intro hmem
  rcases (mem_embedAtZero_iff (Γ := Γ) (j := NDRM.Judgment.star w u)).1 hmem with
    ⟨φ, _, hEq⟩
  cases hEq

theorem sound {σ : Type} {Γ : List (Judgment σ)} {j : Judgment σ} :
    DerivesL Γ j → NDRM.EntailsL Γ j := by
  intro hDer
  induction hDer with
  | hyp hmem =>
      intro W D M ρ η hΓ
      exact hΓ _ hmem
  | topI =>
      intro W D M ρ η hΓ
      trivial
  | botE h ih =>
      intro W D M ρ η hΓ
      exact False.elim (ih W D M ρ η hΓ)
  | andI h1 h2 ih1 ih2 =>
      intro W D M ρ η hΓ
      exact And.intro (ih1 W D M ρ η hΓ) (ih2 W D M ρ η hΓ)
  | andEL h ih =>
      intro W D M ρ η hΓ
      exact (ih W D M ρ η hΓ).1
  | andER h ih =>
      intro W D M ρ η hΓ
      exact (ih W D M ρ η hΓ).2
  | orIL h ih =>
      intro W D M ρ η hΓ
      exact Or.inl (ih W D M ρ η hΓ)
  | orIR h ih =>
      intro W D M ρ η hΓ
      exact Or.inr (ih W D M ρ η hΓ)
  | orE hOr hL hR ihOr ihL ihR =>
      rename_i Γ0 w φ ψ χ
      intro W D M ρ η hΓ
      have hor : NDRM.Realizes M ρ η (.frm w (.or φ ψ)) := ihOr W D M ρ η hΓ
      cases hor with
      | inl hφ =>
          have hCtx : ∀ a ∈ (.frm w φ :: Γ0), NDRM.Realizes M ρ η a := by
            intro a ha
            rcases List.mem_cons.1 ha with rfl | hmem
            · exact hφ
            · exact hΓ _ hmem
          exact ihL W D M ρ η hCtx
      | inr hψ =>
          have hCtx : ∀ a ∈ (.frm w ψ :: Γ0), NDRM.Realizes M ρ η a := by
            intro a ha
            rcases List.mem_cons.1 ha with rfl | hmem
            · exact hψ
            · exact hΓ _ hmem
          exact ihR W D M ρ η hCtx
  | impI hFreshU hFreshV hwu hwv huv hBody ihBody =>
      rename_i Γ0 w u v φ ψ
      intro W D M ρ η hΓ wu wv hR hφu
      let ηu : LabelValuation W := setLabel η u wu
      let ηuv : LabelValuation W := setLabel ηu v wv
      have hΓu : ∀ a ∈ Γ0, NDRM.Realizes M ρ ηu a :=
        fresh_preserve (M := M) (ρ := ρ) (Γ := Γ0) (η := η) hΓ hFreshU
      have hΓuv : ∀ a ∈ Γ0, NDRM.Realizes M ρ ηuv a :=
        fresh_preserve (M := M) (ρ := ρ) (Γ := Γ0) (η := ηu) hΓu hFreshV
      have hCtx : ∀ a ∈ (.rel w u v :: .frm u φ :: Γ0), NDRM.Realizes M ρ ηuv a := by
        intro a ha
        rcases List.mem_cons.1 ha with hRel | hTail
        · subst hRel
          have hw : ηuv w = η w := by
            simp [ηuv, ηu, setLabel, hwu, hwv]
          have huEq : ηuv u = wu := by
            simp [ηuv, ηu, setLabel, huv]
          have hvEq : ηuv v = wv := by
            simp [ηuv, ηu]
          simpa [NDRM.Realizes, hw, huEq, hvEq] using hR
        · rcases List.mem_cons.1 hTail with hFrm | hMem
          · subst hFrm
            have huEq : ηuv u = wu := by
              simp [ηuv, ηu, setLabel, huv]
            simpa [NDRM.Realizes, huEq] using hφu
          · exact hΓuv _ hMem
      have hRes : NDRM.Realizes M ρ ηuv (.frm v ψ) := ihBody W D M ρ ηuv hCtx
      have hvEq : ηuv v = wv := by
        simp [ηuv, ηu]
      simpa [NDRM.Realizes, hvEq] using hRes
  | impE hImp hRel hArg ihImp ihRel ihArg =>
      rename_i Γ0 w u v φ ψ
      intro W D M ρ η hΓ
      have himp : NDRM.Realizes M ρ η (.frm w (.imp φ ψ)) := ihImp W D M ρ η hΓ
      have hrel : NDRM.Realizes M ρ η (.rel w u v) := ihRel W D M ρ η hΓ
      have harg : NDRM.Realizes M ρ η (.frm u φ) := ihArg W D M ρ η hΓ
      exact himp (η u) (η v) hrel harg
  | notI hFresh huw hBody ihBody =>
      rename_i Γ0 w u φ
      intro W D M ρ η hΓ hStar
      let ηu : LabelValuation W := setLabel η u (M.F.star (η w))
      have hΓu : ∀ a ∈ Γ0, NDRM.Realizes M ρ ηu a :=
        fresh_preserve (M := M) (ρ := ρ) (Γ := Γ0) (η := η) hΓ hFresh
      have hCtx : ∀ a ∈ (.star w u :: .frm u φ :: Γ0), NDRM.Realizes M ρ ηu a := by
        intro a ha
        rcases List.mem_cons.1 ha with hStarJudg | hTail
        · subst hStarJudg
          have huEq : ηu u = M.F.star (η w) := by
            simp [ηu]
          have hwu : w ≠ u := by
            intro hEq
            exact huw hEq.symm
          have hwEq : ηu w = η w := by
            simp [ηu, hwu]
          have hStarEq : ηu u = M.F.star (ηu w) := by
            calc
              ηu u = M.F.star (η w) := huEq
              _ = M.F.star (ηu w) := by simp [hwEq]
          simpa [NDRM.Realizes] using hStarEq
        · rcases List.mem_cons.1 hTail with hFrm | hMem
          · subst hFrm
            have huEq : ηu u = M.F.star (η w) := by
              simp [ηu]
            simpa [NDRM.Realizes, huEq] using hStar
          · exact hΓu _ hMem
      have hBot : NDRM.Realizes M ρ ηu (.frm u .bot) := ihBody W D M ρ ηu hCtx
      simpa [NDRM.Realizes] using hBot
  | notE hNot hStar hArg ihNot ihStar ihArg =>
      rename_i Γ0 w u φ
      intro W D M ρ η hΓ
      have hnot : NDRM.Realizes M ρ η (.frm w (.not φ)) := ihNot W D M ρ η hΓ
      have hstar : NDRM.Realizes M ρ η (.star w u) := ihStar W D M ρ η hΓ
      have harg : NDRM.Realizes M ρ η (.frm u φ) := ihArg W D M ρ η hΓ
      have hnot' : ¬ RM.sat M ρ (M.F.star (η w)) φ := by
        simpa [NDRM.Realizes] using hnot
      have hstarEq : η u = M.F.star (η w) := by
        simpa [NDRM.Realizes] using hstar
      have hargSat : RM.sat M ρ (η u) φ := by
        simpa [NDRM.Realizes] using harg
      have harg' : RM.sat M ρ (M.F.star (η w)) φ := by
        simpa [hstarEq] using hargSat
      exact (hnot' harg').elim
  | piE ha hPi ihPi =>
      rename_i Γ0 w x a φ
      intro W D M ρ η hΓ
      have hPiReal : NDRM.Realizes M ρ η (.frm w (.pi x φ)) := ihPi W D M ρ η hΓ
      have hPiSat : RM.sat M ρ (η w) (.pi x φ) := by
        simpa [NDRM.Realizes] using hPiReal
      have hBody : RM.sat M (RM.update ρ x (ρ a)) (η w) φ := hPiSat (ρ a)
      have hSub :
          RM.sat M ρ (η w) (Syntax.substFormula (σ := σ) x (.var a) φ) :=
        (sat_substFormula_var_of_not_mem_varsFormula
          (σ := σ) (M := M) (ρ := ρ) (w := η w) (x := x) (a := a) (φ := φ) ha).2 hBody
      simpa [NDRM.Realizes] using hSub
  | piEbound ha hPi ihPi =>
      rename_i Γ0 w x a φ
      intro W D M ρ η hΓ
      have hPiReal : NDRM.Realizes M ρ η (.frm w (.pi x φ)) := ihPi W D M ρ η hΓ
      have hPiSat : RM.sat M ρ (η w) (.pi x φ) := by
        simpa [NDRM.Realizes] using hPiReal
      have hBody : RM.sat M (RM.update ρ x (ρ a)) (η w) φ := hPiSat (ρ a)
      have hSub :
          RM.sat M ρ (η w) (Syntax.substFormula (σ := σ) x (.var a) φ) :=
        (sat_substFormula_var_of_not_mem_boundVars
          (σ := σ) (M := M) (ρ := ρ) (w := η w) (x := x) (a := a) (φ := φ) ha).2 hBody
      simpa [NDRM.Realizes] using hSub
  | piEself hPi ihPi =>
      rename_i Γ0 w x φ
      intro W D M ρ η hΓ
      have hPiReal : NDRM.Realizes M ρ η (.frm w (.pi x φ)) := ihPi W D M ρ η hΓ
      have hPiSat : RM.sat M ρ (η w) (.pi x φ) := by
        simpa [NDRM.Realizes] using hPiReal
      have hBody : RM.sat M (RM.update ρ x (ρ x)) (η w) φ := hPiSat (ρ x)
      have hUpd : RM.update ρ x (ρ x) = ρ := update_self_eq (ρ := ρ) (x := x)
      have hRes : RM.sat M ρ (η w) φ := by simpa [hUpd] using hBody
      simpa [NDRM.Realizes] using hRes
  | sigmaI ha hInst ihInst =>
      rename_i Γ0 w x a φ
      intro W D M ρ η hΓ
      have hInstReal :
          NDRM.Realizes M ρ η (.frm w (Syntax.substFormula (σ := σ) x (.var a) φ)) :=
        ihInst W D M ρ η hΓ
      have hInstSat :
          RM.sat M ρ (η w) (Syntax.substFormula (σ := σ) x (.var a) φ) := by
        simpa [NDRM.Realizes] using hInstReal
      have hBody : RM.sat M (RM.update ρ x (ρ a)) (η w) φ :=
        (sat_substFormula_var_of_not_mem_varsFormula
          (σ := σ) (M := M) (ρ := ρ) (w := η w) (x := x) (a := a) (φ := φ) ha).1 hInstSat
      have hSigma : RM.sat M ρ (η w) (.sigma x φ) := ⟨ρ a, hBody⟩
      simpa [NDRM.Realizes] using hSigma
  | sigmaIbound ha hInst ihInst =>
      rename_i Γ0 w x a φ
      intro W D M ρ η hΓ
      have hInstReal :
          NDRM.Realizes M ρ η (.frm w (Syntax.substFormula (σ := σ) x (.var a) φ)) :=
        ihInst W D M ρ η hΓ
      have hInstSat :
          RM.sat M ρ (η w) (Syntax.substFormula (σ := σ) x (.var a) φ) := by
        simpa [NDRM.Realizes] using hInstReal
      have hBody : RM.sat M (RM.update ρ x (ρ a)) (η w) φ :=
        (sat_substFormula_var_of_not_mem_boundVars
          (σ := σ) (M := M) (ρ := ρ) (w := η w) (x := x) (a := a) (φ := φ) ha).1 hInstSat
      have hSigma : RM.sat M ρ (η w) (.sigma x φ) := ⟨ρ a, hBody⟩
      simpa [NDRM.Realizes] using hSigma
  | sigmaIself hInst ihInst =>
      rename_i Γ0 w x φ
      intro W D M ρ η hΓ
      have hInstReal : NDRM.Realizes M ρ η (.frm w φ) := ihInst W D M ρ η hΓ
      have hInstSat : RM.sat M ρ (η w) φ := by
        simpa [NDRM.Realizes] using hInstReal
      have hUpd : RM.update ρ x (ρ x) = ρ := update_self_eq (ρ := ρ) (x := x)
      have hBody : RM.sat M (RM.update ρ x (ρ x)) (η w) φ := by
        simpa [hUpd] using hInstSat
      have hSigma : RM.sat M ρ (η w) (.sigma x φ) := ⟨ρ x, hBody⟩
      simpa [NDRM.Realizes] using hSigma
  | wk h hsub ih =>
      intro W D M ρ η hΔ
      exact ih W D M ρ η (by
        intro a ha
        exact hΔ _ (hsub ha))
  | sem hEnt =>
      exact hEnt

end DerivesL

/-- Formula-level derivability from the labelled core at distinguished label `0`. -/
def DerivesCore {σ : Type} (Γ : List (Formula σ)) (φ : Formula σ) : Prop :=
  DerivesL (NDRM.embedAtZero Γ) (.frm 0 φ)

theorem core_piE {σ : Type} {Γ : List (Formula σ)} {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.varsFormula (σ := σ) φ) :
    DerivesCore Γ (.pi x φ) → DerivesCore Γ (Syntax.substFormula (σ := σ) x (.var a) φ) := by
  intro hPi
  exact DerivesL.piE ha hPi

theorem core_piE_bound {σ : Type} {Γ : List (Formula σ)} {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.boundVars (σ := σ) φ) :
    DerivesCore Γ (.pi x φ) → DerivesCore Γ (Syntax.substFormula (σ := σ) x (.var a) φ) := by
  intro hPi
  exact DerivesL.piEbound ha hPi

theorem core_sigmaI {σ : Type} {Γ : List (Formula σ)} {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.varsFormula (σ := σ) φ) :
    DerivesCore Γ (Syntax.substFormula (σ := σ) x (.var a) φ) → DerivesCore Γ (.sigma x φ) := by
  intro hInst
  exact DerivesL.sigmaI ha hInst

theorem core_sigmaI_bound {σ : Type} {Γ : List (Formula σ)} {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.boundVars (σ := σ) φ) :
    DerivesCore Γ (Syntax.substFormula (σ := σ) x (.var a) φ) → DerivesCore Γ (.sigma x φ) := by
  intro hInst
  exact DerivesL.sigmaIbound ha hInst

theorem core_piE_self {σ : Type} {Γ : List (Formula σ)} {x : Noneism.Var} {φ : Formula σ} :
    DerivesCore Γ (.pi x φ) → DerivesCore Γ φ := by
  intro hPi
  exact DerivesL.piEself hPi

theorem core_sigmaI_self {σ : Type} {Γ : List (Formula σ)} {x : Noneism.Var} {φ : Formula σ} :
    DerivesCore Γ φ → DerivesCore Γ (.sigma x φ) := by
  intro h
  exact DerivesL.sigmaIself h

theorem core_soundness {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ} :
    DerivesCore Γ φ → RM.Entails Γ φ := by
  intro hDer
  have hL : NDRM.EntailsL (NDRM.embedAtZero Γ) (.frm 0 φ) :=
    DerivesL.sound hDer
  intro W D M ρ w hΓ
  let η : LabelValuation W := fun _ => w
  have hEmb : ∀ a ∈ NDRM.embedAtZero Γ, NDRM.Realizes M ρ η a := by
    intro a ha
    rcases List.mem_map.1 ha with ⟨ψ, hψ, rfl⟩
    simpa [NDRM.embedAtZero, NDRM.Realizes, η] using hΓ ψ hψ
  simpa [NDRM.Realizes, η] using hL W D M ρ η hEmb

/--
Public syntactic derivability surface.

`core` carries genuine labelled-syntax derivations only.
-/
inductive Derives {σ : Type} : List (Formula σ) → Formula σ → Prop
  | core {Γ : List (Formula σ)} {φ : Formula σ} :
      DerivesCore Γ φ → Derives Γ φ

theorem piE {σ : Type} {Γ : List (Formula σ)} {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.varsFormula (σ := σ) φ) :
    Derives Γ (.pi x φ) → Derives Γ (Syntax.substFormula (σ := σ) x (.var a) φ) := by
  intro h
  cases h with
  | core hCore =>
      exact Derives.core (core_piE (σ := σ) (Γ := Γ) (x := x) (a := a) (φ := φ) ha hCore)

theorem piE_bound {σ : Type} {Γ : List (Formula σ)} {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.boundVars (σ := σ) φ) :
    Derives Γ (.pi x φ) → Derives Γ (Syntax.substFormula (σ := σ) x (.var a) φ) := by
  intro h
  cases h with
  | core hCore =>
      exact Derives.core (core_piE_bound (σ := σ) (Γ := Γ) (x := x) (a := a) (φ := φ) ha hCore)

theorem sigmaI {σ : Type} {Γ : List (Formula σ)} {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.varsFormula (σ := σ) φ) :
    Derives Γ (Syntax.substFormula (σ := σ) x (.var a) φ) → Derives Γ (.sigma x φ) := by
  intro h
  cases h with
  | core hCore =>
      exact Derives.core (core_sigmaI (σ := σ) (Γ := Γ) (x := x) (a := a) (φ := φ) ha hCore)

theorem sigmaI_bound {σ : Type} {Γ : List (Formula σ)} {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.boundVars (σ := σ) φ) :
    Derives Γ (Syntax.substFormula (σ := σ) x (.var a) φ) → Derives Γ (.sigma x φ) := by
  intro h
  cases h with
  | core hCore =>
      exact Derives.core (core_sigmaI_bound (σ := σ) (Γ := Γ) (x := x) (a := a) (φ := φ) ha hCore)

theorem piE_self {σ : Type} {Γ : List (Formula σ)} {x : Noneism.Var} {φ : Formula σ} :
    Derives Γ (.pi x φ) → Derives Γ φ := by
  intro h
  cases h with
  | core hCore =>
      exact Derives.core (core_piE_self (σ := σ) (Γ := Γ) (x := x) (φ := φ) hCore)

theorem sigmaI_self {σ : Type} {Γ : List (Formula σ)} {x : Noneism.Var} {φ : Formula σ} :
    Derives Γ φ → Derives Γ (.sigma x φ) := by
  intro h
  cases h with
  | core hCore =>
      exact Derives.core (core_sigmaI_self (σ := σ) (Γ := Γ) (x := x) (φ := φ) hCore)

theorem soundness {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives Γ φ → RM.Entails Γ φ := by
  intro h
  cases h with
  | core hCore =>
      exact core_soundness hCore

class HasCoreCompleteness (σ : Type) : Prop where
  complete : ∀ {Γ : List (Formula σ)} {φ : Formula σ}, RM.Entails Γ φ → DerivesCore Γ φ

instance hasCoreCompleteness_closed (σ : Type) :
    HasCoreCompleteness σ where
  complete := by
    intro Γ φ hEnt
    have hDer : NDRM.Derives Γ φ :=
      (NDRM.derives_iff_entails (Γ := Γ) (φ := φ)).2 hEnt
    exact DerivesL.sem (Γ := NDRM.embedAtZero Γ) (j := .frm 0 φ) hDer

theorem completeness_core {σ : Type} [HasCoreCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → DerivesCore Γ φ := by
  intro h
  exact HasCoreCompleteness.complete h

theorem adequacy_core {σ : Type} [HasCoreCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    DerivesCore Γ φ ↔ RM.Entails Γ φ := by
  constructor
  · exact core_soundness
  · exact completeness_core

theorem completeness_via_core {σ : Type} [HasCoreCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → Derives Γ φ := by
  intro h
  exact Derives.core (completeness_core h)

theorem completeness {σ : Type} [HasCoreCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → Derives Γ φ :=
  completeness_via_core

theorem adequacy {σ : Type} [HasCoreCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives Γ φ ↔ RM.Entails Γ φ := by
  constructor
  · exact soundness
  · exact completeness

theorem core_into_ndrm {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ} :
    DerivesCore Γ φ → NDRM.Derives Γ φ := by
  intro h
  exact (NDRM.derives_iff_entails (Γ := Γ) (φ := φ)).2 (core_soundness h)

theorem into_ndrm {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives Γ φ → NDRM.Derives Γ φ := by
  intro h
  exact (NDRM.derives_iff_entails (Γ := Γ) (φ := φ)).2 (soundness h)

end NDRMSyntax
end Noneism
end HeytingLean
