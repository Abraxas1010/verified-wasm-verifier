import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Tactic
import HeytingLean.Noneism.Syntax

namespace HeytingLean
namespace Noneism
namespace Syntax

open Formula

/-- Free variables of a term. -/
def fvTerm : Term → Finset Var
  | .var x => {x}

/-- Free variables of a list of terms. -/
def fvTerms (ts : List Term) : Finset Var :=
  ts.foldr (fun t acc => fvTerm t ∪ acc) ∅

/-- Free variables of a formula. -/
def fvFormula {σ : Type} : Formula σ → Finset Var
  | .top => ∅
  | .bot => ∅
  | .pred _ args => fvTerms args
  | .eExists t => fvTerm t
  | .not φ => fvFormula φ
  | .and φ ψ => fvFormula φ ∪ fvFormula ψ
  | .or φ ψ => fvFormula φ ∪ fvFormula ψ
  | .imp φ ψ => fvFormula φ ∪ fvFormula ψ
  | .sigma x φ => (fvFormula φ).erase x
  | .pi x φ => (fvFormula φ).erase x

/-- Variables appearing anywhere in a formula (free or bound). -/
def varsFormula {σ : Type} : Formula σ → Finset Var
  | .top => ∅
  | .bot => ∅
  | .pred _ args => fvTerms args
  | .eExists t => fvTerm t
  | .not φ => varsFormula φ
  | .and φ ψ => varsFormula φ ∪ varsFormula ψ
  | .or φ ψ => varsFormula φ ∪ varsFormula ψ
  | .imp φ ψ => varsFormula φ ∪ varsFormula ψ
  | .sigma x φ => insert x (varsFormula φ)
  | .pi x φ => insert x (varsFormula φ)

/-- Bound variables of a formula. -/
def boundVars {σ : Type} : Formula σ → Finset Var
  | .top => ∅
  | .bot => ∅
  | .pred _ _ => ∅
  | .eExists _ => ∅
  | .not φ => boundVars φ
  | .and φ ψ => boundVars φ ∪ boundVars ψ
  | .or φ ψ => boundVars φ ∪ boundVars ψ
  | .imp φ ψ => boundVars φ ∪ boundVars ψ
  | .sigma x φ => insert x (boundVars φ)
  | .pi x φ => insert x (boundVars φ)

/-- Rename variable `x` to `y` in a term. -/
def renameTerm (x y : Var) : Term → Term
  | .var z => if z = x then .var y else .var z

/-- Rename variable `x` to `y` in a list of terms. -/
def renameTerms (x y : Var) (ts : List Term) : List Term :=
  ts.map (renameTerm x y)

/-- Rename variable `x` to `y` in a formula. -/
def renameFormula {σ : Type} (x y : Var) : Formula σ → Formula σ
  | .top => .top
  | .bot => .bot
  | .pred p args => .pred p (renameTerms x y args)
  | .eExists t => .eExists (renameTerm x y t)
  | .not φ => .not (renameFormula x y φ)
  | .and φ ψ => .and (renameFormula x y φ) (renameFormula x y ψ)
  | .or φ ψ => .or (renameFormula x y φ) (renameFormula x y ψ)
  | .imp φ ψ => .imp (renameFormula x y φ) (renameFormula x y ψ)
  | .sigma z φ => if z = x then .sigma y (renameFormula x y φ) else .sigma z (renameFormula x y φ)
  | .pi z φ => if z = x then .pi y (renameFormula x y φ) else .pi z (renameFormula x y φ)

/-- Formula size used for well-founded recursion. -/
def fSize {σ : Type} : Formula σ → Nat
  | .top => 1
  | .bot => 1
  | .pred _ _ => 1
  | .eExists _ => 1
  | .not φ => fSize φ + 1
  | .and φ ψ => fSize φ + fSize ψ + 1
  | .or φ ψ => fSize φ + fSize ψ + 1
  | .imp φ ψ => fSize φ + fSize ψ + 1
  | .sigma _ φ => fSize φ + 1
  | .pi _ φ => fSize φ + 1

theorem fSize_renameFormula {σ : Type} (x y : Var) (φ : Formula σ) :
    fSize (renameFormula x y φ) = fSize φ := by
  induction φ with
  | top => simp [renameFormula, fSize]
  | bot => simp [renameFormula, fSize]
  | pred p args => simp [renameFormula, fSize]
  | eExists t => simp [renameFormula, fSize]
  | not φ ih => simpa [renameFormula, fSize] using congrArg Nat.succ ih
  | and φ ψ ihφ ihψ => simp [renameFormula, fSize, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp [renameFormula, fSize, ihφ, ihψ]
  | imp φ ψ ihφ ihψ => simp [renameFormula, fSize, ihφ, ihψ]
  | sigma z φ ih => by_cases hz : z = x <;> simp [renameFormula, fSize, hz, ih]
  | pi z φ ih => by_cases hz : z = x <;> simp [renameFormula, fSize, hz, ih]

/--
If `y ≠ x`, then renaming binders/variables `x ↦ y` removes `x` from the bound-variable set.
-/
theorem not_mem_boundVars_renameFormula_target (σ : Type)
    (x y : Var) (hxy : y ≠ x) (φ : Formula σ) :
    x ∉ boundVars (σ := σ) (renameFormula x y φ) := by
  induction φ with
  | top => simp [boundVars, renameFormula]
  | bot => simp [boundVars, renameFormula]
  | pred p args => simp [boundVars, renameFormula]
  | eExists t => simp [boundVars, renameFormula]
  | not φ ih =>
      simpa [boundVars, renameFormula] using ih
  | and φ ψ ihφ ihψ =>
      simp [boundVars, renameFormula, Finset.mem_union, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [boundVars, renameFormula, Finset.mem_union, ihφ, ihψ]
  | imp φ ψ ihφ ihψ =>
      simp [boundVars, renameFormula, Finset.mem_union, ihφ, ihψ]
  | sigma z φ ih =>
      by_cases hz : z = x
      · subst hz
        simp [renameFormula, boundVars, ih, Ne.symm hxy]
      · have hxz : x ≠ z := by
          intro hxzEq
          exact hz hxzEq.symm
        simp [renameFormula, boundVars, hz, ih, hxz]
  | pi z φ ih =>
      by_cases hz : z = x
      · subst hz
        simp [renameFormula, boundVars, ih, Ne.symm hxy]
      · have hxz : x ≠ z := by
          intro hxzEq
          exact hz hxzEq.symm
        simp [renameFormula, boundVars, hz, ih, hxz]

/-- Pick a variable strictly larger than all variables in `S`. -/
def freshVar (S : Finset Var) : Var :=
  if h : S.Nonempty then S.max' h + 1 else 0

theorem freshVar_not_mem (S : Finset Var) : freshVar S ∉ S := by
  intro hmem
  have hne : S.Nonempty := ⟨freshVar S, hmem⟩
  have hEq : freshVar S = S.max' hne + 1 := by
    simp [freshVar, hne]
  have hlt : S.max' hne < freshVar S := by
    simp [hEq]
  have hle : freshVar S ≤ S.max' hne := Finset.le_max' S (freshVar S) hmem
  exact (Nat.not_lt_of_ge hle) hlt

/-- Substitute variable `x` with term `s` in a term. -/
def substTerm (x : Var) (s : Term) : Term → Term
  | .var z => if z = x then s else .var z

/-- Substitute variable `x` with term `s` in a list of terms. -/
def substTerms (x : Var) (s : Term) (ts : List Term) : List Term :=
  ts.map (substTerm x s)

/-- Capture-avoiding substitution on formulas. -/
@[irreducible] def substFormula {σ : Type} (x : Var) (s : Term) : Formula σ → Formula σ
  | .top => .top
  | .bot => .bot
  | .pred p args => .pred p (substTerms x s args)
  | .eExists t => .eExists (substTerm x s t)
  | .not φ => .not (substFormula x s φ)
  | .and φ ψ => .and (substFormula x s φ) (substFormula x s ψ)
  | .or φ ψ => .or (substFormula x s φ) (substFormula x s ψ)
  | .imp φ ψ => .imp (substFormula x s φ) (substFormula x s ψ)
  | .sigma z φ =>
      if z = x then
        .sigma z φ
      else if z ∈ fvTerm s ∧ x ∈ fvFormula φ then
        let avoid : Finset Var := varsFormula φ ∪ fvTerm s ∪ ({x, z} : Finset Var)
        let z' : Var := freshVar avoid
        .sigma z' (substFormula x s (renameFormula z z' φ))
      else
        .sigma z (substFormula x s φ)
  | .pi z φ =>
      if z = x then
        .pi z φ
      else if z ∈ fvTerm s ∧ x ∈ fvFormula φ then
        let avoid : Finset Var := varsFormula φ ∪ fvTerm s ∪ ({x, z} : Finset Var)
        let z' : Var := freshVar avoid
        .pi z' (substFormula x s (renameFormula z z' φ))
      else
        .pi z (substFormula x s φ)
termination_by
  φ => fSize φ
decreasing_by
  all_goals
    simp [fSize, fSize_renameFormula]
    try omega

/-- Substitution by a variable preserves formula size. -/
theorem fSize_substFormula_var {σ : Type} (x a : Var) :
    (φ : Formula σ) → fSize (substFormula x (.var a) φ) = fSize φ
  | .top => by simp [substFormula, fSize]
  | .bot => by simp [substFormula, fSize]
  | .pred _ _ => by simp [substFormula, fSize]
  | .eExists _ => by simp [substFormula, fSize]
  | .not φ => by
      simp [substFormula, fSize, fSize_substFormula_var (x := x) (a := a) φ]
  | .and φ ψ => by
      simp [substFormula, fSize,
        fSize_substFormula_var (x := x) (a := a) φ,
        fSize_substFormula_var (x := x) (a := a) ψ]
  | .or φ ψ => by
      simp [substFormula, fSize,
        fSize_substFormula_var (x := x) (a := a) φ,
        fSize_substFormula_var (x := x) (a := a) ψ]
  | .imp φ ψ => by
      simp [substFormula, fSize,
        fSize_substFormula_var (x := x) (a := a) φ,
        fSize_substFormula_var (x := x) (a := a) ψ]
  | .sigma z φ => by
      by_cases hzx : z = x
      · simp [substFormula, fSize, hzx]
      · by_cases hcap : z ∈ fvTerm (.var a) ∧ x ∈ fvFormula φ
        · have hrec :
              fSize
                  (substFormula x (.var a)
                    (renameFormula z
                      (freshVar (varsFormula φ ∪ fvTerm (.var a) ∪ ({x, z} : Finset Var)))
                      φ)) =
                fSize
                  (renameFormula z
                    (freshVar (varsFormula φ ∪ fvTerm (.var a) ∪ ({x, z} : Finset Var)))
                    φ) :=
            fSize_substFormula_var (x := x) (a := a)
              (renameFormula z
                (freshVar (varsFormula φ ∪ fvTerm (.var a) ∪ ({x, z} : Finset Var)))
                φ)
          have hren :
              fSize
                  (renameFormula z
                    (freshVar (varsFormula φ ∪ fvTerm (.var a) ∪ ({x, z} : Finset Var)))
                    φ) =
                fSize φ :=
            fSize_renameFormula z
              (freshVar (varsFormula φ ∪ fvTerm (.var a) ∪ ({x, z} : Finset Var)))
              φ
          have hbody :
              fSize
                  (substFormula x (.var a)
                    (renameFormula z
                      (freshVar (varsFormula φ ∪ fvTerm (.var a) ∪ ({x, z} : Finset Var)))
                      φ)) =
                fSize φ :=
            hrec.trans hren
          simpa [substFormula, fSize, hzx, hcap] using congrArg Nat.succ hbody
        · simp [substFormula, fSize, hzx, hcap,
            fSize_substFormula_var (x := x) (a := a) φ]
  | .pi z φ => by
      by_cases hzx : z = x
      · simp [substFormula, fSize, hzx]
      · by_cases hcap : z ∈ fvTerm (.var a) ∧ x ∈ fvFormula φ
        · have hrec :
              fSize
                  (substFormula x (.var a)
                    (renameFormula z
                      (freshVar (varsFormula φ ∪ fvTerm (.var a) ∪ ({x, z} : Finset Var)))
                      φ)) =
                fSize
                  (renameFormula z
                    (freshVar (varsFormula φ ∪ fvTerm (.var a) ∪ ({x, z} : Finset Var)))
                    φ) :=
            fSize_substFormula_var (x := x) (a := a)
              (renameFormula z
                (freshVar (varsFormula φ ∪ fvTerm (.var a) ∪ ({x, z} : Finset Var)))
                φ)
          have hren :
              fSize
                  (renameFormula z
                    (freshVar (varsFormula φ ∪ fvTerm (.var a) ∪ ({x, z} : Finset Var)))
                    φ) =
                fSize φ :=
            fSize_renameFormula z
              (freshVar (varsFormula φ ∪ fvTerm (.var a) ∪ ({x, z} : Finset Var)))
              φ
          have hbody :
              fSize
                  (substFormula x (.var a)
                    (renameFormula z
                      (freshVar (varsFormula φ ∪ fvTerm (.var a) ∪ ({x, z} : Finset Var)))
                      φ)) =
                fSize φ :=
            hrec.trans hren
          simpa [substFormula, fSize, hzx, hcap] using congrArg Nat.succ hbody
        · simp [substFormula, fSize, hzx, hcap,
            fSize_substFormula_var (x := x) (a := a) φ]
termination_by
  φ => fSize φ
decreasing_by
  all_goals
    simp [fSize, fSize_renameFormula]
    try omega

lemma substTerm_eq_self_of_not_mem_fvTerm (x : Var) (s t : Term)
    (h : x ∉ fvTerm t) : substTerm x s t = t := by
  cases t with
  | var z =>
      have hz : z ≠ x := by
        intro hz
        apply h
        simp [fvTerm, hz]
      simp [substTerm, hz]

lemma substTerms_eq_self_of_not_mem_fvTerms (x : Var) (s : Term) :
    (ts : List Term) → x ∉ fvTerms ts → substTerms x s ts = ts
  | [], _ => by simp [substTerms]
  | t :: ts, h => by
      have hsplit : x ∉ fvTerm t ∧ x ∉ fvTerms ts := by
        simpa [fvTerms, Finset.mem_union] using h
      have htail : substTerms x s ts = ts :=
        substTerms_eq_self_of_not_mem_fvTerms (x := x) (s := s) ts hsplit.2
      have htail' : List.map (substTerm x s) ts = ts := by
        simpa [substTerms] using htail
      simp [substTerms, substTerm_eq_self_of_not_mem_fvTerm, hsplit.1, htail']

lemma substFormula_eq_self_of_not_mem_fvFormula {σ : Type} (x : Var) (s : Term) :
    (φ : Formula σ) → x ∉ fvFormula φ → substFormula x s φ = φ
  | .top, _ => by simp [substFormula]
  | .bot, _ => by simp [substFormula]
  | .pred p args, h => by
      simpa [substFormula] using
        congrArg (Formula.pred p)
          (substTerms_eq_self_of_not_mem_fvTerms (x := x) (s := s) args (by simpa [fvFormula] using h))
  | .eExists t, h => by
      have ht : x ∉ fvTerm t := by simpa [fvFormula] using h
      simp [substFormula, substTerm_eq_self_of_not_mem_fvTerm, ht]
  | .not φ, h => by
      have hφ : x ∉ fvFormula φ := by simpa [fvFormula] using h
      simpa [substFormula] using congrArg Formula.not
        (substFormula_eq_self_of_not_mem_fvFormula (x := x) (s := s) φ hφ)
  | .and φ ψ, h => by
      have hsplit : x ∉ fvFormula φ ∧ x ∉ fvFormula ψ := by
        simpa [fvFormula, Finset.mem_union] using h
      simp [substFormula,
        substFormula_eq_self_of_not_mem_fvFormula (x := x) (s := s) φ hsplit.1,
        substFormula_eq_self_of_not_mem_fvFormula (x := x) (s := s) ψ hsplit.2]
  | .or φ ψ, h => by
      have hsplit : x ∉ fvFormula φ ∧ x ∉ fvFormula ψ := by
        simpa [fvFormula, Finset.mem_union] using h
      simp [substFormula,
        substFormula_eq_self_of_not_mem_fvFormula (x := x) (s := s) φ hsplit.1,
        substFormula_eq_self_of_not_mem_fvFormula (x := x) (s := s) ψ hsplit.2]
  | .imp φ ψ, h => by
      have hsplit : x ∉ fvFormula φ ∧ x ∉ fvFormula ψ := by
        simpa [fvFormula, Finset.mem_union] using h
      simp [substFormula,
        substFormula_eq_self_of_not_mem_fvFormula (x := x) (s := s) φ hsplit.1,
        substFormula_eq_self_of_not_mem_fvFormula (x := x) (s := s) ψ hsplit.2]
  | .sigma z φ, h => by
      by_cases hzx : z = x
      · simp [substFormula, hzx]
      · have hxz : x ≠ z := fun h' => hzx h'.symm
        have hxφ : x ∉ fvFormula φ := by
          intro hx
          exact h (Finset.mem_erase.mpr ⟨hxz, hx⟩)
        have hguard : ¬(z ∈ fvTerm s ∧ x ∈ fvFormula φ) := by
          intro hcap
          exact hxφ hcap.2
        simp [substFormula, hzx, hguard,
          substFormula_eq_self_of_not_mem_fvFormula (x := x) (s := s) φ hxφ]
  | .pi z φ, h => by
      by_cases hzx : z = x
      · simp [substFormula, hzx]
      · have hxz : x ≠ z := fun h' => hzx h'.symm
        have hxφ : x ∉ fvFormula φ := by
          intro hx
          exact h (Finset.mem_erase.mpr ⟨hxz, hx⟩)
        have hguard : ¬(z ∈ fvTerm s ∧ x ∈ fvFormula φ) := by
          intro hcap
          exact hxφ hcap.2
        simp [substFormula, hzx, hguard,
          substFormula_eq_self_of_not_mem_fvFormula (x := x) (s := s) φ hxφ]

@[simp] lemma substTerm_var_self (x : Var) (t : Term) : substTerm x (.var x) t = t := by
  cases t with
  | var z => by_cases hz : z = x <;> simp [substTerm, hz]

@[simp] lemma substTerms_var_self (x : Var) (ts : List Term) :
    substTerms x (.var x) ts = ts := by
  induction ts with
  | nil => simp [substTerms]
  | cons t ts ih =>
      have htail : substTerms x (.var x) ts = ts := ih
      have htail' : List.map (substTerm x (.var x)) ts = ts := by
        simpa [substTerms] using htail
      simp [substTerms, htail']

@[simp] lemma substFormula_var_self {σ : Type} (x : Var) (φ : Formula σ) :
    substFormula x (.var x) φ = φ := by
  induction φ with
  | top => simp [substFormula]
  | bot => simp [substFormula]
  | pred p args => simp [substFormula]
  | eExists t => simp [substFormula]
  | not φ ih => simp [substFormula, ih]
  | and φ ψ ihφ ihψ => simp [substFormula, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp [substFormula, ihφ, ihψ]
  | imp φ ψ ihφ ihψ => simp [substFormula, ihφ, ihψ]
  | sigma z φ ih =>
      by_cases hzx : z = x
      · simp [substFormula, hzx]
      · have hguard : ¬(z ∈ fvTerm (.var x) ∧ x ∈ fvFormula φ) := by
          intro hcap
          exact hzx (by simpa [fvTerm] using hcap.1)
        simp [substFormula, hzx, hguard, ih]
  | pi z φ ih =>
      by_cases hzx : z = x
      · simp [substFormula, hzx]
      · have hguard : ¬(z ∈ fvTerm (.var x) ∧ x ∈ fvFormula φ) := by
          intro hcap
          exact hzx (by simpa [fvTerm] using hcap.1)
        simp [substFormula, hzx, hguard, ih]

end Syntax
end Noneism
end HeytingLean
