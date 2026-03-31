import HeytingLean.LoF.LoFPrimary.Normalization
import HeytingLean.Representations.Matrix.Projection
import HeytingLean.Coalgebra.Universal.Examples.Mealy
import HeytingLean.Coalgebra.Universal.Examples.MealyFinal
import Mathlib.Data.List.FinRange

/-!
# Logic ≃ Matrix ≃ Coalgebra (finite LoFPrimary slice)

This module pins down a precise, fully verified “triangle” equivalence for the **primary**
LoF calculus (`LoFPrimary.Expr n`).

For a fixed variable arity `n`:

* **Logic** is LoFPrimary expressions modulo semantic equivalence.
* **Matrix** is diagonal `0/1` projection matrices indexed by valuations.
* **Coalgebra** is a one-state Mealy coalgebra whose observation function is the Boolean semantics.

Key point: for one-state Mealy coalgebras, bisimilarity on the unique state is exactly
extensional equality of the observation function, so it coincides with LoF semantic equivalence.

This gives a rigorous “spine” towards the broader WIP paper, while staying executable-first and
proof-hole-free.
-/

namespace HeytingLean
namespace Equivalence

namespace LoFPrimary

open HeytingLean.LoF.LoFPrimary

/-- A valuation for `n` propositional variables. -/
abbrev Val (n : Nat) : Type :=
  Fin n → Bool

instance (n : Nat) : DecidableEq (Val n) := by
  classical
  infer_instance

variable {n : Nat}

/-- Boolean-function semantics of a primary LoF expression. -/
def sem (A : Expr n) : Val n → Bool :=
  fun ρ => eval A ρ

theorem eqv_iff_sem_eq (A B : Expr n) : Eqv (n := n) A B ↔ sem (n := n) A = sem (n := n) B := by
  constructor
  · intro h
    funext ρ
    exact h ρ
  · intro h ρ
    simpa [sem] using congrArg (fun f => f ρ) h

/-! ## DNF completeness: every truth set is representable -/

/-- Boolean conjunction, definable from `mark` and `juxt` by De Morgan. -/
def band (A B : Expr n) : Expr n :=
  Expr.mark (Expr.juxt (Expr.mark A) (Expr.mark B))

@[simp] theorem eval_band (A B : Expr n) (ρ : Val n) :
    eval (n := n) (band (n := n) A B) ρ = (eval A ρ && eval B ρ) := by
  -- Case-split on the boolean values; this keeps dependencies minimal.
  cases hA : eval A ρ <;> cases hB : eval B ρ <;> simp [band, eval, hA, hB]

/-- Boolean top: `¬⊥`. -/
def btop : Expr n :=
  Expr.mark Expr.void

@[simp] theorem eval_btop (ρ : Val n) : eval (n := n) (btop (n := n)) ρ = true := by
  simp [btop, eval]

/-- A literal for variable `i` with desired boolean value. -/
def lit (i : Fin n) (b : Bool) : Expr n :=
  match b with
  | true => Expr.var i
  | false => Expr.mark (Expr.var i)

theorem eval_lit (i : Fin n) (b : Bool) (ρ : Val n) :
    eval (n := n) (lit (n := n) i b) ρ = decide (ρ i = b) := by
  cases b <;> cases h : ρ i <;> simp [lit, eval, h]

/-- A conjunction clause selecting exactly one valuation `ρ₀`. -/
def clause (ρ₀ : Val n) : Expr n :=
  (List.finRange n).foldr
    (fun i acc => band (n := n) (lit (n := n) i (ρ₀ i)) acc)
    (btop (n := n))

private theorem eval_clause_eq_all (ρ₀ ρ : Val n) :
    eval (n := n) (clause (n := n) ρ₀) ρ =
      (List.finRange n).all (fun i => decide (ρ i = ρ₀ i)) := by
  unfold clause
  induction List.finRange n with
  | nil =>
      simp [btop, eval]
  | cons i is ih =>
      simp [List.all, ih, eval_band, eval_lit]

theorem eval_clause_iff (ρ₀ ρ : Val n) :
    eval (n := n) (clause (n := n) ρ₀) ρ = true ↔ ρ = ρ₀ := by
  classical
  have hEval := eval_clause_eq_all (n := n) ρ₀ ρ
  have hAll :
      ((List.finRange n).all (fun i => decide (ρ i = ρ₀ i)) = true) ↔ (ρ = ρ₀) := by
    constructor
    · intro h
      funext i
      have hi : decide (ρ i = ρ₀ i) = true := by
        have hall' := (List.all_eq_true).1 h
        exact hall' i (List.mem_finRange i)
      exact of_decide_eq_true hi
    · intro hEq
      subst hEq
      apply (List.all_eq_true).2
      intro i _
      simp

  constructor
  · intro h
    have : (List.finRange n).all (fun i => decide (ρ i = ρ₀ i)) = true := by
      simpa [hEval] using h
    exact hAll.mp this
  · intro hEq
    have : (List.finRange n).all (fun i => decide (ρ i = ρ₀ i)) = true := hAll.mpr hEq
    simpa [hEval] using this

/-- A DNF for a list of satisfying valuations. -/
def ofList : List (Val n) → Expr n
  | [] => Expr.void
  | ρ₀ :: rest => Expr.juxt (clause (n := n) ρ₀) (ofList rest)

theorem eval_ofList_eq_true_iff (L : List (Val n)) (ρ : Val n) :
    eval (n := n) (ofList (n := n) L) ρ = true ↔ ρ ∈ L := by
  classical
  induction L with
  | nil =>
      simp [ofList, eval]
  | cons ρ₀ rest ih =>
      simp [ofList, eval, ih, eval_clause_iff, List.mem_cons, Bool.or_eq_true]

/-- A syntactic DNF from a finite truth set. -/
noncomputable def ofTruthSet (S : Finset (Val n)) : Expr n :=
  ofList (n := n) S.toList

theorem eval_ofTruthSet_eq_true_iff (S : Finset (Val n)) (ρ : Val n) :
    eval (n := n) (ofTruthSet (n := n) S) ρ = true ↔ ρ ∈ S := by
  classical
  unfold ofTruthSet
  simpa [Finset.mem_toList] using (eval_ofList_eq_true_iff (n := n) S.toList ρ)

theorem trueSet_ofTruthSet (S : Finset (Val n)) :
    trueSet (n := n) (ofTruthSet (n := n) S) = S := by
  classical
  ext ρ
  simp [mem_trueSet, eval_ofTruthSet_eq_true_iff]

/-- Equivalence between the quotient-by-truth-set-kernel and actual truth sets.

We use `Setoid.ker (trueSet)` as the exact equivalence relation “has the same truth set”.
-/
noncomputable def exprQuotEquivTruthSet :
    Quot (Setoid.ker (trueSet (n := n))) ≃ Finset (Val n) := by
  classical
  refine
    { toFun := fun q => Quot.liftOn q (fun A => trueSet (n := n) A) ?_
      invFun := fun S => Quot.mk _ (ofTruthSet (n := n) S)
      left_inv := ?_
      right_inv := ?_ }
  · intro A B h
    simpa [Setoid.ker] using h
  · intro q
    refine Quot.inductionOn q ?_
    intro A
    apply Quot.sound
    -- Kernel relation is equality of truth sets.
    -- Note the relation expects `trueSet (ofTruthSet ...) = trueSet A`.
    simpa [Setoid.ker] using (trueSet_ofTruthSet (n := n) (trueSet (n := n) A))
  · intro S
    simpa using (trueSet_ofTruthSet (n := n) S)

end LoFPrimary

/-! ## Matrix representation of truth sets -/

namespace MatrixRep

open LoFPrimary

variable {n : Nat}

noncomputable def diagProj (S : Finset (LoFPrimary.Val n)) :
    Matrix (LoFPrimary.Val n) (LoFPrimary.Val n) ℚ :=
  Matrix.diagonal fun ρ => if ρ ∈ S then (1 : ℚ) else 0

theorem diagProj_isProjection (S : Finset (LoFPrimary.Val n)) :
    HeytingLean.Representations.Matrix.IsProjection (P := diagProj (n := n) S) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [diagProj]
  · simp [diagProj, hij]

end MatrixRep

/-! ## Coalgebra representation: one-state Mealy coalgebras -/

namespace CoalgebraRep

open LoFPrimary
open HeytingLean.Coalgebra.Universal
open HeytingLean.Coalgebra.Universal.Examples

variable {n : Nat}

/-- Coalgebra for a truth set: output is membership, next-state is constant. -/
noncomputable def truthSetMealy (S : Finset (LoFPrimary.Val n)) :
    HeytingLean.Coalgebra.Universal.Coalg (F := MealyF (LoFPrimary.Val n) Bool) :=
  oneStateMealy (A := LoFPrimary.Val n) (B := Bool) (fun ρ => decide (ρ ∈ S))

/-- Coalgebra for a LoF expression: output is its semantics, next-state is constant. -/
def exprMealy {n : Nat} (A : HeytingLean.LoF.LoFPrimary.Expr n) :
    HeytingLean.Coalgebra.Universal.Coalg (F := MealyF (LoFPrimary.Val n) Bool) :=
  oneStateMealy (A := LoFPrimary.Val n) (B := Bool) (LoFPrimary.sem (n := n) A)

theorem eqv_iff_mealy_bisimilar {n : Nat}
    (A B : HeytingLean.LoF.LoFPrimary.Expr n) :
    HeytingLean.LoF.LoFPrimary.Eqv (n := n) A B ↔
      RelBisim.Bisimilar (F := MealyF (LoFPrimary.Val n) Bool)
        (exprMealy (n := n) A) (exprMealy (n := n) B) (ULift.up ()) (ULift.up ()) := by
  classical
  -- Bisimilarity on the unique state is equality of the observation functions.
  have hbisim := oneStateMealy.bisimilar_iff
    (A := LoFPrimary.Val n) (B := Bool)
    (f := LoFPrimary.sem (n := n) A) (g := LoFPrimary.sem (n := n) B)
    (u := ULift.up ()) (v := ULift.up ())
  -- Translate `Eqv` to equality of `sem`.
  simpa [exprMealy, LoFPrimary.eqv_iff_sem_eq] using hbisim.symm

/-- Coalgebraic upgrade: for Mealy machines, bisimilarity is equality of behavior semantics.

Specialized here to the one-state LoF representation, this yields a more canonical statement:
`Eqv` iff the unique behavior maps into the final Mealy coalgebra coincide.
-/
theorem eqv_iff_mealy_behavior_eq {n : Nat}
    (A B : HeytingLean.LoF.LoFPrimary.Expr n) :
    HeytingLean.LoF.LoFPrimary.Eqv (n := n) A B ↔
      (MealyFinal.sem (A := LoFPrimary.Val n) (B := Bool)
          (exprMealy (n := n) A) (ULift.up ()) =
        MealyFinal.sem (A := LoFPrimary.Val n) (B := Bool)
          (exprMealy (n := n) B) (ULift.up ())) := by
  -- `Eqv ↔ bisimilar` is the existing triangle spine.
  have hEqv :
      HeytingLean.LoF.LoFPrimary.Eqv (n := n) A B ↔
        RelBisim.Bisimilar (F := MealyF (LoFPrimary.Val n) Bool)
          (exprMealy (n := n) A) (exprMealy (n := n) B) (ULift.up ()) (ULift.up ()) :=
    eqv_iff_mealy_bisimilar (n := n) A B
  -- Bisimilarity coincides with equality of the behavior semantics into the final coalgebra.
  have hBeh :
      RelBisim.Bisimilar (F := MealyF (LoFPrimary.Val n) Bool)
          (exprMealy (n := n) A) (exprMealy (n := n) B) (ULift.up ()) (ULift.up ()) ↔
        (MealyFinal.sem (A := LoFPrimary.Val n) (B := Bool)
            (exprMealy (n := n) A) (ULift.up ()) =
          MealyFinal.sem (A := LoFPrimary.Val n) (B := Bool)
            (exprMealy (n := n) B) (ULift.up ())) := by
    simpa using
      (MealyFinal.bisimilar_iff_sem_eq (A := LoFPrimary.Val n) (B := Bool)
        (S := exprMealy (n := n) A) (T := exprMealy (n := n) B)
        (s := ULift.up ()) (t := ULift.up ()))
  exact hEqv.trans hBeh

end CoalgebraRep

end Equivalence
end HeytingLean
