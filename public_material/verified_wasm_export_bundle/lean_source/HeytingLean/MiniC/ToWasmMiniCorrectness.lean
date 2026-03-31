import HeytingLean.MiniC.Semantics
import HeytingLean.MiniC.ToWasmMini
import HeytingLean.WasmMini.Semantics

namespace HeytingLean
namespace MiniC
namespace ToWasmMini

open HeytingLean.MiniC
open HeytingLean.WasmMini

/-!
# HeytingLean.MiniC.ToWasmMiniCorrectness

Phase-1 compilation correctness for MiniC expressions into WasmMini stack code.

We prove correctness against `MiniC.Expr.eval` (total semantics with 0/1 booleans)
using the expression-only evaluator `WasmMini.evalExprCode`.

This mirrors the existing `MiniC.ToC.compileExpr_correct` proof, but with a
stack-machine target rather than an expression-tree target.
-/

theorem evalExprCode_append (is₁ is₂ : List Instr) (σ : WasmMini.Store) (st : WasmMini.Stack) :
    WasmMini.evalExprCode (is₁ ++ is₂) σ st =
      (WasmMini.evalExprCode is₁ σ st).bind (fun st' => WasmMini.evalExprCode is₂ σ st') := by
  induction is₁ generalizing st with
  | nil =>
      simp [WasmMini.evalExprCode]
  | cons i is ih =>
      cases i <;> simp [WasmMini.evalExprCode, ih]
      · -- i64Add
        cases h : WasmMini.pop2 st <;> simp
      · -- i64Sub
        cases h : WasmMini.pop2 st <;> simp
      · -- i64Mul
        cases h : WasmMini.pop2 st <;> simp
      · -- i64LeS
        cases h : WasmMini.pop2 st <;> simp
      · -- i64Eq
        cases h : WasmMini.pop2 st <;> simp
      · -- i64Ne
        cases h : WasmMini.pop2 st <;> simp
      · -- i64Eqz
        cases h : WasmMini.pop1 st <;> simp

private theorem mul01_eq_if_and (a b : Int) (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    a * b = (if a ≠ 0 ∧ b ≠ 0 then 1 else 0) := by
  cases ha with
  | inl ha => simp [ha]
  | inr ha =>
      cases hb with
      | inl hb => simp [ha, hb]
      | inr hb => simp [ha, hb]

private theorem le1_add01_eq_if_or (a b : Int) (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    (if (1 : Int) ≤ a + b then (1 : Int) else 0) = (if a ≠ 0 ∨ b ≠ 0 then 1 else 0) := by
  cases ha with
  | inl ha =>
      cases hb with
      | inl hb => simp [ha, hb]
      | inr hb => simp [ha, hb]
  | inr ha =>
      cases hb with
      | inl hb => simp [ha, hb]
      | inr hb => simp [ha, hb]

theorem compileExpr_correct (Γ : MiniC.TyEnv) (σ : MiniC.TotalStore)
    (hσ : MiniC.StoreRespects Γ σ) {e : MiniC.Expr} {τ : MiniC.Ty}
    (ht : MiniC.HasType Γ e τ) (st : WasmMini.Stack) :
    WasmMini.evalExprCode (compileExpr e) σ st =
      some (MiniC.Expr.eval e σ :: st) := by
  induction ht generalizing st with
  | var hx =>
      simp [compileExpr, WasmMini.evalExprCode, MiniC.Expr.eval]
  | intLit n =>
      simp [compileExpr, WasmMini.evalExprCode, MiniC.Expr.eval]
  | boolLit b =>
      cases b <;> simp [compileExpr, WasmMini.evalExprCode, MiniC.Expr.eval]
  | arrayLit =>
      simp [compileExpr, WasmMini.evalExprCode, MiniC.Expr.eval]
  | arrayLength htArr ihArr =>
      simp [compileExpr, WasmMini.evalExprCode, MiniC.Expr.eval]
  | arrayIndex htArr htIdx ihArr ihIdx =>
      simp [compileExpr, WasmMini.evalExprCode, MiniC.Expr.eval]
  | structLit =>
      simp [compileExpr, WasmMini.evalExprCode, MiniC.Expr.eval]
  | fieldAccess htObj ihObj =>
      rename_i obj name field
      cases obj <;> simp [compileExpr, WasmMini.evalExprCode, MiniC.Expr.eval]
  | add ht1 ht2 ih1 ih2 =>
      rename_i e₁ e₂
      have h1 := ih1 st
      have h2 := ih2 (MiniC.Expr.eval e₁ σ :: st)
      -- reassociate to `compileExpr e₁ ++ (compileExpr e₂ ++ [i64Add])`
      simpa [compileExpr, List.append_assoc] using (show
        WasmMini.evalExprCode (compileExpr e₁ ++ (compileExpr e₂ ++ [Instr.i64Add])) σ st =
          some (MiniC.Expr.eval (MiniC.Expr.add e₁ e₂) σ :: st) from by
            rw [evalExprCode_append (is₁ := compileExpr e₁) (is₂ := compileExpr e₂ ++ [Instr.i64Add])]
            rw [h1]
            simp
            rw [evalExprCode_append (is₁ := compileExpr e₂) (is₂ := [Instr.i64Add])]
            rw [h2]
            simp [MiniC.Expr.eval, WasmMini.evalExprCode, WasmMini.pop2])
  | sub ht1 ht2 ih1 ih2 =>
      rename_i e₁ e₂
      have h1 := ih1 st
      have h2 := ih2 (MiniC.Expr.eval e₁ σ :: st)
      simpa [compileExpr, List.append_assoc] using (show
        WasmMini.evalExprCode (compileExpr e₁ ++ (compileExpr e₂ ++ [Instr.i64Sub])) σ st =
          some (MiniC.Expr.eval (MiniC.Expr.sub e₁ e₂) σ :: st) from by
            rw [evalExprCode_append (is₁ := compileExpr e₁) (is₂ := compileExpr e₂ ++ [Instr.i64Sub])]
            rw [h1]
            simp
            rw [evalExprCode_append (is₁ := compileExpr e₂) (is₂ := [Instr.i64Sub])]
            rw [h2]
            simp [MiniC.Expr.eval, WasmMini.evalExprCode, WasmMini.pop2])
  | mul ht1 ht2 ih1 ih2 =>
      rename_i e₁ e₂
      have h1 := ih1 st
      have h2 := ih2 (MiniC.Expr.eval e₁ σ :: st)
      simpa [compileExpr, List.append_assoc] using (show
        WasmMini.evalExprCode (compileExpr e₁ ++ (compileExpr e₂ ++ [Instr.i64Mul])) σ st =
          some (MiniC.Expr.eval (MiniC.Expr.mul e₁ e₂) σ :: st) from by
            rw [evalExprCode_append (is₁ := compileExpr e₁) (is₂ := compileExpr e₂ ++ [Instr.i64Mul])]
            rw [h1]
            simp
            rw [evalExprCode_append (is₁ := compileExpr e₂) (is₂ := [Instr.i64Mul])]
            rw [h2]
            simp [MiniC.Expr.eval, WasmMini.evalExprCode, WasmMini.pop2])
  | le ht1 ht2 ih1 ih2 =>
      rename_i e₁ e₂
      have h1 := ih1 st
      have h2 := ih2 (MiniC.Expr.eval e₁ σ :: st)
      simpa [compileExpr, List.append_assoc] using (show
        WasmMini.evalExprCode (compileExpr e₁ ++ (compileExpr e₂ ++ [Instr.i64LeS, Instr.i64ExtendI32u])) σ st =
          some (MiniC.Expr.eval (MiniC.Expr.le e₁ e₂) σ :: st) from by
            rw [evalExprCode_append (is₁ := compileExpr e₁) (is₂ := compileExpr e₂ ++ [Instr.i64LeS, Instr.i64ExtendI32u])]
            rw [h1]
            simp
            rw [evalExprCode_append (is₁ := compileExpr e₂) (is₂ := [Instr.i64LeS, Instr.i64ExtendI32u])]
            rw [h2]
            simp [MiniC.Expr.eval, WasmMini.evalExprCode, WasmMini.pop2, WasmMini.bool01])
  | eq ht1 ht2 ih1 ih2 =>
      rename_i e₁ e₂ τ
      have h1 := ih1 st
      have h2 := ih2 (MiniC.Expr.eval e₁ σ :: st)
      simpa [compileExpr, List.append_assoc] using (show
        WasmMini.evalExprCode (compileExpr e₁ ++ (compileExpr e₂ ++ [Instr.i64Eq, Instr.i64ExtendI32u])) σ st =
          some (MiniC.Expr.eval (MiniC.Expr.eq e₁ e₂) σ :: st) from by
            rw [evalExprCode_append (is₁ := compileExpr e₁) (is₂ := compileExpr e₂ ++ [Instr.i64Eq, Instr.i64ExtendI32u])]
            rw [h1]
            simp
            rw [evalExprCode_append (is₁ := compileExpr e₂) (is₂ := [Instr.i64Eq, Instr.i64ExtendI32u])]
            rw [h2]
            simp [MiniC.Expr.eval, WasmMini.evalExprCode, WasmMini.pop2, WasmMini.bool01])
  | not ht ih =>
      rename_i e
      have h := ih st
      simpa [compileExpr, List.append_assoc] using (show
        WasmMini.evalExprCode (compileExpr e ++ [Instr.i64Eqz, Instr.i64ExtendI32u]) σ st =
          some (MiniC.Expr.eval (MiniC.Expr.not e) σ :: st) from by
            rw [evalExprCode_append (is₁ := compileExpr e) (is₂ := [Instr.i64Eqz, Instr.i64ExtendI32u])]
            rw [h]
            simp [MiniC.Expr.eval, WasmMini.evalExprCode, WasmMini.pop1, WasmMini.bool01])
  | and ht1 ht2 ih1 ih2 =>
      rename_i e₁ e₂
      have ha : e₁.eval σ = 0 ∨ e₁.eval σ = 1 :=
        MiniC.eval_is01_of_hasType_bool (Γ := Γ) (σ := σ) (e := e₁) hσ ht1
      have hb : e₂.eval σ = 0 ∨ e₂.eval σ = 1 :=
        MiniC.eval_is01_of_hasType_bool (Γ := Γ) (σ := σ) (e := e₂) hσ ht2
      have h1 := ih1 st
      have h2 := ih2 (MiniC.Expr.eval e₁ σ :: st)
      simpa [compileExpr, List.append_assoc] using (show
        WasmMini.evalExprCode (compileExpr e₁ ++ (compileExpr e₂ ++ [Instr.i64Mul])) σ st =
          some (MiniC.Expr.eval (MiniC.Expr.and e₁ e₂) σ :: st) from by
            rw [evalExprCode_append (is₁ := compileExpr e₁) (is₂ := compileExpr e₂ ++ [Instr.i64Mul])]
            rw [h1]
            simp
            rw [evalExprCode_append (is₁ := compileExpr e₂) (is₂ := [Instr.i64Mul])]
            rw [h2]
            simp [MiniC.Expr.eval, WasmMini.evalExprCode, WasmMini.pop2]
            simpa [ne_eq] using (mul01_eq_if_and (e₁.eval σ) (e₂.eval σ) ha hb))
  | or ht1 ht2 ih1 ih2 =>
      rename_i e₁ e₂
      have ha : e₁.eval σ = 0 ∨ e₁.eval σ = 1 :=
        MiniC.eval_is01_of_hasType_bool (Γ := Γ) (σ := σ) (e := e₁) hσ ht1
      have hb : e₂.eval σ = 0 ∨ e₂.eval σ = 1 :=
        MiniC.eval_is01_of_hasType_bool (Γ := Γ) (σ := σ) (e := e₂) hσ ht2
      -- stack discipline: push 1, then e₁, then e₂, then add, then le_s, then extend
      have h1 := ih1 (1 :: st)
      have h2 := ih2 (MiniC.Expr.eval e₁ σ :: (1 :: st))
      -- Step 1: consume the leading `(i64.const 1)` instruction.
      simp [compileExpr, WasmMini.evalExprCode]
      -- Remaining goal is on the tail, starting from stack `1 :: st`.
      -- Reassociate and run `e₁`, then `e₂`, then the final three ops.
      rw [evalExprCode_append (is₁ := compileExpr e₁) (is₂ := compileExpr e₂ ++ [Instr.i64Add, Instr.i64LeS, Instr.i64ExtendI32u])]
      rw [h1]
      simp
      rw [evalExprCode_append (is₁ := compileExpr e₂) (is₂ := [Instr.i64Add, Instr.i64LeS, Instr.i64ExtendI32u])]
      rw [h2]
      simp [MiniC.Expr.eval, WasmMini.evalExprCode, WasmMini.pop2, WasmMini.bool01]
      simpa [ne_eq] using (le1_add01_eq_if_or (e₁.eval σ) (e₂.eval σ) ha hb)

end ToWasmMini
end MiniC
end HeytingLean
