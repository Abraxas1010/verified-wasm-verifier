import HeytingLean.MiniC.Syntax
import HeytingLean.MiniC.Semantics
import HeytingLean.C.Syntax
import HeytingLean.C.Semantics

namespace HeytingLean
namespace MiniC
namespace ToC

open HeytingLean.MiniC
open HeytingLean.C

/-- Explicit failure cases for the checked tiny-C lowering surface. -/
inductive CompileError where
  | unsupportedExpr (message : String)
  | unsupportedStmt (message : String)
  deriving DecidableEq, Repr, Inhabited

/-- Checked lowering for the honest tiny-C subset. Unsupported constructs fail
closed instead of silently lowering through placeholder values. -/
def compileExprChecked : Expr → Except CompileError CExpr
  | Expr.intLit n => .ok (CExpr.intLit n)
  | Expr.boolLit b => .ok (CExpr.intLit (if b then 1 else 0))
  | Expr.var x => .ok (CExpr.var x)
  | Expr.arrayLit _ =>
      .error (.unsupportedExpr "array literals are not supported in tiny-C lowering")
  | Expr.arrayLength arr =>
      match arr with
      | Expr.var name => .ok (CExpr.arrayLength name)
      | _ =>
          .error (.unsupportedExpr
            "arrayLength requires a named array variable in tiny-C lowering")
  | Expr.arrayIndex arr idx => do
      let idx' ← compileExprChecked idx
      match arr with
      | Expr.var name => .ok (CExpr.arrayIndex name idx')
      | _ =>
          .error (.unsupportedExpr
            "arrayIndex requires a named array variable in tiny-C lowering")
  | Expr.structLit _ _ =>
      .error (.unsupportedExpr "struct literals are not supported in tiny-C lowering")
  | Expr.fieldAccess obj field =>
      match obj with
      | Expr.var name => .ok (CExpr.var (MiniC.structFieldSlot name field))
      | _ =>
          .error (.unsupportedExpr
            "fieldAccess requires a named struct variable in tiny-C lowering")
  | Expr.add e₁ e₂ => return CExpr.add (← compileExprChecked e₁) (← compileExprChecked e₂)
  | Expr.sub e₁ e₂ => return CExpr.sub (← compileExprChecked e₁) (← compileExprChecked e₂)
  | Expr.mul e₁ e₂ => return CExpr.mul (← compileExprChecked e₁) (← compileExprChecked e₂)
  | Expr.le e₁ e₂ => return CExpr.le (← compileExprChecked e₁) (← compileExprChecked e₂)
  | Expr.eq e₁ e₂ => return CExpr.eq (← compileExprChecked e₁) (← compileExprChecked e₂)
  | Expr.not e => return CExpr.eq (← compileExprChecked e) (CExpr.intLit 0)
  | Expr.and e₁ e₂ => return CExpr.mul (← compileExprChecked e₁) (← compileExprChecked e₂)
  | Expr.or e₁ e₂ =>
      return CExpr.le (CExpr.intLit 1)
        (CExpr.add (← compileExprChecked e₁) (← compileExprChecked e₂))

/-- Checked lowering for the honest tiny-C statement subset. -/
def compileStmtChecked : Stmt → Except CompileError CStmt
  | Stmt.return e => return CStmt.return (← compileExprChecked e)
  | Stmt.assign x e => return CStmt.assign x (← compileExprChecked e)
  | Stmt.arrayUpdate name idx val =>
      return CStmt.arrayUpdate name (← compileExprChecked idx) (← compileExprChecked val)
  | Stmt.structUpdate name field val =>
      return CStmt.assign (MiniC.structFieldSlot name field) (← compileExprChecked val)
  | Stmt.call _ _ _ =>
      .error (.unsupportedStmt "function calls are not supported in tiny-C lowering")
  | Stmt.if_ c t e =>
      return CStmt.if_ (← compileExprChecked c) (← compileStmtChecked t) (← compileStmtChecked e)
  | Stmt.seq s₁ s₂ =>
      return CStmt.seq (← compileStmtChecked s₁) (← compileStmtChecked s₂)
  | Stmt.skip =>
      .error (.unsupportedStmt "skip has no faithful tiny-C encoding in the current fragment")
  | Stmt.while c b =>
      return CStmt.while (← compileExprChecked c) (← compileStmtChecked b)

/-- Checked function lowering for the honest tiny-C subset. -/
def compileFunChecked (fn : Fun) : Except CompileError CFun := do
  let body ← compileStmtChecked fn.body
  pure { name := fn.name, params := fn.params, body := body }

/-- Legacy total lowering for the historical tiny-C fragment.

Use `compileExprChecked` for any widening work. This total function is retained
for the existing proof-carrying fragment and older callers. -/
def compileExpr : Expr → CExpr
  | Expr.intLit n    => CExpr.intLit n
  | Expr.boolLit b   => CExpr.intLit (if b then 1 else 0)
  | Expr.var x       => CExpr.var x
  | Expr.arrayLit _  => CExpr.intLit 0
  | Expr.arrayLength _ => CExpr.intLit 0
  | Expr.arrayIndex _ _ => CExpr.intLit 0
  | Expr.structLit _ _ => CExpr.intLit 0
  | Expr.fieldAccess obj field =>
      match obj with
      | Expr.var name => CExpr.var (MiniC.structFieldSlot name field)
      | _ => CExpr.intLit 0
  | Expr.add e₁ e₂   => CExpr.add (compileExpr e₁) (compileExpr e₂)
  | Expr.sub e₁ e₂   => CExpr.sub (compileExpr e₁) (compileExpr e₂)
  | Expr.mul e₁ e₂   => CExpr.mul (compileExpr e₁) (compileExpr e₂)
  | Expr.le e₁ e₂    => CExpr.le (compileExpr e₁) (compileExpr e₂)
  | Expr.eq e₁ e₂    => CExpr.eq (compileExpr e₁) (compileExpr e₂)
  | Expr.not e       => CExpr.eq (compileExpr e) (CExpr.intLit 0)    -- boolean not as equality to 0
  | Expr.and e₁ e₂   => CExpr.mul (compileExpr e₁) (compileExpr e₂)  -- 0/1 encoding
  | Expr.or e₁ e₂    =>
      -- return 1 when either operand is non-zero (assuming 0/1 encoding)
      CExpr.le (CExpr.intLit 1)
        (CExpr.add (compileExpr e₁) (compileExpr e₂))

/-- Legacy total statement lowering for the historical tiny-C fragment.

Use `compileStmtChecked` for honest subset enforcement. -/
def compileStmt : Stmt → CStmt
  | Stmt.return e        => CStmt.return (compileExpr e)
  | Stmt.assign x e      => CStmt.assign x (compileExpr e)
  | Stmt.arrayUpdate name idx val =>
      CStmt.arrayUpdate name (compileExpr idx) (compileExpr val)
  | Stmt.structUpdate name field val =>
      CStmt.assign (MiniC.structFieldSlot name field) (compileExpr val)
  | Stmt.call _ _ ret    => CStmt.assign ret (CExpr.intLit 0)
  | Stmt.if_ c t e       => CStmt.if_ (compileExpr c) (compileStmt t) (compileStmt e)
  | Stmt.seq s₁ s₂       => CStmt.seq (compileStmt s₁) (compileStmt s₂)
  | Stmt.skip            => CStmt.return (CExpr.intLit 0)
  | Stmt.while c b       => CStmt.while (compileExpr c) (compileStmt b)

/-- Legacy total function lowering for the historical tiny-C fragment.

Use `compileFunChecked` for fail-closed compilation. -/
def compileFun (fn : Fun) : CFun :=
  { name := fn.name
    params := fn.params
    body := compileStmt fn.body }

/-! ## Compilation Correctness (total/denotational semantics) -/

/-- Convert a MiniC total store to a C partial store. -/
def toPartialStore (σ : MiniC.TotalStore) : C.Store :=
  fun x => some (σ x)

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
    (ht : MiniC.HasType Γ e τ) :
    C.evalExpr (compileExpr e) (toPartialStore σ) = some (MiniC.Expr.eval e σ) := by
  induction ht with
  | var hx =>
      simp [compileExpr, C.evalExpr, MiniC.Expr.eval, toPartialStore]
  | intLit n =>
      simp [compileExpr, C.evalExpr, MiniC.Expr.eval]
  | boolLit b =>
      cases b <;> simp [compileExpr, C.evalExpr, MiniC.Expr.eval]
  | arrayLit =>
      simp [compileExpr, C.evalExpr, MiniC.Expr.eval]
  | arrayIndex htArr htIdx ihArr ihIdx =>
      simp [compileExpr, C.evalExpr, MiniC.Expr.eval]
  | arrayLength htArr ihArr =>
      simp [compileExpr, C.evalExpr, MiniC.Expr.eval]
  | structLit =>
      simp [compileExpr, C.evalExpr, MiniC.Expr.eval]
  | fieldAccess htObj ihObj =>
      rename_i obj name field
      cases obj <;> simp [compileExpr, C.evalExpr, MiniC.Expr.eval, toPartialStore]
  | add ht1 ht2 ih1 ih2 =>
      simp [compileExpr, C.evalExpr, MiniC.Expr.eval, ih1, ih2]
  | sub ht1 ht2 ih1 ih2 =>
      simp [compileExpr, C.evalExpr, MiniC.Expr.eval, ih1, ih2]
  | mul ht1 ht2 ih1 ih2 =>
      simp [compileExpr, C.evalExpr, MiniC.Expr.eval, ih1, ih2]
  | le ht1 ht2 ih1 ih2 =>
      simp [compileExpr, C.evalExpr, MiniC.Expr.eval, ih1, ih2]
  | eq ht1 ht2 ih1 ih2 =>
      simp [compileExpr, C.evalExpr, MiniC.Expr.eval, ih1, ih2]
  | not ht ih =>
      simp [compileExpr, C.evalExpr, MiniC.Expr.eval, ih]
  | and ht1 ht2 ih1 ih2 =>
      rename_i e₁ e₂
      have ha : e₁.eval σ = 0 ∨ e₁.eval σ = 1 :=
        MiniC.eval_is01_of_hasType_bool (Γ := Γ) (σ := σ) (e := e₁) hσ ht1
      have hb : e₂.eval σ = 0 ∨ e₂.eval σ = 1 :=
        MiniC.eval_is01_of_hasType_bool (Γ := Γ) (σ := σ) (e := e₂) hσ ht2
      -- rewrite the arithmetic encoding using the 0/1 invariant for boolean subexpressions
      simp [compileExpr, C.evalExpr, MiniC.Expr.eval, ih1, ih2]
      simpa [ne_eq] using (mul01_eq_if_and (e₁.eval σ) (e₂.eval σ) ha hb)
  | or ht1 ht2 ih1 ih2 =>
      rename_i e₁ e₂
      have ha : e₁.eval σ = 0 ∨ e₁.eval σ = 1 :=
        MiniC.eval_is01_of_hasType_bool (Γ := Γ) (σ := σ) (e := e₁) hσ ht1
      have hb : e₂.eval σ = 0 ∨ e₂.eval σ = 1 :=
        MiniC.eval_is01_of_hasType_bool (Γ := Γ) (σ := σ) (e := e₂) hσ ht2
      simp [compileExpr, C.evalExpr, MiniC.Expr.eval, ih1, ih2]
      simpa [ne_eq] using (le1_add01_eq_if_or (e₁.eval σ) (e₂.eval σ) ha hb)

private def execResultTotalToC : MiniC.ExecResultTotal → C.ExecResult
  | .normal σ' => .normal (toPartialStore σ')
  | .returned v => .returned v

private inductive FragStmt : MiniC.TyEnv → MiniC.Stmt → Prop
  | ret {Γ e τ} : MiniC.HasType Γ e τ → FragStmt Γ (.return e)
  | if_ {Γ c t e} :
      MiniC.HasType Γ c .bool → FragStmt Γ t → FragStmt Γ e → FragStmt Γ (.if_ c t e)

theorem compileStmt_frag_correct (Γ : MiniC.TyEnv) (σ : MiniC.TotalStore)
    (hσ : MiniC.StoreRespects Γ σ) {s : MiniC.Stmt}
    (hs : FragStmt Γ s) :
    C.execFragC (compileStmt s) (toPartialStore σ) =
      (MiniC.Stmt.execFrag s σ).map execResultTotalToC := by
  induction hs generalizing σ with
  | ret ht =>
      have hE := compileExpr_correct (Γ := Γ) (σ := σ) hσ (ht := ht)
      simp [MiniC.Stmt.execFrag, compileStmt, execResultTotalToC, hE]
  | if_ hc ht he ihT ihE =>
      rename_i c t e
      have hC := compileExpr_correct (Γ := Γ) (σ := σ) hσ (e := c) hc
      have h01 := MiniC.eval_is01_of_hasType_bool (Γ := Γ) (σ := σ) (e := c) hσ hc
      cases h01 with
      | inl hz =>
          have hC0 : C.evalExpr (compileExpr c) (toPartialStore σ) = some 0 := by
            simpa [hz] using hC
          simpa [MiniC.Stmt.execFrag, compileStmt, C.execFragC, execResultTotalToC, hz, hC0]
            using (ihE σ hσ)
      | inr h1 =>
          have hC1 : C.evalExpr (compileExpr c) (toPartialStore σ) = some 1 := by
            simpa [h1] using hC
          have hnz : (1 : Int) ≠ 0 := by decide
          simpa [MiniC.Stmt.execFrag, compileStmt, C.execFragC, execResultTotalToC, h1, hC1, hnz]
            using (ihT σ hσ)

end ToC
end MiniC
end HeytingLean
