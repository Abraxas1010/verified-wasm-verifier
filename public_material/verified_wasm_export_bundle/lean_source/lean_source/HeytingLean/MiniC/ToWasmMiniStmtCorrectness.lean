import HeytingLean.MiniC.Semantics
import HeytingLean.MiniC.ToWasmMini
import HeytingLean.MiniC.ToWasmMiniCorrectness
import HeytingLean.WasmMini.Semantics

namespace HeytingLean
namespace MiniC
namespace ToWasmMini

open HeytingLean.MiniC

/-!
# HeytingLean.MiniC.ToWasmMiniStmtCorrectness

Statement-level semantic preservation for the Phase-1 `MiniC → WasmMini` backend.

Key point: `WasmMini.execFrag` is defined as a `partial` evaluator (opaque),
so this file avoids it entirely and proves correctness against the
fuel-bounded semantics `WasmMini.execInstrsFuel`.
-/

open HeytingLean.WasmMini

/-! ## A minimal statement typing judgment (only what we need for 0/1 correctness) -/

inductive HasTypeStmt : MiniC.TyEnv → MiniC.Stmt → Prop
  | skip {Γ} : HasTypeStmt Γ .skip
  | assign {Γ x rhs τ} : Γ x = τ → MiniC.HasType Γ rhs τ → HasTypeStmt Γ (.assign x rhs)
  | seq {Γ s₁ s₂} : HasTypeStmt Γ s₁ → HasTypeStmt Γ s₂ → HasTypeStmt Γ (.seq s₁ s₂)
  | if_ {Γ c t e} : MiniC.HasType Γ c .bool → HasTypeStmt Γ t → HasTypeStmt Γ e → HasTypeStmt Γ (.if_ c t e)
  | while_ {Γ c b} : MiniC.HasType Γ c .bool → HasTypeStmt Γ b → HasTypeStmt Γ (.while c b)
  | ret {Γ e τ} : MiniC.HasType Γ e τ → HasTypeStmt Γ (.return e)

private theorem storeRespects_update (Γ : MiniC.TyEnv) (σ : MiniC.TotalStore)
    (hσ : MiniC.StoreRespects Γ σ) {x : String} {e : MiniC.Expr} {τ : MiniC.Ty}
    (hx : Γ x = τ) (he : MiniC.HasType Γ e τ) :
    MiniC.StoreRespects Γ (fun y => if y = x then MiniC.Expr.eval e σ else σ y) := by
  intro y hy
  by_cases hxy : y = x
  · subst hxy
    cases τ with
    | int =>
        have : (MiniC.Ty.int = MiniC.Ty.bool) := by
          exact hx.symm.trans hy
        cases this
    | bool =>
        have : MiniC.Expr.eval e σ = 0 ∨ MiniC.Expr.eval e σ = 1 :=
          MiniC.eval_is01_of_hasType_bool (Γ := Γ) (σ := σ) (e := e) hσ (by simpa [hx] using he)
        simpa [MiniC.StoreRespects, hx, MiniC.Expr.eval] using this
    | array elemTy size =>
        have : (MiniC.Ty.array elemTy size = MiniC.Ty.bool) := by
          exact hx.symm.trans hy
        cases this
    | struct name =>
        have : (MiniC.Ty.struct name = MiniC.Ty.bool) := by
          exact hx.symm.trans hy
        cases this
  · have : Γ y = MiniC.Ty.bool := hy
    have hOld := hσ y this
    simp [hxy, hOld]

/-! ## Bridging `evalExprCode` to `execInstrsFuel` for expression code -/

private theorem execInstrsFuel_of_evalExprCode
    {code : List WasmMini.Instr} {σ : WasmMini.Store} {st st' : WasmMini.Stack}
    (h : WasmMini.evalExprCode code σ st = some st') :
    WasmMini.execInstrsFuel (code.length + 1) code σ st = some (.normal σ st') := by
  induction code generalizing st with
  | nil =>
      simp [WasmMini.evalExprCode] at h
      cases h
      simp [WasmMini.execInstrsFuel]
  | cons i rest ih =>
      cases i <;> try (simp [WasmMini.evalExprCode] at h; cases h)
      · -- i64Const
        simp [WasmMini.evalExprCode] at h
        have hRest := ih (st := _ ) h
        simp [WasmMini.execInstrsFuel, WasmMini.execInstrFuel, WasmMini.push, List.length, hRest]
      · -- localGet
        simp [WasmMini.evalExprCode] at h
        have hRest := ih (st := _ ) h
        simp [WasmMini.execInstrsFuel, WasmMini.execInstrFuel, WasmMini.push, List.length, hRest]
      · -- localSet (impossible)
        simp [WasmMini.evalExprCode] at h
      · -- i64Add
        cases hPop : WasmMini.pop2 st with
        | none =>
            simp [WasmMini.evalExprCode, hPop] at h
        | some val =>
            rcases val with ⟨v₂, v₁, st0⟩
            have h' : WasmMini.evalExprCode rest σ ((v₁ + v₂) :: st0) = some st' := by
              simpa [WasmMini.evalExprCode, hPop] using h
            have hRest := ih (st := (v₁ + v₂) :: st0) h'
            simp [WasmMini.execInstrsFuel, WasmMini.execInstrFuel, hPop, List.length, WasmMini.push]
            exact hRest
      · -- i64Sub
        cases hPop : WasmMini.pop2 st with
        | none =>
            simp [WasmMini.evalExprCode, hPop] at h
        | some val =>
            rcases val with ⟨v₂, v₁, st0⟩
            have h' : WasmMini.evalExprCode rest σ ((v₁ - v₂) :: st0) = some st' := by
              simpa [WasmMini.evalExprCode, hPop] using h
            have hRest := ih (st := (v₁ - v₂) :: st0) h'
            simp [WasmMini.execInstrsFuel, WasmMini.execInstrFuel, hPop, List.length, WasmMini.push]
            exact hRest
      · -- i64Mul
        cases hPop : WasmMini.pop2 st with
        | none =>
            simp [WasmMini.evalExprCode, hPop] at h
        | some val =>
            rcases val with ⟨v₂, v₁, st0⟩
            have h' : WasmMini.evalExprCode rest σ (v₁ * v₂ :: st0) = some st' := by
              simpa [WasmMini.evalExprCode, hPop] using h
            have hRest := ih (st := (v₁ * v₂) :: st0) h'
            simp [WasmMini.execInstrsFuel, WasmMini.execInstrFuel, hPop, List.length, WasmMini.push]
            exact hRest
      · -- i64LeS
        cases hPop : WasmMini.pop2 st with
        | none =>
            simp [WasmMini.evalExprCode, hPop] at h
        | some val =>
            rcases val with ⟨v₂, v₁, st0⟩
            let b : Int := if v₁ ≤ v₂ then 1 else 0
            have h' : WasmMini.evalExprCode rest σ (b :: st0) = some st' := by
              simpa [WasmMini.evalExprCode, hPop, WasmMini.bool01, b] using h
            have hRest := ih (st := b :: st0) h'
            simp [WasmMini.execInstrsFuel, WasmMini.execInstrFuel, hPop, List.length, WasmMini.push, WasmMini.bool01]
            exact hRest
      · -- i64Eq
        cases hPop : WasmMini.pop2 st with
        | none =>
            simp [WasmMini.evalExprCode, hPop] at h
        | some val =>
            rcases val with ⟨v₂, v₁, st0⟩
            let b : Int := if v₁ = v₂ then 1 else 0
            have h' : WasmMini.evalExprCode rest σ (b :: st0) = some st' := by
              simpa [WasmMini.evalExprCode, hPop, WasmMini.bool01, b] using h
            have hRest := ih (st := b :: st0) h'
            simp [WasmMini.execInstrsFuel, WasmMini.execInstrFuel, hPop, List.length, WasmMini.push, WasmMini.bool01]
            exact hRest
      · -- i64Ne
        cases hPop : WasmMini.pop2 st with
        | none =>
            simp [WasmMini.evalExprCode, hPop] at h
        | some val =>
            rcases val with ⟨v₂, v₁, st0⟩
            let b : Int := if v₁ = v₂ then 0 else 1
            have h' : WasmMini.evalExprCode rest σ (b :: st0) = some st' := by
              simpa [WasmMini.evalExprCode, hPop, WasmMini.bool01, b, ne_eq] using h
            have hRest := ih (st := b :: st0) h'
            simp [WasmMini.execInstrsFuel, WasmMini.execInstrFuel, hPop, List.length, WasmMini.push, WasmMini.bool01, ne_eq]
            exact hRest
      · -- i64Eqz
        cases hPop : WasmMini.pop1 st with
        | none =>
            simp [WasmMini.evalExprCode, hPop] at h
        | some val =>
            rcases val with ⟨v, st0⟩
            let b : Int := if v = 0 then 1 else 0
            have h' : WasmMini.evalExprCode rest σ (b :: st0) = some st' := by
              simpa [WasmMini.evalExprCode, hPop, WasmMini.bool01, b] using h
            have hRest := ih (st := b :: st0) h'
            simp [WasmMini.execInstrsFuel, WasmMini.execInstrFuel, hPop, List.length, WasmMini.push, WasmMini.bool01]
            exact hRest
      · -- i64ExtendI32u
        simp [WasmMini.evalExprCode] at h
        have hRest := ih (st := st) h
        simp [WasmMini.execInstrsFuel, WasmMini.execInstrFuel, List.length, hRest]
      · -- if_
        simp [WasmMini.evalExprCode] at h
      · -- block
        simp [WasmMini.evalExprCode] at h
      · -- loop
        simp [WasmMini.evalExprCode] at h
      · -- br
        simp [WasmMini.evalExprCode] at h
      · -- return_
        simp [WasmMini.evalExprCode] at h

private theorem evalExprCode_compileCondToI32 (Γ : MiniC.TyEnv) (σ : MiniC.TotalStore)
    (hσ : MiniC.StoreRespects Γ σ) {e : MiniC.Expr}
    (ht : MiniC.HasType Γ e .bool) (st : WasmMini.Stack) :
    WasmMini.evalExprCode (compileCondToI32 e) σ st =
      some ((if MiniC.Expr.eval e σ ≠ 0 then 1 else 0) :: st) := by
  have hExpr :=
    ToWasmMini.compileExpr_correct (Γ := Γ) (σ := σ) (hσ := hσ) (e := e) (τ := .bool) (ht := ht) (st := st)
  simp [compileCondToI32, evalExprCode_append, hExpr, WasmMini.evalExprCode, WasmMini.pop2, WasmMini.bool01]

/-! ## Fuel monotonicity (needed for list composition in a few spots) -/

mutual
  private theorem execInstrsFuel_succ {fuel : Nat} {is : List WasmMini.Instr}
      {σ : WasmMini.Store} {st : WasmMini.Stack} {out : WasmMini.Outcome} :
      WasmMini.execInstrsFuel fuel is σ st = some out →
      WasmMini.execInstrsFuel (fuel + 1) is σ st = some out := by
    cases fuel with
    | zero =>
        intro h
        simp [WasmMini.execInstrsFuel] at h
    | succ fuel =>
        intro h
        cases is with
        | nil =>
            simp [WasmMini.execInstrsFuel] at h
            cases h
            simp [WasmMini.execInstrsFuel]
        | cons i is =>
            -- Expand the smaller-fuel run.
            cases h0 : WasmMini.execInstrFuel fuel i σ st with
            | none =>
                simp [WasmMini.execInstrsFuel, h0] at h
            | some out0 =>
                cases out0 with
                | normal σ1 st1 =>
                    have hTail : WasmMini.execInstrsFuel fuel is σ1 st1 = some out := by
                      -- `execInstrsFuel` continues on the tail when the head is normal
                      simpa [WasmMini.execInstrsFuel, h0] using h
                    have h0' : WasmMini.execInstrFuel (fuel + 1) i σ st = some (.normal σ1 st1) :=
                      execInstrFuel_succ (fuel := fuel) (i := i) (σ := σ) (st := st) (out := .normal σ1 st1) (by
                        simpa using h0)
                    have hTail' : WasmMini.execInstrsFuel (fuel + 1) is σ1 st1 = some out :=
                      execInstrsFuel_succ (fuel := fuel) (is := is) (σ := σ1) (st := st1) (out := out) hTail
                    simp [WasmMini.execInstrsFuel, h0', hTail']
                | br l σ1 st1 =>
                    have : out = .br l σ1 st1 := by
                      simpa [eq_comm, WasmMini.execInstrsFuel, h0] using h
                    subst this
                    have h0' : WasmMini.execInstrFuel (fuel + 1) i σ st = some (.br l σ1 st1) :=
                      execInstrFuel_succ (fuel := fuel) (i := i) (σ := σ) (st := st) (out := .br l σ1 st1) (by
                        simpa using h0)
                    simp [WasmMini.execInstrsFuel, h0']
                | returned v =>
                    have : out = .returned v := by
                      simpa [eq_comm, WasmMini.execInstrsFuel, h0] using h
                    subst this
                    have h0' : WasmMini.execInstrFuel (fuel + 1) i σ st = some (.returned v) :=
                      execInstrFuel_succ (fuel := fuel) (i := i) (σ := σ) (st := st) (out := .returned v) (by
                        simpa using h0)
                    simp [WasmMini.execInstrsFuel, h0']

  private theorem execInstrFuel_succ {fuel : Nat} {i : WasmMini.Instr}
      {σ : WasmMini.Store} {st : WasmMini.Stack} {out : WasmMini.Outcome} :
      WasmMini.execInstrFuel fuel i σ st = some out →
      WasmMini.execInstrFuel (fuel + 1) i σ st = some out := by
    cases fuel with
    | zero =>
        intro h
        simp [WasmMini.execInstrFuel] at h
    | succ fuel =>
        intro h
        cases i with
        | i64Const n =>
            simpa [WasmMini.execInstrFuel] using h
        | localGet x =>
            simpa [WasmMini.execInstrFuel] using h
        | localSet x =>
            simpa [WasmMini.execInstrFuel] using h
        | i64Add =>
            simpa [WasmMini.execInstrFuel] using h
        | i64Sub =>
            simpa [WasmMini.execInstrFuel] using h
        | i64Mul =>
            simpa [WasmMini.execInstrFuel] using h
        | i64LeS =>
            simpa [WasmMini.execInstrFuel] using h
        | i64Eq =>
            simpa [WasmMini.execInstrFuel] using h
        | i64Ne =>
            simpa [WasmMini.execInstrFuel] using h
        | i64Eqz =>
            simpa [WasmMini.execInstrFuel] using h
        | i64ExtendI32u =>
            simpa [WasmMini.execInstrFuel] using h
        | br lbl =>
            simpa [WasmMini.execInstrFuel] using h
        | return_ =>
            simpa [WasmMini.execInstrFuel] using h
        | if_ then_ else_ =>
            cases hPop : WasmMini.pop1 st with
            | none =>
                simp [WasmMini.execInstrFuel, hPop] at h
            | some cst =>
                rcases cst with ⟨c, st'⟩
                -- Use the shape `if c = 0 then else_ else then_`, since simp often rewrites the
                -- semantics' `if c ≠ 0` into this form.
                let branch : List WasmMini.Instr := if c = 0 then else_ else then_
                cases hBranch0 : WasmMini.execInstrsFuel fuel branch σ st' with
                | none =>
                    have hFalse : False := by
                      have h' := h
                      simp [WasmMini.execInstrFuel, hPop, branch, hBranch0] at h'
                    cases hFalse
                | some out0 =>
                    have hEq :
                        (match out0, hBranch0 with
                          | Outcome.normal σ' st'', _ => some (Outcome.normal σ' st'')
                          | Outcome.br l σ' st'', _ => some (Outcome.br l σ' st'')
                          | Outcome.returned v, _ => some (Outcome.returned v)) =
                          some out := by
                      have hBind0 :
                          ((WasmMini.execInstrsFuel fuel branch σ st').bind fun __do_lift =>
                              match __do_lift with
                              | Outcome.normal σ' st'' => some (Outcome.normal σ' st'')
                              | Outcome.br l σ' st'' => some (Outcome.br l σ' st'')
                              | Outcome.returned v => some (Outcome.returned v)) =
                            some out := by
                        simpa [WasmMini.execInstrFuel, hPop, branch] using h
                      have hBind1 := hBind0
                      rw [hBranch0] at hBind1
                      have hBind2 :
                          ((some out0).bind fun __do_lift =>
                              match __do_lift with
                              | Outcome.normal σ' st'' => some (Outcome.normal σ' st'')
                              | Outcome.br l σ' st'' => some (Outcome.br l σ' st'')
                              | Outcome.returned v => some (Outcome.returned v)) =
                            some out := by
                        exact hBind1
                      cases out0 <;> simpa using hBind2
                    have hout : out0 = out := by
                      have hSome : some out0 = some out := by
                        cases out0 <;> exact hEq
                      exact Option.some.inj hSome
                    have hBranch1 :
                        WasmMini.execInstrsFuel (fuel + 1) branch σ st' = some out0 :=
                      execInstrsFuel_succ (fuel := fuel) (is := branch) (σ := σ) (st := st') (out := out0) (by
                        simpa using hBranch0)
                    simp [WasmMini.execInstrFuel, hPop, branch, hBranch1, hout]
                    cases out <;> rfl
        | block lbl body =>
            cases hBody0 : WasmMini.execInstrsFuel fuel body σ st with
            | none =>
                simp [WasmMini.execInstrFuel, hBody0] at h
            | some out0 =>
                have hBody1 :
                    WasmMini.execInstrsFuel (fuel + 1) body σ st = some out0 :=
                  execInstrsFuel_succ (fuel := fuel) (is := body) (σ := σ) (st := st) (out := out0) (by
                    simpa using hBody0)
                cases out0 with
                | normal σ' st' =>
                    have : out = .normal σ' st' := by
                      simpa [eq_comm, WasmMini.execInstrFuel, hBody0] using h
                    subst this
                    simp [WasmMini.execInstrFuel, hBody1]
                | returned v =>
                    have : out = .returned v := by
                      simpa [eq_comm, WasmMini.execInstrFuel, hBody0] using h
                    subst this
                    simp [WasmMini.execInstrFuel, hBody1]
                | br l σ' st' =>
                    by_cases hl : l = lbl
                    · have : out = .normal σ' st' := by
                        simpa [eq_comm, WasmMini.execInstrFuel, hBody0, hl] using h
                      subst this
                      simp [WasmMini.execInstrFuel, hBody1, hl]
                    · have hEq :
                          (if l = lbl then some (Outcome.normal σ' st') else some (Outcome.br l σ' st')) =
                            some out := by
                          simpa [WasmMini.execInstrFuel, hBody0] using h
                      have hEq' : some (Outcome.br l σ' st') = some out := by
                        simpa [hl] using hEq
                      have : out = .br l σ' st' := by
                        have : Outcome.br l σ' st' = out := Option.some.inj hEq'
                        simpa using this.symm
                      subst this
                      simp [WasmMini.execInstrFuel, hBody1, hl]
        | loop lbl body =>
            cases hBody0 : WasmMini.execInstrsFuel fuel body σ st with
            | none =>
                have hFalse : False := by
                  have h' := h
                  simp [WasmMini.execInstrFuel, hBody0] at h'
                cases hFalse
            | some out0 =>
                have hBody1 :
                    WasmMini.execInstrsFuel (fuel + 1) body σ st = some out0 :=
                  execInstrsFuel_succ (fuel := fuel) (is := body) (σ := σ) (st := st) (out := out0) (by
                    simpa using hBody0)
                cases out0 with
                | normal σ' st' =>
                    have : out = .normal σ' st' := by
                      simpa [eq_comm, WasmMini.execInstrFuel, hBody0] using h
                    subst this
                    simp [WasmMini.execInstrFuel, hBody1]
                | returned v =>
                    have : out = .returned v := by
                      simpa [eq_comm, WasmMini.execInstrFuel, hBody0] using h
                    subst this
                    simp [WasmMini.execInstrFuel, hBody1]
                | br l σ' st' =>
                    by_cases hl : l = lbl
                    · have hRec :
                        WasmMini.execInstrFuel fuel (.loop lbl body) σ' st' = some out := by
                        simpa [WasmMini.execInstrFuel, hBody0, hl] using h
                      have hRec' :=
                        execInstrFuel_succ (fuel := fuel) (i := .loop lbl body) (σ := σ') (st := st') (out := out) hRec
                      simpa [WasmMini.execInstrFuel, hBody1, hl] using hRec'
                    · have hEq :
                          (if l = lbl then execInstrFuel fuel (Instr.loop lbl body) σ' st' else
                              some (Outcome.br l σ' st')) =
                            some out := by
                          simpa [WasmMini.execInstrFuel, hBody0] using h
                      have hEq' : some (Outcome.br l σ' st') = some out := by
                        simpa [hl] using hEq
                      have : out = .br l σ' st' := by
                        have : Outcome.br l σ' st' = out := Option.some.inj hEq'
                        simpa using this.symm
                      subst this
                      simp [WasmMini.execInstrFuel, hBody1, hl]
end

private theorem execInstrsFuel_mono {fuel₁ fuel₂ : Nat} (h : fuel₁ ≤ fuel₂)
    {is : List WasmMini.Instr} {σ : WasmMini.Store} {st : WasmMini.Stack} {out : WasmMini.Outcome} :
    WasmMini.execInstrsFuel fuel₁ is σ st = some out →
    WasmMini.execInstrsFuel fuel₂ is σ st = some out := by
  rcases Nat.exists_eq_add_of_le h with ⟨k, rfl⟩
  clear h
  intro hrun
  revert hrun
  induction k with
  | zero =>
      intro hrun
      simpa using hrun
  | succ k ih =>
      intro hrun
      have hprev : WasmMini.execInstrsFuel (fuel₁ + k) is σ st = some out :=
        ih hrun
      simpa [Nat.add_assoc] using
        execInstrsFuel_succ (fuel := fuel₁ + k) (is := is) (σ := σ) (st := st) (out := out) hprev

private theorem execInstrFuel_mono {fuel₁ fuel₂ : Nat} (h : fuel₁ ≤ fuel₂)
    {i : WasmMini.Instr} {σ : WasmMini.Store} {st : WasmMini.Stack} {out : WasmMini.Outcome} :
    WasmMini.execInstrFuel fuel₁ i σ st = some out →
    WasmMini.execInstrFuel fuel₂ i σ st = some out := by
  rcases Nat.exists_eq_add_of_le h with ⟨k, rfl⟩
  clear h
  intro hrun
  revert hrun
  induction k with
  | zero =>
      intro hrun
      simpa using hrun
  | succ k ih =>
      intro hrun
      have hprev : WasmMini.execInstrFuel (fuel₁ + k) i σ st = some out :=
        ih hrun
      simpa [Nat.add_assoc] using
        execInstrFuel_succ (fuel := fuel₁ + k) (i := i) (σ := σ) (st := st) (out := out) hprev

/-! ## List composition lemmas -/

/-- Compose fuel-bounded runs across list append (normal prefix). -/
theorem execInstrsFuel_append_of_normal
    {fuel₁ fuel₂ : Nat} {as bs : List WasmMini.Instr}
    {σ : WasmMini.Store} {st : WasmMini.Stack}
    {σ' : WasmMini.Store} {st' : WasmMini.Stack} {out : WasmMini.Outcome}
    (hA : WasmMini.execInstrsFuel fuel₁ as σ st = some (.normal σ' st'))
    (hB : WasmMini.execInstrsFuel fuel₂ bs σ' st' = some out) :
    WasmMini.execInstrsFuel (fuel₁ + fuel₂) (as ++ bs) σ st = some out := by
  induction as generalizing σ st σ' st' fuel₁ with
  | nil =>
      cases fuel₁ with
      | zero => simp [WasmMini.execInstrsFuel] at hA
      | succ fuel₁ =>
          -- `as = []` forces `σ' = σ` and `st' = st`.
          simp [WasmMini.execInstrsFuel] at hA
          rcases hA with ⟨rfl, rfl⟩
          -- lift `hB` to the larger fuel
          have hB' :=
            execInstrsFuel_mono (fuel₁ := fuel₂) (fuel₂ := fuel₁.succ + fuel₂) (Nat.le_add_left fuel₂ fuel₁.succ)
              (is := bs) (σ := σ) (st := st) (out := out) hB
          simpa [List.nil_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hB'
  | cons a as ih =>
      cases fuel₁ with
      | zero => simp [WasmMini.execInstrsFuel] at hA
      | succ fuel₁ =>
          -- Invert the prefix run to get a normal head and a normal tail.
            cases h0 : WasmMini.execInstrFuel fuel₁ a σ st with
            | none =>
                simp [WasmMini.execInstrsFuel, h0] at hA
            | some out0 =>
                cases out0 with
                | normal σ1 st1 =>
                    have hTail : WasmMini.execInstrsFuel fuel₁ as σ1 st1 = some (.normal σ' st') := by
                      simpa [WasmMini.execInstrsFuel, h0] using hA
                    -- lift the head to the larger fuel so we can run `bs` afterwards
                    have h0' : WasmMini.execInstrFuel (fuel₁ + fuel₂) a σ st = some (.normal σ1 st1) :=
                      execInstrFuel_mono (fuel₁ := fuel₁) (fuel₂ := fuel₁ + fuel₂) (Nat.le_add_right fuel₁ fuel₂)
                        (i := a) (σ := σ) (st := st) (out := .normal σ1 st1) (by simpa using h0)
                    have hTailAll :=
                      ih (σ := σ1) (st := st1) (σ' := σ') (st' := st') (fuel₁ := fuel₁) hTail hB
                    -- rebuild the run on the appended list
                    have hCons :
                        WasmMini.execInstrsFuel ((fuel₁ + fuel₂) + 1) (a :: as ++ bs) σ st = some out := by
                      simp [WasmMini.execInstrsFuel, h0', hTailAll]
                    simpa [List.cons_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hCons
                | br l σ1 st1 =>
                    -- prefix cannot end in `br` if it ended in normal
                    simp [WasmMini.execInstrsFuel, h0] at hA
                | returned v =>
                    simp [WasmMini.execInstrsFuel, h0] at hA

/-- If a prefix run returns, appending more instructions does not change the returned value. -/
theorem execInstrsFuel_append_of_returned_left
    {fuel : Nat} {as bs : List WasmMini.Instr}
    {σ : WasmMini.Store} {st : WasmMini.Stack} {v : Int}
    (hA : WasmMini.execInstrsFuel fuel as σ st = some (.returned v)) :
    WasmMini.execInstrsFuel fuel (as ++ bs) σ st = some (.returned v) := by
  induction as generalizing σ st fuel with
  | nil =>
      cases fuel with
      | zero => simp [WasmMini.execInstrsFuel] at hA
      | succ fuel => simp [WasmMini.execInstrsFuel] at hA
  | cons a as ih =>
      cases fuel with
      | zero => simp [WasmMini.execInstrsFuel] at hA
      | succ fuel =>
          cases h0 : WasmMini.execInstrFuel fuel a σ st with
          | none =>
              simp [WasmMini.execInstrsFuel, h0] at hA
          | some out0 =>
              cases out0 with
              | returned v0 =>
                  have : v0 = v := by simpa [WasmMini.execInstrsFuel, h0] using hA
                  subst this
                  simp [WasmMini.execInstrsFuel, h0, List.cons_append]
              | normal σ1 st1 =>
                  have hTail : WasmMini.execInstrsFuel fuel as σ1 st1 = some (.returned v) := by
                    simpa [WasmMini.execInstrsFuel, h0] using hA
                  have ihRet := ih (σ := σ1) (st := st1) (fuel := fuel) hTail
                  simpa [WasmMini.execInstrsFuel, h0, List.cons_append] using ihRet
              | br l σ1 st1 =>
                  simp [WasmMini.execInstrsFuel, h0] at hA

/-! ## Main statement-level correctness theorem (total MiniC semantics, with while) -/

theorem compileStmt_execFuel_correct
    (Γ : MiniC.TyEnv) (σ : MiniC.TotalStore) (st : WasmMini.Stack)
    (hσ : MiniC.StoreRespects Γ σ) {s : MiniC.Stmt} (hs : HasTypeStmt Γ s) :
    ∀ fuel,
      (∀ {σ' : MiniC.TotalStore},
        MiniC.Stmt.execFuel fuel s σ = some (.normal σ') →
          ∃ fuelW,
            WasmMini.execInstrsFuel fuelW (compileStmt s) σ st = some (.normal σ' st) ∧
            MiniC.StoreRespects Γ σ') ∧
      (∀ {v : Int},
        MiniC.Stmt.execFuel fuel s σ = some (.returned v) →
          ∃ fuelW,
            WasmMini.execInstrsFuel fuelW (compileStmt s) σ st = some (.returned v)) := by
  intro fuel
  induction fuel generalizing σ st s with
  | zero =>
      constructor
      · intro σ' h
        simp [MiniC.Stmt.execFuel] at h
      · intro v h
        simp [MiniC.Stmt.execFuel] at h
  | succ fuel ih =>
      constructor
      · intro σ' hExec
        cases hs with
        | skip =>
            simp [MiniC.Stmt.execFuel] at hExec
            cases hExec
            refine ⟨1, ?_, hσ⟩
            simp [compileStmt, WasmMini.execInstrsFuel]
        | ret he =>
            rename_i e τ
            simp [MiniC.Stmt.execFuel] at hExec
        | assign hx he =>
            rename_i x rhs τ
            -- assignment always returns normal
            simp [MiniC.Stmt.execFuel] at hExec
            cases hExec
            -- compute rhs value
            have hEvalExpr :
                WasmMini.evalExprCode (compileExpr rhs) σ st =
                  some (MiniC.Expr.eval rhs σ :: st) :=
              ToWasmMini.compileExpr_correct (Γ := Γ) (σ := σ) (hσ := hσ) (e := rhs) (τ := _)
                (ht := he) (st := st)
            have hPrefix :
                WasmMini.execInstrsFuel ((compileExpr rhs).length + 1) (compileExpr rhs) σ st =
                  some (.normal σ (MiniC.Expr.eval rhs σ :: st)) :=
              execInstrsFuel_of_evalExprCode (h := hEvalExpr)
            -- execute the trailing `localSet`
            have hSet :
                WasmMini.execInstrsFuel 2 [WasmMini.Instr.localSet x] σ (MiniC.Expr.eval rhs σ :: st) =
                  some (.normal (WasmMini.Store.update σ x (MiniC.Expr.eval rhs σ)) st) := by
              simp [WasmMini.execInstrsFuel, WasmMini.execInstrFuel, WasmMini.pop1]
            -- compose
            have hAll :
                WasmMini.execInstrsFuel (((compileExpr rhs).length + 1) + 2)
                  (compileStmt (.assign x rhs)) σ st =
                  some (.normal (fun y => if y = x then MiniC.Expr.eval rhs σ else σ y) st) := by
              -- `Store.update` is definitionally the same update used by MiniC total semantics.
              simpa [compileStmt, WasmMini.Store.update, Nat.add_assoc] using
                execInstrsFuel_append_of_normal (hA := hPrefix) (hB := hSet)
            -- finish
            refine ⟨((compileExpr rhs).length + 1) + 2, ?_, ?_⟩
            · simpa [compileStmt] using hAll
            · exact storeRespects_update (Γ := Γ) (σ := σ) (hσ := hσ) (x := x) (e := rhs) (τ := _)
                hx he
        | seq hs₁ hs₂ =>
            rename_i s₁ s₂
            -- Invert the MiniC execution by case-splitting on `s₁.execFuel`.
            cases h1 : MiniC.Stmt.execFuel fuel s₁ σ with
            | none =>
                have hFalse : False := by
                  have hExec' := hExec
                  simp [MiniC.Stmt.execFuel, h1] at hExec'
                exact False.elim hFalse
            | some r1 =>
                cases r1 with
                | returned v =>
                    have hFalse : False := by
                      have hExec' := hExec
                      simp [MiniC.Stmt.execFuel, h1] at hExec'
                    exact False.elim hFalse
                | normal σ1 =>
                    have h2 : MiniC.Stmt.execFuel fuel s₂ σ1 = some (.normal σ') := by
                      simpa [MiniC.Stmt.execFuel, h1] using hExec
                    rcases (ih (σ := σ) (st := st) hσ (s := s₁) hs₁).1 (σ' := σ1) h1 with
                      ⟨fuelW1, hW1, hσ1⟩
                    rcases (ih (σ := σ1) (st := st) hσ1 (s := s₂) hs₂).1 (σ' := σ') h2 with
                      ⟨fuelW2, hW2, hσ'⟩
                    have hAll := execInstrsFuel_append_of_normal (hA := hW1) (hB := hW2)
                    refine ⟨fuelW1 + fuelW2, ?_, hσ'⟩
                    simpa [compileStmt, Nat.add_assoc] using hAll
        | if_ hc ht he =>
            rename_i c t e
            -- Evaluate the condition.
            have hCondEval :=
              evalExprCode_compileCondToI32 (Γ := Γ) (σ := σ) (hσ := hσ) (e := c) (ht := hc) (st := st)
            by_cases hcnz : MiniC.Expr.eval c σ ≠ 0
            · -- then-branch
              simp [MiniC.Stmt.execFuel, hcnz] at hExec
              rcases (ih (σ := σ) (st := st) hσ (s := t) ht).1 (σ' := σ') hExec with
                ⟨fuelT, hWT, hσ'⟩
              have hPref :
                  WasmMini.execInstrsFuel ((compileCondToI32 c).length + 1) (compileCondToI32 c) σ st =
                    some (.normal σ ((if MiniC.Expr.eval c σ ≠ 0 then 1 else 0) :: st)) :=
                execInstrsFuel_of_evalExprCode (h := hCondEval)
              have hIf :
                  WasmMini.execInstrsFuel (fuelT + 2)
                    [WasmMini.Instr.if_ (compileStmt t) (compileStmt e)] σ (1 :: st) =
                      some (.normal σ' st) := by
                simp [WasmMini.execInstrsFuel, WasmMini.execInstrFuel, WasmMini.pop1, hWT]
              have hAll :=
                execInstrsFuel_append_of_normal (hA := (by simpa [hcnz] using hPref)) (hB := hIf)
              refine ⟨((compileCondToI32 c).length + 1) + (fuelT + 2), ?_, hσ'⟩
              simpa [compileStmt, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hAll
            · -- else-branch
              simp [MiniC.Stmt.execFuel, hcnz] at hExec
              rcases (ih (σ := σ) (st := st) hσ (s := e) he).1 (σ' := σ') hExec with
                ⟨fuelE, hWE, hσ'⟩
              have hPref :
                  WasmMini.execInstrsFuel ((compileCondToI32 c).length + 1) (compileCondToI32 c) σ st =
                    some (.normal σ ((if MiniC.Expr.eval c σ ≠ 0 then 1 else 0) :: st)) :=
                execInstrsFuel_of_evalExprCode (h := hCondEval)
              have hIf :
                  WasmMini.execInstrsFuel (fuelE + 2)
                    [WasmMini.Instr.if_ (compileStmt t) (compileStmt e)] σ (0 :: st) =
                      some (.normal σ' st) := by
                simp [WasmMini.execInstrsFuel, WasmMini.execInstrFuel, WasmMini.pop1, hWE]
              have hAll :=
                execInstrsFuel_append_of_normal (hA := (by simpa [hcnz] using hPref)) (hB := hIf)
              refine ⟨((compileCondToI32 c).length + 1) + (fuelE + 2), ?_, hσ'⟩
              simpa [compileStmt, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hAll
        | while_ hc hb =>
            rename_i c b
            -- Unfold the MiniC while execution.
            by_cases hcz : MiniC.Expr.eval c σ = 0
            · -- loop exits immediately
              simp [MiniC.Stmt.execFuel, hcz] at hExec
              cases hExec
              -- Show the compiled block/loop exits via `br "exit"`.
              have hCondEval :=
                evalExprCode_compileCondToI32 (Γ := Γ) (σ := σ) (hσ := hσ) (e := c) (ht := hc) (st := st)
              have hCondExec :
                  WasmMini.execInstrsFuel ((compileCondToI32 c).length + 1) (compileCondToI32 c) σ st =
                    some (.normal σ (0 :: st)) := by
                have := execInstrsFuel_of_evalExprCode (h := hCondEval)
                simpa [hcz] using this
              -- Assemble one iteration of the loop body.
              have hIf :
                  WasmMini.execInstrsFuel 4
                    [WasmMini.Instr.if_ (compileStmt b ++ [WasmMini.Instr.br "loop"]) ([WasmMini.Instr.br "exit"])] σ
                    (0 :: st) = some (.br "exit" σ st) := by
                simp [WasmMini.execInstrsFuel, WasmMini.execInstrFuel, WasmMini.pop1]
              have hBody :
                  WasmMini.execInstrsFuel (((compileCondToI32 c).length + 1) + 4)
                    (compileCondToI32 c ++
                      [WasmMini.Instr.if_ (compileStmt b ++ [WasmMini.Instr.br "loop"]) ([WasmMini.Instr.br "exit"])])
                    σ st = some (.br "exit" σ st) :=
                execInstrsFuel_append_of_normal (hA := hCondExec) (hB := hIf)
              -- Loop propagates `br exit`, block catches it, list returns normal.
              refine ⟨(((compileCondToI32 c).length + 1) + 4) + 4, ?_, hσ⟩
              -- Use `simp` to execute the outer structured control.
              simp [compileStmt, WasmMini.execInstrsFuel, WasmMini.execInstrFuel, hBody]
            · -- loop continues at least one iteration
              have hcnz : MiniC.Expr.eval c σ ≠ 0 := hcz
              -- Unfold the while, since the condition is nonzero.
              simp [MiniC.Stmt.execFuel, hcz] at hExec
              -- Inspect body execution.
              cases hBodyMini : MiniC.Stmt.execFuel fuel b σ with
              | none =>
                  have hFalse : False := by
                    have hExec' := hExec
                    simp [hBodyMini] at hExec'
                  exact False.elim hFalse
              | some r =>
                  cases r with
                  | returned v =>
                      have hFalse : False := by
                        have hExec' := hExec
                        simp [hBodyMini] at hExec'
                      exact False.elim hFalse
                  | normal σ1 =>
                      have hWhileMini : MiniC.Stmt.execFuel fuel (.while c b) σ1 = some (.normal σ') := by
                        simpa [hBodyMini] using hExec
                      -- establish store respects for σ1 from body correctness
                      rcases (ih (σ := σ) (st := st) hσ (s := b) hb).1 (σ' := σ1) hBodyMini with
                        ⟨fuelB, hWB, hσ1⟩
                      -- execute body ++ [br loop] -> br loop
                      have hBr :
                          WasmMini.execInstrsFuel 2 [WasmMini.Instr.br "loop"] σ1 st =
                            some (.br "loop" σ1 st) := by
                        simp [WasmMini.execInstrsFuel, WasmMini.execInstrFuel]
                      have hBodyBr :
                          WasmMini.execInstrsFuel (fuelB + 2) (compileStmt b ++ [WasmMini.Instr.br "loop"]) σ st =
                            some (.br "loop" σ1 st) := by
                        -- First run body to normal, then br.
                        have hAll := execInstrsFuel_append_of_normal (hA := hWB) (hB := hBr)
                        simpa [Nat.add_assoc] using hAll
                      -- cond + if picks then-branch and yields br loop
                      have hCondEval :=
                        evalExprCode_compileCondToI32 (Γ := Γ) (σ := σ) (hσ := hσ) (e := c) (ht := hc) (st := st)
                      have hCondExec :
                          WasmMini.execInstrsFuel ((compileCondToI32 c).length + 1) (compileCondToI32 c) σ st =
                            some (.normal σ (1 :: st)) := by
                        have := execInstrsFuel_of_evalExprCode (h := hCondEval)
                        simpa [hcnz] using this
                      have hIfThen :
                          WasmMini.execInstrsFuel ((fuelB + 2) + 2)
                            [WasmMini.Instr.if_ (compileStmt b ++ [WasmMini.Instr.br "loop"]) ([WasmMini.Instr.br "exit"])]
                            σ (1 :: st) = some (.br "loop" σ1 st) := by
                        simp [WasmMini.execInstrsFuel, WasmMini.execInstrFuel, WasmMini.pop1, hBodyBr]
                      have hLoopBody :
                          WasmMini.execInstrsFuel (((compileCondToI32 c).length + 1) + ((fuelB + 2) + 2))
                            (compileCondToI32 c ++
                              [WasmMini.Instr.if_ (compileStmt b ++ [WasmMini.Instr.br "loop"]) ([WasmMini.Instr.br "exit"])])
                            σ st = some (.br "loop" σ1 st) :=
                        execInstrsFuel_append_of_normal (hA := hCondExec) (hB := hIfThen)
                      -- Now use loop semantics: br loop triggers recursion; apply IH for the rest of the loop.
                      rcases (ih (σ := σ1) (st := st) hσ1 (s := .while c b) (HasTypeStmt.while_ hc hb)).1
                          (σ' := σ') hWhileMini with ⟨fuelWrec, hWrec, hσ'⟩
                      -- Extract from the recursive run (at `σ1`) enough information to drive the *next* loop call.
                      let fuelStep : Nat := ((compileCondToI32 c).length + 1) + ((fuelB + 2) + 2)
                      let loopBody : List WasmMini.Instr :=
                        compileCondToI32 c ++
                          [WasmMini.Instr.if_ (compileStmt b ++ [WasmMini.Instr.br "loop"])
                              ([WasmMini.Instr.br "exit"])]
                      let loopInstr : WasmMini.Instr := WasmMini.Instr.loop "loop" loopBody
                      let blockInstr : WasmMini.Instr := WasmMini.Instr.block "exit" [loopInstr]

                      have hLoopBodyStep : WasmMini.execInstrsFuel fuelStep loopBody σ st = some (.br "loop" σ1 st) := by
                        simpa [fuelStep, loopBody] using hLoopBody

                      have hWrec0 : WasmMini.execInstrsFuel fuelWrec [blockInstr] σ1 st = some (.normal σ' st) := by
                        simpa [compileStmt, fuelStep, loopBody, loopInstr, blockInstr] using hWrec

                      have hLoopRec0 :
                          ∃ fuelRec0,
                            (WasmMini.execInstrFuel fuelRec0 loopInstr σ1 st = some (.normal σ' st) ∨
                              WasmMini.execInstrFuel fuelRec0 loopInstr σ1 st = some (.br "exit" σ' st)) := by
                        cases fuelWrec with
                        | zero =>
                            have hFalse : False := by
                              have h := hWrec0
                              simp [WasmMini.execInstrsFuel] at h
                            exact False.elim hFalse
                        | succ fuelWrec1 =>
                            cases fuelWrec1 with
                            | zero =>
                                -- `execInstrsFuel 1 [blockInstr]` must be `none`.
                                have hFalse : False := by
                                  have h := hWrec0
                                  simp [WasmMini.execInstrsFuel, WasmMini.execInstrFuel] at h
                                exact False.elim hFalse
                            | succ fuelBlock =>
                                -- First, invert the singleton-list run to obtain the block run.
                                have hDo :
                                    (do
                                      let out ← WasmMini.execInstrFuel (fuelBlock + 1) blockInstr σ1 st
                                      match out with
                                      | .normal σ2 st2 => WasmMini.execInstrsFuel (fuelBlock + 1) [] σ2 st2
                                      | .br l σ2 st2 => some (.br l σ2 st2)
                                      | .returned v => some (.returned v)) =
                                      some (.normal σ' st) := by
                                  simpa [WasmMini.execInstrsFuel] using hWrec0
                                cases hBlock0 : WasmMini.execInstrFuel (fuelBlock + 1) blockInstr σ1 st with
                                | none =>
                                    have : False := by
                                      have h' := hDo
                                      simp [hBlock0] at h'
                                    cases this
                                | some outBlock =>
                                    cases outBlock with
                                    | normal σ2 st2 =>
                                        have hTail :
                                            WasmMini.execInstrsFuel (fuelBlock + 1) [] σ2 st2 =
                                              some (.normal σ' st) := by
                                          simpa [hBlock0] using hDo
                                        have hEqSome :
                                            some (Outcome.normal σ2 st2) = some (Outcome.normal σ' st) := by
                                          simpa [WasmMini.execInstrsFuel] using hTail
                                        have hEqOut :
                                            WasmMini.Outcome.normal σ2 st2 = WasmMini.Outcome.normal σ' st :=
                                          Option.some.inj hEqSome
                                        cases hEqOut
                                        have hBlockRun :
                                            WasmMini.execInstrFuel (fuelBlock + 1) blockInstr σ1 st =
                                              some (.normal σ' st) := by
                                          simp [hBlock0]
                                        -- Now invert the block run to obtain either a normal or `br "exit"` result
                                        -- for the loop instruction (and then an instruction-level run).
                                        cases hLoopList : WasmMini.execInstrsFuel fuelBlock [loopInstr] σ1 st with
                                        | none =>
                                            have : False := by
                                              have h' := hBlockRun
                                              simp [WasmMini.execInstrFuel, blockInstr, hLoopList] at h'
                                            cases this
                                        | some outList =>
                                            have hBlockRun' := hBlockRun
                                            simp [WasmMini.execInstrFuel, blockInstr, hLoopList] at hBlockRun'
                                            -- `outList` must be either `.normal σ' st` or `.br "exit" σ' st`.
                                            have hListRes :
                                                outList = (Outcome.normal σ' st) ∨ outList = (Outcome.br "exit" σ' st) := by
                                              cases outList with
                                              | normal σx stx =>
                                                  left
                                                  simpa using (Option.some.inj hBlockRun')
                                              | returned v =>
                                                  have : False := by
                                                    cases hBlockRun'
                                                  cases this
                                              | br l σx stx =>
                                                  by_cases hl : l = "exit"
                                                  · subst hl
                                                    right
                                                    have hEq : some (Outcome.normal σx stx) = some (Outcome.normal σ' st) := by
                                                      simpa using hBlockRun'
                                                    have hEqOut :
                                                        Outcome.normal σx stx = Outcome.normal σ' st :=
                                                      Option.some.inj hEq
                                                    cases hEqOut
                                                    rfl
                                                  · have : False := by
                                                      -- If `l ≠ "exit"`, block would return `br`, contradicting normal.
                                                      simp [hl] at hBlockRun'
                                                    cases this
                                            -- Now convert the singleton list result into an instruction result.
                                            cases fuelBlock with
                                            | zero =>
                                                have hFalse : False := by
                                                  have h := hLoopList
                                                  simp [WasmMini.execInstrsFuel] at h
                                                exact False.elim hFalse
                                            | succ fuelRec0 =>
                                                have hDoLoop :
                                                    (do
                                                      let out ← WasmMini.execInstrFuel fuelRec0 loopInstr σ1 st
                                                      match out with
                                                      | .normal σ2 st2 => WasmMini.execInstrsFuel fuelRec0 [] σ2 st2
                                                      | .br l σ2 st2 => some (.br l σ2 st2)
                                                      | .returned v => some (.returned v)) =
                                                      some outList := by
                                                  simpa [WasmMini.execInstrsFuel] using hLoopList
                                                cases hExecLoop : WasmMini.execInstrFuel fuelRec0 loopInstr σ1 st with
                                                | none =>
                                                    have : False := by
                                                      have h' := hDoLoop
                                                      simp [hExecLoop] at h'
                                                    cases this
                                                | some outI =>
                                                    cases hListRes with
                                                    | inl hNorm =>
                                                        subst hNorm
                                                        -- List returned normal, so the instruction must return normal too.
                                                        have : WasmMini.execInstrFuel fuelRec0 loopInstr σ1 st =
                                                            some (Outcome.normal σ' st) := by
                                                          cases outI with
                                                          | returned v =>
                                                              have h' := hDoLoop
                                                              simp [hExecLoop] at h'
                                                          | br l σ2 st2 =>
                                                              have h' := hDoLoop
                                                              simp [hExecLoop] at h'
                                                          | normal σ2 st2 =>
                                                              have hTailEq :
                                                                  WasmMini.execInstrsFuel fuelRec0 [] σ2 st2 =
                                                                    some (Outcome.normal σ' st) := by
                                                                have h' := hDoLoop
                                                                simp [hExecLoop] at h'
                                                                exact h'
                                                              cases fuelRec0 with
                                                              | zero =>
                                                                  -- impossible since `execInstrFuel 0 … = none`
                                                                  simp [WasmMini.execInstrFuel] at hExecLoop
                                                              | succ fuelRec0 =>
                                                                  have hEqSome :
                                                                      some (Outcome.normal σ2 st2) =
                                                                        some (Outcome.normal σ' st) := by
                                                                    simpa [WasmMini.execInstrsFuel] using hTailEq
                                                                  have hEqOut :
                                                                      Outcome.normal σ2 st2 = Outcome.normal σ' st :=
                                                                    Option.some.inj hEqSome
                                                                  cases hEqOut
                                                                  simpa using hExecLoop
                                                        exact ⟨fuelRec0, Or.inl this⟩
                                                    | inr hExit =>
                                                        subst hExit
                                                        -- List returned `br "exit"`, so the instruction returned that `br`.
                                                        have : WasmMini.execInstrFuel fuelRec0 loopInstr σ1 st =
                                                            some (Outcome.br "exit" σ' st) := by
                                                          cases outI with
                                                          | normal σ2 st2 =>
                                                              have h' := hDoLoop
                                                              simp [hExecLoop] at h'
                                                              -- `execInstrsFuel` on `[]` cannot produce a `br`.
                                                              cases fuelRec0 with
                                                              | zero =>
                                                                  simp [WasmMini.execInstrsFuel] at h'
                                                              | succ fuelRec0 =>
                                                                  simp [WasmMini.execInstrsFuel] at h'
                                                          | returned v =>
                                                              have h' := hDoLoop
                                                              simp [hExecLoop] at h'
                                                          | br l σ2 st2 =>
                                                              have h' := hDoLoop
                                                              simp [hExecLoop] at h'
                                                              -- `simp` reduces equality of `br` outcomes to field equalities.
                                                              rcases h' with ⟨hl, hσ, hst⟩
                                                              subst hl
                                                              subst hσ
                                                              subst hst
                                                              simpa using hExecLoop
                                                        exact ⟨fuelRec0, Or.inr this⟩
                                    | returned v =>
                                        have : False := by
                                          have h' := hDo
                                          simp [hBlock0] at h'
                                        cases this
                                    | br l σ2 st2 =>
                                        have : False := by
                                          have h' := hDo
                                          simp [hBlock0] at h'
                                        cases this

                      rcases hLoopRec0 with ⟨fuelRec0, hLoopRec0⟩
                      let fuelRec : Nat := Nat.max fuelRec0 fuelStep

                      have hLoopBodyLift :
                          WasmMini.execInstrsFuel fuelRec loopBody σ st = some (.br "loop" σ1 st) :=
                        execInstrsFuel_mono (fuel₁ := fuelStep) (fuel₂ := fuelRec) (Nat.le_max_right _ _)
                          (is := loopBody) (σ := σ) (st := st) (out := .br "loop" σ1 st) hLoopBodyStep

                      -- Execute the compiled while from `σ` at fuel `fuelRec + 4`:
                      -- the first iteration yields `br "loop"`, and the recursive loop call is provided by `hLoopRec0`.
                      refine ⟨fuelRec + 4, ?_, hσ'⟩
                      cases hLoopRec0 with
                      | inl hRecNorm =>
                          have hRecNorm' :
                              WasmMini.execInstrFuel fuelRec loopInstr σ1 st = some (.normal σ' st) :=
                            execInstrFuel_mono (fuel₁ := fuelRec0) (fuel₂ := fuelRec) (Nat.le_max_left _ _)
                              (i := loopInstr) (σ := σ1) (st := st) (out := .normal σ' st) hRecNorm
                          simp [compileStmt, loopBody, loopInstr, WasmMini.execInstrsFuel, WasmMini.execInstrFuel,
                            hLoopBodyLift, hRecNorm']
                      | inr hRecExit =>
                          have hRecExit' :
                              WasmMini.execInstrFuel fuelRec loopInstr σ1 st = some (.br "exit" σ' st) :=
                            execInstrFuel_mono (fuel₁ := fuelRec0) (fuel₂ := fuelRec) (Nat.le_max_left _ _)
                              (i := loopInstr) (σ := σ1) (st := st) (out := .br "exit" σ' st) hRecExit
                          simp [compileStmt, loopBody, loopInstr, WasmMini.execInstrsFuel, WasmMini.execInstrFuel,
                            hLoopBodyLift, hRecExit']
                      -- returned body is impossible since `hExec` produces a normal result
      · intro v hExec
        cases hs with
        | skip =>
            simp [MiniC.Stmt.execFuel] at hExec
        | ret he =>
            rename_i e τ
            simp [MiniC.Stmt.execFuel] at hExec
            cases hExec
            let v0 := MiniC.Expr.eval e σ
            have hEvalExpr :
                WasmMini.evalExprCode (compileExpr e) σ st = some (v0 :: st) :=
              ToWasmMini.compileExpr_correct (Γ := Γ) (σ := σ) (hσ := hσ) (e := e) (τ := _)
                (ht := he) (st := st)
            have hPrefix :
                WasmMini.execInstrsFuel ((compileExpr e).length + 1) (compileExpr e) σ st =
                  some (.normal σ (v0 :: st)) :=
              execInstrsFuel_of_evalExprCode (h := hEvalExpr)
            have hRet :
                WasmMini.execInstrsFuel 2 [WasmMini.Instr.return_] σ (v0 :: st) = some (.returned v0) := by
              simp [WasmMini.execInstrsFuel, WasmMini.execInstrFuel, WasmMini.pop1, v0]
            have hAll :=
              execInstrsFuel_append_of_normal (hA := hPrefix) (hB := hRet)
            refine ⟨((compileExpr e).length + 1) + 2, ?_⟩
            simpa [compileStmt, v0, Nat.add_assoc] using hAll
        | assign hx he =>
            rename_i x rhs τ
            simp [MiniC.Stmt.execFuel] at hExec
        | seq hs₁ hs₂ =>
            rename_i s₁ s₂
            -- Either s₁ returned, or s₁ normal and s₂ returned.
            simp [MiniC.Stmt.execFuel] at hExec
            cases h1 : MiniC.Stmt.execFuel fuel s₁ σ with
            | none =>
                have hFalse : False := by
                  have hExec' := hExec
                  simp [h1] at hExec'
                cases hFalse
            | some r1 =>
                cases r1 with
                | returned v1 =>
                    have hv1 : v1 = v := by
                      have hEq :
                          some (MiniC.ExecResultTotal.returned v1) =
                            some (MiniC.ExecResultTotal.returned v) := by
                        simpa [MiniC.Stmt.execFuel, h1] using hExec
                      have :
                          (MiniC.ExecResultTotal.returned v1) =
                            (MiniC.ExecResultTotal.returned v) := Option.some.inj hEq
                      cases this
                      rfl
                    rcases (ih (σ := σ) (st := st) hσ (s := s₁) hs₁).2 (v := v1) (by simpa using h1) with
                      ⟨fuelW, hW⟩
                    refine ⟨fuelW, ?_⟩
                    have hAll := execInstrsFuel_append_of_returned_left (bs := compileStmt s₂) (hA := hW)
                    simpa [compileStmt, hv1] using hAll
                  | normal σ1 =>
                      have hExec2 : MiniC.Stmt.execFuel fuel s₂ σ1 = some (.returned v) := by
                        simpa [MiniC.Stmt.execFuel, h1] using hExec
                      rcases (ih (σ := σ) (st := st) hσ (s := s₁) hs₁).1 (σ' := σ1) (by simpa using h1) with
                        ⟨fuelW1, hW1, hσ1⟩
                      rcases (ih (σ := σ1) (st := st) hσ1 (s := s₂) hs₂).2 (v := v) hExec2 with
                        ⟨fuelW2, hW2⟩
                      have hAll := execInstrsFuel_append_of_normal (hA := hW1) (hB := hW2)
                      refine ⟨fuelW1 + fuelW2, ?_⟩
                      simpa [compileStmt, Nat.add_assoc] using hAll
        | if_ hc ht he =>
            rename_i c t e
            have hCondEval :=
              evalExprCode_compileCondToI32 (Γ := Γ) (σ := σ) (hσ := hσ) (e := c) (ht := hc) (st := st)
            by_cases hcnz : MiniC.Expr.eval c σ ≠ 0
            · simp [MiniC.Stmt.execFuel, hcnz] at hExec
              rcases (ih (σ := σ) (st := st) hσ (s := t) ht).2 (v := v) hExec with ⟨fuelT, hWT⟩
              have hPref :
                  WasmMini.execInstrsFuel ((compileCondToI32 c).length + 1) (compileCondToI32 c) σ st =
                    some (.normal σ (1 :: st)) := by
                have h := execInstrsFuel_of_evalExprCode (h := hCondEval)
                simpa [hcnz] using h
              have hIf :
                  WasmMini.execInstrsFuel (fuelT + 2)
                    [WasmMini.Instr.if_ (compileStmt t) (compileStmt e)] σ (1 :: st) =
                      some (.returned v) := by
                simp [WasmMini.execInstrsFuel, WasmMini.execInstrFuel, WasmMini.pop1, hWT]
              have hAll := execInstrsFuel_append_of_normal (hA := hPref) (hB := hIf)
              refine ⟨((compileCondToI32 c).length + 1) + (fuelT + 2), ?_⟩
              simpa [compileStmt, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hAll
            · simp [MiniC.Stmt.execFuel, hcnz] at hExec
              rcases (ih (σ := σ) (st := st) hσ (s := e) he).2 (v := v) hExec with ⟨fuelE, hWE⟩
              have hPref :
                  WasmMini.execInstrsFuel ((compileCondToI32 c).length + 1) (compileCondToI32 c) σ st =
                    some (.normal σ (0 :: st)) := by
                have h := execInstrsFuel_of_evalExprCode (h := hCondEval)
                simpa [hcnz] using h
              have hIf :
                  WasmMini.execInstrsFuel (fuelE + 2)
                    [WasmMini.Instr.if_ (compileStmt t) (compileStmt e)] σ (0 :: st) =
                      some (.returned v) := by
                simp [WasmMini.execInstrsFuel, WasmMini.execInstrFuel, WasmMini.pop1, hWE]
              have hAll := execInstrsFuel_append_of_normal (hA := hPref) (hB := hIf)
              refine ⟨((compileCondToI32 c).length + 1) + (fuelE + 2), ?_⟩
              simpa [compileStmt, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hAll
        | while_ hc hb =>
            rename_i c b
            -- Returned from while can only come from the body.
            by_cases hcz : MiniC.Expr.eval c σ = 0
            · simp [MiniC.Stmt.execFuel, hcz] at hExec
            · simp [MiniC.Stmt.execFuel, hcz] at hExec
              cases hBodyMini : MiniC.Stmt.execFuel fuel b σ with
              | none =>
                  have hFalse : False := by
                    have hExec' := hExec
                    simp [hBodyMini] at hExec'
                  cases hFalse
              | some rBody =>
                  cases rBody with
                  | returned v1 =>
                      have hv1 : v1 = v := by
                        have hEq :
                            some (MiniC.ExecResultTotal.returned v1) =
                              some (MiniC.ExecResultTotal.returned v) := by
                          simpa [MiniC.Stmt.execFuel, hBodyMini] using hExec
                        have :
                            (MiniC.ExecResultTotal.returned v1) =
                              (MiniC.ExecResultTotal.returned v) := Option.some.inj hEq
                        cases this
                        rfl
                      -- Use the body IH and then mirror the loop/if plumbing.
                      rcases (ih (σ := σ) (st := st) hσ (s := b) hb).2 (v := v1) (by simpa using hBodyMini) with
                        ⟨fuelB, hWB⟩
                      have hBodyRet :
                          WasmMini.execInstrsFuel fuelB (compileStmt b ++ [WasmMini.Instr.br "loop"]) σ st =
                            some (.returned v1) :=
                        execInstrsFuel_append_of_returned_left (hA := hWB)
                      have hCondEval :=
                        evalExprCode_compileCondToI32 (Γ := Γ) (σ := σ) (hσ := hσ) (e := c) (ht := hc) (st := st)
                      have hPref :
                          WasmMini.execInstrsFuel ((compileCondToI32 c).length + 1) (compileCondToI32 c) σ st =
                            some (.normal σ (1 :: st)) := by
                        have h := execInstrsFuel_of_evalExprCode (h := hCondEval)
                        have hcnz : MiniC.Expr.eval c σ ≠ 0 := hcz
                        simpa [hcnz] using h
                      have hIf :
                          WasmMini.execInstrsFuel (fuelB + 2)
                            [WasmMini.Instr.if_ (compileStmt b ++ [WasmMini.Instr.br "loop"]) ([WasmMini.Instr.br "exit"])]
                            σ (1 :: st) = some (.returned v1) := by
                        simp [WasmMini.execInstrsFuel, WasmMini.execInstrFuel, WasmMini.pop1, hBodyRet]
                      have hLoopBody :=
                        execInstrsFuel_append_of_normal (hA := hPref) (hB := hIf)
                      let fuelStep := ((compileCondToI32 c).length + 1) + (fuelB + 2)
                      let loopBody :=
                        compileCondToI32 c ++
                          [WasmMini.Instr.if_ (compileStmt b ++ [WasmMini.Instr.br "loop"]) ([WasmMini.Instr.br "exit"])]
                      have hLoopBody' :
                          WasmMini.execInstrsFuel fuelStep loopBody σ st = some (.returned v1) := by
                        simpa [fuelStep, loopBody, Nat.add_assoc] using hLoopBody
                      let loopInstr : WasmMini.Instr := WasmMini.Instr.loop "loop" loopBody
                      have hLoopInstr :
                          WasmMini.execInstrFuel (fuelStep + 1) loopInstr σ st = some (.returned v1) := by
                        simp [loopInstr, WasmMini.execInstrFuel, hLoopBody']
                      have hLoopList :
                          WasmMini.execInstrsFuel (fuelStep + 2) [loopInstr] σ st = some (.returned v1) := by
                        simp [WasmMini.execInstrsFuel, hLoopInstr]
                      let blockInstr : WasmMini.Instr := WasmMini.Instr.block "exit" [loopInstr]
                      have hBlockInstr :
                          WasmMini.execInstrFuel (fuelStep + 3) blockInstr σ st = some (.returned v1) := by
                        simp [blockInstr, WasmMini.execInstrFuel, hLoopList]
                      have hBlockList :
                          WasmMini.execInstrsFuel (fuelStep + 4) [blockInstr] σ st = some (.returned v1) := by
                        simp [WasmMini.execInstrsFuel, hBlockInstr]
                      refine ⟨fuelStep + 4, ?_⟩
                      simpa [compileStmt, blockInstr, loopInstr, loopBody, fuelStep, hv1] using hBlockList
                  | normal σ1 =>
                      -- Returned happens in a later iteration.
                      have hWhileMini : MiniC.Stmt.execFuel fuel (.while c b) σ1 = some (.returned v) := by
                        simpa [MiniC.Stmt.execFuel, hBodyMini] using hExec
                      -- establish store respects for σ1 from body correctness
                      rcases (ih (σ := σ) (st := st) hσ (s := b) hb).1 (σ' := σ1) (by simpa using hBodyMini) with
                        ⟨fuelB, hWB, hσ1⟩
                      -- execute body ++ [br loop] -> br loop
                      have hBr :
                          WasmMini.execInstrsFuel 2 [WasmMini.Instr.br "loop"] σ1 st =
                            some (.br "loop" σ1 st) := by
                        simp [WasmMini.execInstrsFuel, WasmMini.execInstrFuel]
                      have hBodyBr :
                          WasmMini.execInstrsFuel (fuelB + 2) (compileStmt b ++ [WasmMini.Instr.br "loop"]) σ st =
                            some (.br "loop" σ1 st) := by
                        have hAll := execInstrsFuel_append_of_normal (hA := hWB) (hB := hBr)
                        simpa [Nat.add_assoc] using hAll
                      -- cond + if picks then-branch and yields br loop
                      have hCondEval :=
                        evalExprCode_compileCondToI32 (Γ := Γ) (σ := σ) (hσ := hσ) (e := c) (ht := hc) (st := st)
                      have hCondExec :
                          WasmMini.execInstrsFuel ((compileCondToI32 c).length + 1) (compileCondToI32 c) σ st =
                            some (.normal σ (1 :: st)) := by
                        have hTmp := execInstrsFuel_of_evalExprCode (h := hCondEval)
                        have hcnz : MiniC.Expr.eval c σ ≠ 0 := hcz
                        simpa [hcnz] using hTmp
                      have hIfThen :
                          WasmMini.execInstrsFuel ((fuelB + 2) + 2)
                            [WasmMini.Instr.if_ (compileStmt b ++ [WasmMini.Instr.br "loop"]) ([WasmMini.Instr.br "exit"])]
                            σ (1 :: st) = some (.br "loop" σ1 st) := by
                        simp [WasmMini.execInstrsFuel, WasmMini.execInstrFuel, WasmMini.pop1, hBodyBr]
                      have hLoopBody :
                          WasmMini.execInstrsFuel (((compileCondToI32 c).length + 1) + ((fuelB + 2) + 2))
                            (compileCondToI32 c ++
                              [WasmMini.Instr.if_ (compileStmt b ++ [WasmMini.Instr.br "loop"]) ([WasmMini.Instr.br "exit"])])
                            σ st = some (.br "loop" σ1 st) :=
                        execInstrsFuel_append_of_normal (hA := hCondExec) (hB := hIfThen)
                      -- Apply IH to the recursive while call.
                      rcases
                          (ih (σ := σ1) (st := st) hσ1 (s := .while c b) (HasTypeStmt.while_ hc hb)).2 (v := v)
                            hWhileMini with
                        ⟨fuelWrec, hWrec⟩

                      let fuelStep :=
                        ((compileCondToI32 c).length + 1) + ((fuelB + 2) + 2)
                      let loopBody :=
                        compileCondToI32 c ++
                          [WasmMini.Instr.if_ (compileStmt b ++ [WasmMini.Instr.br "loop"]) ([WasmMini.Instr.br "exit"])]
                      let loopInstr : WasmMini.Instr := WasmMini.Instr.loop "loop" loopBody
                      let blockInstr : WasmMini.Instr := WasmMini.Instr.block "exit" [loopInstr]

                      have hLoopBodyStep :
                          WasmMini.execInstrsFuel fuelStep loopBody σ st = some (.br "loop" σ1 st) := by
                        simpa [fuelStep, loopBody, Nat.add_assoc] using hLoopBody

                      have hWhileFromσ1 :
                          WasmMini.execInstrsFuel fuelWrec [blockInstr] σ1 st = some (.returned v) := by
                        simpa [compileStmt, blockInstr, loopInstr, loopBody] using hWrec

                      have hRecLoop0 : ∃ fuelLoop, WasmMini.execInstrFuel fuelLoop loopInstr σ1 st = some (.returned v) := by
                        cases fuelWrec with
                        | zero =>
                            have hFalse : False := by
                              have h := hWhileFromσ1
                              simp [WasmMini.execInstrsFuel] at h
                            exact False.elim hFalse
                        | succ fuelW1 =>
                            cases fuelW1 with
                            | zero =>
                                have hFalse : False := by
                                  have h := hWhileFromσ1
                                  simp [WasmMini.execInstrsFuel, WasmMini.execInstrFuel] at h
                                exact False.elim hFalse
                            | succ fuelBlock =>
                                have hDo :
                                    (do
                                      let out ← WasmMini.execInstrFuel (fuelBlock + 1) blockInstr σ1 st
                                      match out with
                                      | .normal σ2 st2 => WasmMini.execInstrsFuel (fuelBlock + 1) [] σ2 st2
                                      | .br l σ2 st2 => some (.br l σ2 st2)
                                      | .returned v2 => some (.returned v2)) =
                                      some (.returned v) := by
                                  simpa [WasmMini.execInstrsFuel] using hWhileFromσ1
                                cases hBlock : WasmMini.execInstrFuel (fuelBlock + 1) blockInstr σ1 st with
                                | none =>
                                    have hFalse : False := by
                                      have h := hDo
                                      simp [hBlock] at h
                                    exact False.elim hFalse
                                | some outBlock =>
                                    cases outBlock with
                                    | normal σ2 st2 =>
                                        have hFalse : False := by
                                          have h := hDo
                                          simp [hBlock, WasmMini.execInstrsFuel] at h
                                        exact False.elim hFalse
                                    | br l σ2 st2 =>
                                        have hFalse : False := by
                                          have h := hDo
                                          simp [hBlock] at h
                                        exact False.elim hFalse
                                    | returned v2 =>
                                        have hv2 : v2 = v := by
                                          have hEqOut : Outcome.returned v2 = Outcome.returned v :=
                                            Option.some.inj (by simpa [hBlock] using hDo)
                                          cases hEqOut
                                          rfl
                                        have hBlockReturned :
                                            WasmMini.execInstrFuel (fuelBlock + 1) blockInstr σ1 st =
                                              some (.returned v) := by
                                          simp [hBlock, hv2]
                                        -- `block` propagates returned results from its body.
                                        cases hList : WasmMini.execInstrsFuel fuelBlock [loopInstr] σ1 st with
                                        | none =>
                                            have : False := by
                                              have h' := hBlockReturned
                                              simp [WasmMini.execInstrFuel, blockInstr, hList] at h'
                                            cases this
                                        | some outList =>
                                            have hb := hBlockReturned
                                            cases outList with
                                            | normal σ2 st2 =>
                                                have hFalse : False := by
                                                  have h := hb
                                                  simp [WasmMini.execInstrFuel, blockInstr, hList] at h
                                                exact False.elim hFalse
                                            | br l σ2 st2 =>
                                                by_cases hl : l = "exit"
                                                · have hFalse : False := by
                                                    have h := hb
                                                    simp [WasmMini.execInstrFuel, blockInstr, hList, hl] at h
                                                  exact False.elim hFalse
                                                · have hFalse : False := by
                                                    have h := hb
                                                    simp [WasmMini.execInstrFuel, blockInstr, hList, hl] at h
                                                  exact False.elim hFalse
                                            | returned v3 =>
                                                have hv3 : v3 = v := by
                                                  have hb' := hb
                                                  simp [WasmMini.execInstrFuel, blockInstr, hList] at hb'
                                                  simpa using hb'
                                                have hLoopList :
                                                    WasmMini.execInstrsFuel fuelBlock [loopInstr] σ1 st =
                                                      some (.returned v) := by
                                                  simp [hList, hv3]
                                                cases fuelBlock with
                                                | zero =>
                                                    have hFalse : False := by
                                                      have h := hLoopList
                                                      simp [WasmMini.execInstrsFuel] at h
                                                    exact False.elim hFalse
                                                | succ fuelLoop =>
                                                    have hDoLoop :
                                                        (do
                                                          let out ← WasmMini.execInstrFuel fuelLoop loopInstr σ1 st
                                                          match out with
                                                          | .normal σ2 st2 => WasmMini.execInstrsFuel fuelLoop [] σ2 st2
                                                          | .br l σ2 st2 => some (.br l σ2 st2)
                                                          | .returned v4 => some (.returned v4)) =
                                                          some (.returned v) := by
                                                      simpa [WasmMini.execInstrsFuel] using hLoopList
                                                    cases hExec : WasmMini.execInstrFuel fuelLoop loopInstr σ1 st with
                                                    | none =>
                                                        have hFalse : False := by
                                                          have h := hDoLoop
                                                          simp [hExec] at h
                                                        exact False.elim hFalse
                                                    | some outI =>
                                                        cases outI with
                                                        | normal σ2 st2 =>
                                                            have h' := hDoLoop
                                                            simp [hExec] at h'
                                                            cases fuelLoop with
                                                            | zero =>
                                                                simp [WasmMini.execInstrsFuel] at h'
                                                            | succ fuelLoop' =>
                                                                simp [WasmMini.execInstrsFuel] at h'
                                                        | br l σ2 st2 =>
                                                            have hFalse : False := by
                                                              have h := hDoLoop
                                                              simp [hExec] at h
                                                            exact False.elim hFalse
                                                        | returned v4 =>
                                                            have hv4 : v4 = v := by
                                                              have hEqOut : Outcome.returned v4 = Outcome.returned v :=
                                                                Option.some.inj (by simpa [hExec] using hDoLoop)
                                                              cases hEqOut
                                                              rfl
                                                            refine ⟨fuelLoop, ?_⟩
                                                            simp [hExec, hv4]
                      rcases hRecLoop0 with ⟨fuelLoop, hRecLoop0⟩

                      let fuelRec : Nat := Nat.max fuelStep fuelLoop
                      have hLoopBodyLift :
                          WasmMini.execInstrsFuel fuelRec loopBody σ st = some (.br "loop" σ1 st) :=
                        execInstrsFuel_mono (fuel₁ := fuelStep) (fuel₂ := fuelRec) (Nat.le_max_left _ _)
                          (is := loopBody) (σ := σ) (st := st) (out := .br "loop" σ1 st) hLoopBodyStep
                      have hRecLoop :
                          WasmMini.execInstrFuel fuelRec loopInstr σ1 st = some (.returned v) :=
                        execInstrFuel_mono (fuel₁ := fuelLoop) (fuel₂ := fuelRec) (Nat.le_max_right _ _)
                          (i := loopInstr) (σ := σ1) (st := st) (out := .returned v) hRecLoop0

                      have hLoopFromσ :
                          WasmMini.execInstrFuel (fuelRec + 1) loopInstr σ st = some (.returned v) := by
                        simp [loopInstr, WasmMini.execInstrFuel, hLoopBodyLift, hRecLoop]
                      have hLoopListFromσ :
                          WasmMini.execInstrsFuel (fuelRec + 2) [loopInstr] σ st = some (.returned v) := by
                        simp [WasmMini.execInstrsFuel, hLoopFromσ]
                      have hBlockFromσ :
                          WasmMini.execInstrFuel (fuelRec + 3) blockInstr σ st = some (.returned v) := by
                        simp [blockInstr, WasmMini.execInstrFuel, hLoopListFromσ]
                      have hBlockListFromσ :
                          WasmMini.execInstrsFuel (fuelRec + 4) [blockInstr] σ st = some (.returned v) := by
                        simp [WasmMini.execInstrsFuel, hBlockFromσ]

                      refine ⟨fuelRec + 4, ?_⟩
                      simpa [compileStmt, blockInstr, loopInstr, loopBody] using hBlockListFromσ

end ToWasmMini
end MiniC
end HeytingLean
