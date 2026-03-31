import HeytingLean.MiniC.Semantics
import HeytingLean.MiniC.ToWasmMini
import HeytingLean.MiniC.ToWasmMiniStmtCorrectness
import HeytingLean.WasmMini.Semantics

namespace HeytingLean
namespace MiniC
namespace ToWasmMini

open HeytingLean.WasmMini

/-!
# HeytingLean.MiniC.ToWasmMiniFunCorrectness

Function-level semantic preservation for the Phase-1 `MiniC → WasmMini` backend.

This file bridges the existing statement-level theorem
`compileStmt_execFuel_correct` to the function runner `WasmMini.runFun` for
compiled functions (`compileFun`).

Important:
- `MiniC.Stmt.execFuel` is the **total** MiniC semantics (booleans as 0/1).
- `compileFun` appends `i64.const 0; return` so that “no explicit return”
  results in `0` (this is a deliberate totalization in the compiled artifact).
-/

private theorem execInstrsFuel_tail_return0 (σ : WasmMini.Store) :
    WasmMini.execInstrsFuel 3 [WasmMini.Instr.i64Const 0, WasmMini.Instr.return_] σ [] =
      some (.returned 0) := by
  simp [WasmMini.execInstrsFuel, WasmMini.execInstrFuel, WasmMini.pop1, WasmMini.push]

theorem compileFun_runFun_correct_of_returned
    (Γ : MiniC.TyEnv) (fn : MiniC.Fun) (args : List Int) (σ : MiniC.TotalStore)
    (hbind : WasmMini.bindParams fn.params args = some σ)
    (hσ : MiniC.StoreRespects Γ σ) (hs : HasTypeStmt Γ fn.body) :
    ∀ fuel {v : Int},
      MiniC.Stmt.execFuel fuel fn.body σ = some (.returned v) →
        ∃ fuelW, WasmMini.runFun (compileFun fn) args (fuel := fuelW) = some v := by
  intro fuel v hExec
  -- Statement-level correctness gives a fuel for the compiled statement code.
  have hStmt := (compileStmt_execFuel_correct (Γ := Γ) (σ := σ) (st := []) hσ (s := fn.body) hs) fuel
  rcases hStmt.2 (v := v) hExec with ⟨fuelW, hW⟩

  -- Appending extra instructions after a `return` does not change the result.
  have hW' :
      WasmMini.execInstrsFuel fuelW (compileStmt fn.body ++ [WasmMini.Instr.i64Const 0, WasmMini.Instr.return_])
          σ [] =
        some (.returned v) :=
    execInstrsFuel_append_of_returned_left (bs := [WasmMini.Instr.i64Const 0, WasmMini.Instr.return_]) (hA := hW)

  refine ⟨fuelW, ?_⟩
  -- Unfold `runFun` and rewrite the parameter binding.
  simp [WasmMini.runFun, ToWasmMini.compileFun, hbind, hW']

theorem compileFun_runFun_correct_of_normal
    (Γ : MiniC.TyEnv) (fn : MiniC.Fun) (args : List Int) (σ : MiniC.TotalStore)
    (hbind : WasmMini.bindParams fn.params args = some σ)
    (hσ : MiniC.StoreRespects Γ σ) (hs : HasTypeStmt Γ fn.body) :
    ∀ fuel {σ' : MiniC.TotalStore},
      MiniC.Stmt.execFuel fuel fn.body σ = some (.normal σ') →
        ∃ fuelW, WasmMini.runFun (compileFun fn) args (fuel := fuelW) = some 0 := by
  intro fuel σ' hExec
  have hStmt := (compileStmt_execFuel_correct (Γ := Γ) (σ := σ) (st := []) hσ (s := fn.body) hs) fuel
  rcases hStmt.1 (σ' := σ') hExec with ⟨fuelW, hW, _hσ'⟩

  have hTail : WasmMini.execInstrsFuel 3 [WasmMini.Instr.i64Const 0, WasmMini.Instr.return_] σ' [] =
      some (.returned 0) :=
    execInstrsFuel_tail_return0 (σ := σ')

  have hAll :
      WasmMini.execInstrsFuel (fuelW + 3)
          (compileStmt fn.body ++ [WasmMini.Instr.i64Const 0, WasmMini.Instr.return_])
          σ [] =
        some (.returned 0) :=
    execInstrsFuel_append_of_normal (hA := hW) (hB := hTail)

  refine ⟨fuelW + 3, ?_⟩
  simp [WasmMini.runFun, ToWasmMini.compileFun, hbind, hAll]

end ToWasmMini
end MiniC
end HeytingLean
