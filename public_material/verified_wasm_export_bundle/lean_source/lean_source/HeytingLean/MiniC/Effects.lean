import HeytingLean.MiniC.Syntax
import HeytingLean.MiniC.Semantics
import HeytingLean.MiniC.ToC
import HeytingLean.C.Syntax

namespace HeytingLean
namespace MiniC
namespace Effects

/-- Flattened input-channel slot used by effect desugaring. -/
@[simp] def inputSlot (channel : String) : String :=
  "input$" ++ channel

/-- Flattened output-channel slot used by effect desugaring. -/
@[simp] def outputSlot (channel : String) : String :=
  "output$" ++ channel

/-- Read from an external input channel into a MiniC variable. -/
@[simp] def readInput (var channel : String) : Stmt :=
  .assign var (.var (inputSlot channel))

/-- Write a MiniC expression to an external output channel. -/
@[simp] def writeOutput (channel : String) (value : Expr) : Stmt :=
  .assign (outputSlot channel) value

/-- Convenience guard: every current output slot value is nonnegative. -/
def outputNonnegative (σ : Store) (channel : String) : Prop :=
  match lookup σ (outputSlot channel) with
  | some (.int n) => 0 ≤ n
  | _ => True

@[simp] theorem compileStmt_readInput (var channel : String) :
    ToC.compileStmt (readInput var channel) =
      C.CStmt.assign var (C.CExpr.var (inputSlot channel)) := by
  rfl

@[simp] theorem compileStmt_writeOutput (channel : String) (value : Expr) :
    ToC.compileStmt (writeOutput channel value) =
      C.CStmt.assign (outputSlot channel) (ToC.compileExpr value) := by
  rfl

@[simp] theorem execFuel_readInput_succ (fuel : Nat) (var channel : String)
    (σ : Store) (defs : List Fun := []) :
    execFuel (fuel + 1) (readInput var channel) σ defs =
      (lookup σ (inputSlot channel)).map (fun v => ExecResult.normal (update σ var v)) := by
  have hMap :
      (σ (inputSlot channel)).bind (fun v => some (ExecResult.normal (update σ var v))) =
        ((σ (inputSlot channel)).map (fun v => ExecResult.normal (update σ var v))) := by
    cases h : σ (inputSlot channel) <;> rfl
  simpa [readInput, execFuel, evalExpr, lookup] using hMap

@[simp] theorem execFuel_writeOutput_succ (fuel : Nat) (channel : String)
    (value : Expr) (σ : Store) (defs : List Fun := []) :
    execFuel (fuel + 1) (writeOutput channel value) σ defs =
      (evalExpr value σ).map (fun v => ExecResult.normal (update σ (outputSlot channel) v)) := by
  have hMap :
      (evalExpr value σ).bind (fun v => some (ExecResult.normal (update σ (outputSlot channel) v))) =
        ((evalExpr value σ).map (fun v => ExecResult.normal (update σ (outputSlot channel) v))) := by
    cases h : evalExpr value σ <;> rfl
  simpa [writeOutput, execFuel] using hMap

end Effects
end MiniC
end HeytingLean
