import HeytingLean.MiniC.Semantics
import HeytingLean.MiniC.ToC
import HeytingLean.LeanCP.Lang.CDecl

/-!
# MiniC -> LeanCP

Checked lowering from existing MiniC producers into the LeanCP-owned C syntax.
This makes the architectural split explicit:

- `MiniC -> tiny-C` remains the legacy narrow fragment
- widened ownership lives under `HeytingLean.LeanCP.Lang.*`

The bridge here is intentionally checked and fail-closed so unsupported MiniC
constructs do not masquerade as successful LeanCP compilation.
-/

namespace HeytingLean
namespace MiniC
namespace ToLeanCP

open HeytingLean.LeanCP

/-- MiniC's coarse types embedded into the LeanCP-owned C type surface. -/
def compileType : MiniC.Ty → LeanCP.CType
  | .int => .int
  | .bool => .int
  | .array elem len => .array (compileType elem) len
  | .struct name => .struct name

/-- Checked MiniC-expression lowering into LeanCP C expressions. -/
def compileExprChecked : MiniC.Expr → Except ToC.CompileError LeanCP.CExpr
  | .var x => .ok (.var x)
  | .intLit n => .ok (.intLit n)
  | .boolLit b => .ok (.intLit (if b then 1 else 0))
  | .arrayLit _ =>
      .error (.unsupportedExpr "array literals are not supported in the MiniC -> LeanCP bridge")
  | .arrayLength arr =>
      match arr with
      | .var name => .ok (.var (MiniC.arrayLengthSlot name))
      | _ =>
          .error (.unsupportedExpr
            "arrayLength requires a named array variable in the MiniC -> LeanCP bridge")
  | .arrayIndex arr idx =>
      return .arrayAccess (← compileExprChecked arr) (← compileExprChecked idx)
  | .structLit _ _ =>
      .error (.unsupportedExpr "struct literals are not supported in the MiniC -> LeanCP bridge")
  | .fieldAccess obj field =>
      return .fieldAccess (← compileExprChecked obj) field
  | .add e₁ e₂ => return .binop .add (← compileExprChecked e₁) (← compileExprChecked e₂)
  | .sub e₁ e₂ => return .binop .sub (← compileExprChecked e₁) (← compileExprChecked e₂)
  | .mul e₁ e₂ => return .binop .mul (← compileExprChecked e₁) (← compileExprChecked e₂)
  | .le e₁ e₂ => return .binop .le (← compileExprChecked e₁) (← compileExprChecked e₂)
  | .eq e₁ e₂ => return .binop .eq (← compileExprChecked e₁) (← compileExprChecked e₂)
  | .not e => return .binop .eq (← compileExprChecked e) (.intLit 0)
  | .and e₁ e₂ => return .binop .lAnd (← compileExprChecked e₁) (← compileExprChecked e₂)
  | .or e₁ e₂ => return .binop .lOr (← compileExprChecked e₁) (← compileExprChecked e₂)

/-- Checked MiniC-statement lowering into LeanCP C statements. -/
def compileStmtChecked : MiniC.Stmt → Except ToC.CompileError LeanCP.CStmt
  | .skip => .ok .skip
  | .assign name rhs => return .assign (.var name) (← compileExprChecked rhs)
  | .arrayUpdate name idx rhs =>
      return .assign (.arrayAccess (.var name) (← compileExprChecked idx)) (← compileExprChecked rhs)
  | .structUpdate name field rhs =>
      return .assign (.fieldAccess (.var name) field) (← compileExprChecked rhs)
  | .call fname args ret => do
      let args' ← args.mapM compileExprChecked
      pure (.assign (.var ret) (.call fname args'))
  | .seq s₁ s₂ => return .seq (← compileStmtChecked s₁) (← compileStmtChecked s₂)
  | .if_ cond then_ else_ =>
      return .ite (← compileExprChecked cond) (← compileStmtChecked then_) (← compileStmtChecked else_)
  | .while cond body =>
      return .whileInv (← compileExprChecked cond) HProp.htrue (← compileStmtChecked body)
  | .return val => return .ret (← compileExprChecked val)

/-- Checked MiniC-function lowering into a raw LeanCP-owned declaration.

MiniC functions do not currently carry parameter types, so the bridge defaults
their parameters to `.int` until a richer typed front-end is available. -/
def compileFunDeclChecked (fn : MiniC.Fun) : Except ToC.CompileError LeanCP.CFunDecl := do
  let body ← compileStmtChecked fn.body
  pure
    { name := fn.name
      params := fn.params.map (fun p => (p, LeanCP.CType.int))
      retType := .int
      body := body }

/-- Checked MiniC-program lowering into the LeanCP-owned declaration surface. -/
def compileProgramDeclChecked (prog : MiniC.Program) :
    Except ToC.CompileError LeanCP.CProgramDecl := do
  let defs ← prog.defs.mapM compileFunDeclChecked
  let main ← compileFunDeclChecked prog.main
  pure { defs := defs, main := main }

end ToLeanCP
end MiniC
end HeytingLean
