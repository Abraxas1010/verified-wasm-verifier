import HeytingLean.MiniC.Syntax
import HeytingLean.WasmMini.Syntax

namespace HeytingLean
namespace MiniC
namespace ToWasmMini

open HeytingLean.MiniC
open HeytingLean.WasmMini

@[simp] private def structFieldSlot (name field : String) : String :=
  name ++ "$" ++ field

/-!
# HeytingLean.MiniC.ToWasmMini

MiniC → WasmMini compilation for the Phase-1 WASM backend.

Notes:
- Values are compiled to `i64` (`Int`) and booleans are encoded as `0/1`.
- The generated WasmMini uses only structured control flow (`if/block/loop/br/return`).
- This compiler is designed to be paired with `WasmMini.EmitWAT` for output and
  `WasmMini.Semantics` for Lean-level validation/proofs.
-/

def compileExpr : MiniC.Expr → List WasmMini.Instr
  | .intLit n => [.i64Const n]
  | .boolLit b => [.i64Const (if b then 1 else 0)]
  | .var x => [.localGet x]
  | .arrayLit _ => [.i64Const 0]
  | .arrayLength _ => [.i64Const 0]
  | .arrayIndex _ _ => [.i64Const 0]
  | .structLit _ _ => [.i64Const 0]
  | .fieldAccess obj field =>
      match obj with
      | .var name => [.localGet (structFieldSlot name field)]
      | _ => [.i64Const 0]
  | .add e₁ e₂ => compileExpr e₁ ++ compileExpr e₂ ++ [.i64Add]
  | .sub e₁ e₂ => compileExpr e₁ ++ compileExpr e₂ ++ [.i64Sub]
  | .mul e₁ e₂ => compileExpr e₁ ++ compileExpr e₂ ++ [.i64Mul]
  | .le e₁ e₂ => compileExpr e₁ ++ compileExpr e₂ ++ [.i64LeS, .i64ExtendI32u]
  | .eq e₁ e₂ => compileExpr e₁ ++ compileExpr e₂ ++ [.i64Eq, .i64ExtendI32u]
  | .not e => compileExpr e ++ [.i64Eqz, .i64ExtendI32u]
  | .and e₁ e₂ =>
      -- Boolean conjunction via multiplication (requires 0/1 encoding invariant).
      compileExpr e₁ ++ compileExpr e₂ ++ [.i64Mul]
  | .or e₁ e₂ =>
      -- Boolean disjunction via `(1 <= (a+b))` (requires 0/1 encoding invariant).
      [.i64Const 1] ++ compileExpr e₁ ++ compileExpr e₂ ++ [.i64Add, .i64LeS, .i64ExtendI32u]

/-- Convert a truthy i64 (nonzero) to an i32 condition via `x != 0`. -/
def compileCondToI32 (e : MiniC.Expr) : List WasmMini.Instr :=
  compileExpr e ++ [.i64Const 0, .i64Ne]

def compileStmt : MiniC.Stmt → List WasmMini.Instr
  | .skip => []
  | .assign x rhs => compileExpr rhs ++ [.localSet x]
  | .arrayUpdate _ _ _ => []
  | .structUpdate name field rhs => compileExpr rhs ++ [.localSet (structFieldSlot name field)]
  | .call _ _ ret => [.i64Const 0, .localSet ret]
  | .seq s₁ s₂ => compileStmt s₁ ++ compileStmt s₂
  | .if_ cond thenS elseS =>
      compileCondToI32 cond ++ [.if_ (compileStmt thenS) (compileStmt elseS)]
  | .while cond body =>
      -- Canonical structured loop:
      -- (block $exit
      --   (loop $loop
      --     <cond>; to i32;
      --     (if (then <body>; br $loop) (else br $exit))))
      [ .block "exit"
          [ .loop "loop"
              (compileCondToI32 cond ++
                [ .if_ (compileStmt body ++ [.br "loop"]) ([.br "exit"]) ])
          ]
      ]
  | .return e => compileExpr e ++ [.return_]

private def varsExpr : MiniC.Expr → List String
  | .var x => [x]
  | .intLit _ => []
  | .boolLit _ => []
  | .arrayLit _ => []
  | .arrayLength _ => []
  | .arrayIndex _ _ => []
  | .structLit _ _ => []
  | .fieldAccess obj field =>
      match obj with
      | .var name => [structFieldSlot name field]
      | _ => []
  | .add e₁ e₂ => varsExpr e₁ ++ varsExpr e₂
  | .sub e₁ e₂ => varsExpr e₁ ++ varsExpr e₂
  | .mul e₁ e₂ => varsExpr e₁ ++ varsExpr e₂
  | .le e₁ e₂ => varsExpr e₁ ++ varsExpr e₂
  | .eq e₁ e₂ => varsExpr e₁ ++ varsExpr e₂
  | .not e => varsExpr e
  | .and e₁ e₂ => varsExpr e₁ ++ varsExpr e₂
  | .or e₁ e₂ => varsExpr e₁ ++ varsExpr e₂

private def varsStmt : MiniC.Stmt → List String
  | .skip => []
  | .assign x rhs => x :: varsExpr rhs
  | .arrayUpdate name idx rhs => name :: (varsExpr idx ++ varsExpr rhs)
  | .structUpdate name field rhs => structFieldSlot name field :: varsExpr rhs
  | .call _ _ ret => [ret]
  | .seq s₁ s₂ => varsStmt s₁ ++ varsStmt s₂
  | .if_ cond thenS elseS => varsExpr cond ++ varsStmt thenS ++ varsStmt elseS
  | .while cond body => varsExpr cond ++ varsStmt body
  | .return e => varsExpr e

def locals (params : List String) (body : MiniC.Stmt) : List String :=
  (varsStmt body).eraseDups.filter (fun x => !(params.contains x))

def compileFun (fn : MiniC.Fun) : WasmMini.Fun :=
  { name := fn.name
    params := fn.params
    locals := locals fn.params fn.body
    body := compileStmt fn.body ++ [.i64Const 0, .return_] }

end ToWasmMini
end MiniC
end HeytingLean
