import HeytingLean.LeanCP.Lang.CSyntax
import HeytingLean.LeanCP.Lang.CDecl
import HeytingLean.LeanCP.Lang.RustSyntax

/-!
# LeanCP C-to-Rust Translation

Deterministic, pure translation from C IR types to Rust IR types.
Every CType/CExpr/CStmt has exactly one Rust translation.

All pointer operations are wrapped in `unsafe` — this is the C→Rust
semantic parity path. Safe Rust abstractions (ownership, borrowing)
are a different product, not this translator.

## Type environment threading

Block-scoped declarations are threaded as a type environment through
statement translation, enabling:
- Pointer-typed locals initialized with `null_mut` (not integer zero)
- Allocation element types derived from declaration types
- Deallocation layouts matched to allocation layouts
-/

namespace HeytingLean.LeanCP.CToRust

open HeytingLean.LeanCP
open HeytingLean.LeanCP.Rust

/-- Translate a CType to a RustType. -/
def translateType : CType → RustType
  | .int => .i32
  | .intSized .Signed .I8 => .i8
  | .intSized .Signed .I16 => .i16
  | .intSized .Signed .I32 => .i32
  | .intSized .Signed .I64 => .i64
  | .intSized .Unsigned .I8 => .u8
  | .intSized .Unsigned .I16 => .u16
  | .intSized .Unsigned .I32 => .u32
  | .intSized .Unsigned .I64 => .u64
  | .float => .f32
  | .double => .f64
  | .ptr inner => .rawPtr (translateType inner) true  -- *mut T
  | .array inner n => .array (translateType inner) n
  | .struct name => .namedStruct name
  | .union name => .namedStruct name  -- Rust unions are structurally similar
  | .enum name => .namedEnum name
  | .typedef name => .namedStruct name  -- treat as opaque named type
  | .void => .unit
  | .funcPtr _ _ => .usize  -- function pointers as opaque for now

/-- Type-aware default initializer for Rust local variable declarations.
    Pointers are initialized with `std::ptr::null_mut()`, not integer zero.
    Booleans are initialized with `false`. All numeric types use `0`. -/
def defaultInit : RustType → RustExpr
  | .rawPtr inner _ => .nullPtr inner
  | .bool => .boolLit false
  | _ => .intLit 0

/-- Look up a variable's pointer element type from a declaration environment.
    Returns the translated element type if the variable is declared as a pointer;
    falls back to `.i32` if not found or not a pointer type. -/
def lookupElemType (env : List (String × CType)) (x : String) : RustType :=
  match env.find? (fun entry => entry.1 == x) with
  | some (_, .ptr inner) => translateType inner
  | _ => .i32

/-- Translate a CExpr to a RustExpr. -/
partial def translateExpr : CExpr → RustExpr
  | .var x => .var x
  | .intLit n => .intLit n
  | .floatLit v => .floatLit v
  | .null => .nullPtr .unit
  | .sizeOf ty => .sizeOf (translateType ty)
  | .cast ty e => .cast (translateType ty) (translateExpr e)
  | .binop op e1 e2 => .binop op (translateExpr e1) (translateExpr e2)
  | .deref (.binop .add base offset) =>              -- *(ptr + n) → ptr.add(n)
      .arrayAccess (translateExpr base) (translateExpr offset)
  | .deref e => .unsafeDeref (translateExpr e)       -- *ptr
  | .arrayAccess a i => .arrayAccess (translateExpr a) (translateExpr i)
  | .addrOf x => .addrOf x true                      -- &mut x
  | .fieldAccess e f => .fieldAccess (translateExpr e) f
  | .call fn args => .call fn (args.map translateExpr)

/-- Translate a CStmt to a RustStmt.
    The `env` parameter carries block-scoped variable declarations for
    type-aware pointer initialization, allocation, and deallocation. -/
partial def translateStmt : List (String × CType) → CStmt → RustStmt
  | _, .skip => .skip
  | _, .ret e => .ret (translateExpr e)
  | _, .assign lhs rhs => .assign (translateExpr lhs) (translateExpr rhs)
  | env, .seq s1 s2 => .seq (translateStmt env s1) (translateStmt env s2)
  | env, .ite cond th el =>
      .ite (translateExpr cond) (translateStmt env th) (translateStmt env el)
  | env, .whileInv cond _inv body =>
      .whileLoop (translateExpr cond) (translateStmt env body)
  | env, .forLoop init cond step body =>
      .seq (translateStmt env init)
        (.whileLoop (translateExpr cond)
          (.seq (translateStmt env body) (translateStmt env step)))
  | env, .block decls body =>
      let newEnv := env ++ decls
      let letBinds := decls.map fun (x, ty) =>
        let rty := translateType ty
        RustStmt.letBind x rty (defaultInit rty) true
      let chain := letBinds.foldl (fun acc s => RustStmt.seq acc s) .skip
      .block (.seq chain (translateStmt newEnv body))
  | env, .alloc x cells =>
      .alloc x cells (lookupElemType env x)
  | env, .free e cells =>
      let elemTy := match e with
        | .var x => lookupElemType env x
        | _ => .i32
      .free (translateExpr e) elemTy cells
  | _, .decl x ty =>
      let rty := translateType ty
      .letBind x rty (defaultInit rty) true
  | _, .break => .break_
  | _, .continue => .continue_
  | env, .switch scrut tag caseBody default =>
      .ite (.binop .eq (translateExpr scrut) (.intLit tag))
        (translateStmt env caseBody)
        (translateStmt env default)

/-- Translate a CFunDecl to a RustFunDecl.
    Function parameters seed the type environment for body translation. -/
def translateFunDecl (f : CFunDecl) : RustFunDecl :=
  { name := f.name
    params := f.params.map fun (n, ty) => (n, translateType ty)
    retType := translateType f.retType
    isUnsafe := true  -- all C-translated functions are unsafe
    body := translateStmt f.params f.body }

/-- Translate a CProgramDecl to a RustProgramDecl. -/
def translateProgram (p : CProgramDecl) : RustProgramDecl :=
  { defs := p.defs.map translateFunDecl
    main := translateFunDecl p.main }

end HeytingLean.LeanCP.CToRust
