import HeytingLean.LeanCP.Lang.CSyntax

/-!
# LeanCP Rust Syntax — Deep Embedding

Rust-specific IR types. These are the target of C→Rust translation
and the source for Rust text emission.

Key differences from C IR:
- Explicit `unsafe` blocks for pointer operations
- `mut` annotations on mutable bindings
- No implicit int→bool conversion (Rust requires explicit comparison)
- Raw pointers (`*const T` / `*mut T`) for C pointer parity
- Unit `()` instead of void
-/

namespace HeytingLean.LeanCP.Rust

/-- Rust types. Maps from CType with Rust-specific adjustments. -/
inductive RustType where
  | i8 | i16 | i32 | i64
  | u8 | u16 | u32 | u64
  | f32 | f64
  | bool
  | unit
  | rawPtr : RustType → Bool → RustType  -- *const T or *mut T (Bool = mutable)
  | slice : RustType → RustType           -- &[T] / &mut [T]
  | array : RustType → Nat → RustType     -- [T; N]
  | namedStruct : String → RustType
  | namedEnum : String → RustType
  | usize
  deriving Repr, Inhabited

/-- Rust expressions. -/
inductive RustExpr where
  | var : String → RustExpr
  | intLit : Int → RustExpr
  | floatLit : Float → RustExpr
  | boolLit : Bool → RustExpr
  | nullPtr : RustType → RustExpr          -- std::ptr::null_mut::<T>()
  | sizeOf : RustType → RustExpr           -- std::mem::size_of::<T>()
  | cast : RustType → RustExpr → RustExpr  -- expr as T
  | binop : BinOp → RustExpr → RustExpr → RustExpr
  | unsafeDeref : RustExpr → RustExpr      -- unsafe { *ptr }
  | arrayAccess : RustExpr → RustExpr → RustExpr  -- unsafe { *ptr.add(idx) }
  | addrOf : String → Bool → RustExpr      -- &x or &mut x (Bool = mutable)
  | fieldAccess : RustExpr → String → RustExpr  -- unsafe { (*ptr).field }
  | call : String → List RustExpr → RustExpr
  deriving Repr, Inhabited

/-- Rust statements. -/
inductive RustStmt where
  | skip : RustStmt
  | letBind : String → RustType → RustExpr → Bool → RustStmt  -- let [mut] x: T = e;
  | assign : RustExpr → RustExpr → RustStmt
  | seq : RustStmt → RustStmt → RustStmt
  | ite : RustExpr → RustStmt → RustStmt → RustStmt
  | whileLoop : RustExpr → RustStmt → RustStmt
  | forRange : String → RustExpr → RustExpr → RustStmt → RustStmt
  | block : RustStmt → RustStmt
  | unsafeBlock : RustStmt → RustStmt       -- unsafe { ... }
  | ret : RustExpr → RustStmt
  | alloc : String → Nat → RustType → RustStmt  -- unsafe layout alloc
  | free : RustExpr → RustType → Nat → RustStmt  -- unsafe dealloc (layout-matched)
  | break_ : RustStmt
  | continue_ : RustStmt
  deriving Repr, Inhabited

/-- A Rust function declaration. -/
structure RustFunDecl where
  name : String
  params : List (String × RustType)
  retType : RustType := .i32
  isUnsafe : Bool := false
  body : RustStmt

/-- A Rust program (set of functions + main). -/
structure RustProgramDecl where
  defs : List RustFunDecl
  main : RustFunDecl

end HeytingLean.LeanCP.Rust
