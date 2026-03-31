import HeytingLean.LeanCP.Core.Val
import HeytingLean.LeanCP.Core.HProp
import HeytingLean.LeanCP.Lang.StructLayout

/-!
# LeanCP C Syntax — Deep Embedding

A deep embedding of a C subset sufficient for LeetCode-style problems:
integers, pointers, structs with next/left/right/data fields, malloc/free, arrays.

Programs are Lean DATA structures, not Lean programs. This is necessary because
C's memory model (flat addressable memory with pointer arithmetic) is incompatible
with Lean's runtime.
-/

namespace HeytingLean.LeanCP

set_option maxHeartbeats 800000

/-- Integer signedness for the expanded C surface. -/
inductive Signedness where
  | Signed
  | Unsigned
  deriving DecidableEq, Repr, Inhabited

/-- Unsigned modulus for a machine integer size. -/
def uintModulus (sz : IntSize) : Nat :=
  Nat.shiftLeft 1 sz.bits

/-- Wrap an integer into the unsigned range for the given machine size. -/
def wrapUnsignedInt (sz : IntSize) (n : Int) : Int :=
  Int.ofNat (Int.emod n (Int.ofNat (uintModulus sz))).toNat

/-- Wrap an integer into the unsigned range as a natural number. -/
def wrapUnsignedNat (sz : IntSize) (n : Int) : Nat :=
  (Int.emod n (Int.ofNat (uintModulus sz))).toNat

/-- Wrap an integer into the signed two's-complement range for the given machine size. -/
def wrapSignedInt (sz : IntSize) (n : Int) : Int :=
  let modulus := Int.ofNat (uintModulus sz)
  let half := Int.ofNat (Nat.shiftLeft 1 (sz.bits - 1))
  let u := Int.emod n modulus
  if u < half then u else u - modulus

/-- Prototype bitwise semantics: interpret integers through their natural-number
projection, which gives honest unsigned-style behavior on nonnegative inputs. -/
def natBitwise (op : Nat → Nat → Nat) (a b : Int) : CVal :=
  .int (Int.ofNat (op (Int.toNat a) (Int.toNat b)))

/-- Promote two unsigned machine sizes to the smallest common super-size. -/
def promoteUIntSize : IntSize → IntSize → IntSize
  | .I64, _ => .I64
  | _, .I64 => .I64
  | .I32, _ => .I32
  | _, .I32 => .I32
  | .I16, _ => .I16
  | _, .I16 => .I16
  | .I8, .I8 => .I8

/-- Normalize two unsigned operands into the same promoted size. -/
def promoteUIntPair (a : Nat) (asz : IntSize) (b : Nat) (bsz : IntSize) : Nat × Nat × IntSize :=
  let sz := promoteUIntSize asz bsz
  (a % uintModulus sz, b % uintModulus sz, sz)

/-- Binary operators. -/
inductive BinOp where
  | add | sub | mul | div | mod
  | eq | ne | lt | le | gt | ge
  | and | or
  | bitAnd | bitOr | bitXor
  | shl | shr
  | lAnd | lOr
  deriving DecidableEq, Repr, Inhabited

private def boolResult (p : Prop) [Decidable p] : Option CVal :=
  some (.int (if p then 1 else 0))

private def evalIntArithmetic (op : BinOp) (a b : Int) : Option CVal :=
  match op with
  | .add => some (.int (a + b))
  | .sub => some (.int (a - b))
  | .mul => some (.int (a * b))
  | .div => if b ≠ 0 then some (.int (a / b)) else none
  | .mod => if b ≠ 0 then some (.int (a % b)) else none
  | .eq => boolResult (a = b)
  | .ne => boolResult (a ≠ b)
  | .lt => boolResult (a < b)
  | .le => boolResult (a ≤ b)
  | .gt => boolResult (a > b)
  | .ge => boolResult (a ≥ b)
  | .and => boolResult (a ≠ 0 ∧ b ≠ 0)
  | .or => boolResult (a ≠ 0 ∨ b ≠ 0)
  | .lAnd => boolResult (a ≠ 0 ∧ b ≠ 0)
  | .lOr => boolResult (a ≠ 0 ∨ b ≠ 0)
  | .bitAnd => some (natBitwise (· &&& ·) a b)
  | .bitOr => some (natBitwise (· ||| ·) a b)
  | .bitXor => some (natBitwise (· ^^^ ·) a b)
  | .shl => if 0 ≤ b then some (.int (Int.shiftLeft a (Int.toNat b))) else none
  | .shr => if 0 ≤ b then some (.int (Int.shiftRight a (Int.toNat b))) else none

private def evalUIntArithmetic (op : BinOp) (a : Nat) (asz : IntSize) (b : Nat) (bsz : IntSize) :
    Option CVal :=
  let (a', b', sz) := promoteUIntPair a asz b bsz
  let modulus := uintModulus sz
  match op with
  | .add => some (.uint ((a' + b') % modulus) sz)
  | .sub => some (.uint ((a' + modulus - b') % modulus) sz)
  | .mul => some (.uint ((a' * b') % modulus) sz)
  | .div => if b' ≠ 0 then some (.uint (a' / b') sz) else none
  | .mod => if b' ≠ 0 then some (.uint (a' % b') sz) else none
  | .eq => boolResult (a' = b')
  | .ne => boolResult (a' ≠ b')
  | .lt => boolResult (a' < b')
  | .le => boolResult (a' ≤ b')
  | .gt => boolResult (a' > b')
  | .ge => boolResult (a' ≥ b')
  | .and => boolResult (a' ≠ 0 ∧ b' ≠ 0)
  | .or => boolResult (a' ≠ 0 ∨ b' ≠ 0)
  | .lAnd => boolResult (a' ≠ 0 ∧ b' ≠ 0)
  | .lOr => boolResult (a' ≠ 0 ∨ b' ≠ 0)
  | .bitAnd => some (.uint (a' &&& b') sz)
  | .bitOr => some (.uint (a' ||| b') sz)
  | .bitXor => some (.uint (a' ^^^ b') sz)
  | .shl => some (.uint ((Nat.shiftLeft a' b') % modulus) sz)
  | .shr => some (.uint (Nat.shiftRight a' b') sz)

/-- C types (minimal subset). -/
inductive CType where
  | int : CType
  | intSized : Signedness → IntSize → CType
  | float : CType
  | double : CType
  | ptr : CType → CType
  | array : CType → Nat → CType
  | funcPtr : CType → List CType → CType
  | struct : String → CType
  | union : String → CType
  | enum : String → CType
  | typedef : String → CType
  | void : CType
  deriving Repr, Inhabited

noncomputable instance : DecidableEq CType := Classical.decEq _

/-- C expressions (deep embedding). -/
inductive CExpr where
  | var : String → CExpr
  | intLit : Int → CExpr
  | floatLit : Float → CExpr
  | null : CExpr
  | sizeOf : CType → CExpr
  | cast : CType → CExpr → CExpr
  | binop : BinOp → CExpr → CExpr → CExpr
  | deref : CExpr → CExpr              -- *p
  | arrayAccess : CExpr → CExpr → CExpr  -- arr[idx]
  | addrOf : String → CExpr            -- &x (only for variables)
  | fieldAccess : CExpr → String → CExpr  -- p->field
  | call : String → List CExpr → CExpr
  deriving Repr, Inhabited

/-- Size model for the current deep embedding. Ints, pointers, and function
pointers occupy one cell; arrays use contiguous cells; built-in structs consult
`StructLayout`; unknown structs conservatively occupy one cell. -/
def typeSize : CType → Nat
  | .int => 1
  | .intSized _ _ => 1
  | .float => 1
  | .double => 1
  | .ptr _ => 1
  | .array elem n => typeSize elem * n
  | .funcPtr _ _ => 1
  | .struct name =>
      match StructLayout.defaultRegistry name with
      | some layout => layout.blockSize
      | none => 1
  | .union name =>
      match StructLayout.defaultRegistry name with
      | some layout => layout.blockSize
      | none => 1
  | .enum _ => 1
  | .typedef _ => 1
  | .void => 0

/-- Is a value truthy (nonzero / non-null)? -/
def isTruthy : CVal → Bool
  | .int 0 => false
  | .int _ => true
  | .uint 0 _ => false
  | .uint _ _ => true
  | .float v => v != 0.0
  | .ptr _ _ => true
  | .null => false
  | .undef => false
  | .structVal _ => true
  | .unionVal _ _ => true

/-- Float-Float binary operations (operational, not IEEE-certified). Extracted
to keep `evalBinOp`'s top-level match small enough for Lean's equation
theorem generation (see leanprover/lean4#11546). -/
private def evalFloatArithmetic : BinOp → Float → Float → Option CVal
  | .add, a, b => some (.float (a + b))
  | .sub, a, b => some (.float (a - b))
  | .mul, a, b => some (.float (a * b))
  | .div, a, b => if b != 0.0 then some (.float (a / b)) else none
  | .eq, a, b => some (.int (if a == b then 1 else 0))
  | .ne, a, b => some (.int (if a == b then 0 else 1))
  | .lt, a, b => some (.int (if a < b then 1 else 0))
  | .le, a, b => some (.int (if a <= b then 1 else 0))
  | .gt, a, b => some (.int (if a > b then 1 else 0))
  | .ge, a, b => some (.int (if a >= b then 1 else 0))
  | _, _, _ => none

/-- Evaluate a binary operation on concrete values. Shared by static and dynamic evaluators. -/
def evalBinOp : BinOp → CVal → CVal → Option CVal
  | op, .int a, .int b => evalIntArithmetic op a b
  | op, .uint a sz, .uint b sz' => evalUIntArithmetic op a sz b sz'
  | op, .uint a _, .int b => evalIntArithmetic op (Int.ofNat a) b
  | op, .int a, .uint b _ => evalIntArithmetic op a (Int.ofNat b)
  -- Pointer arithmetic is defined only for nonnegative integer offsets.
  | .add, .ptr block offset, .int off =>
      CVal.ptrAddr <$> Addr.addOffset { block := block, offset := offset } off
  | .add, .int off, .ptr block offset =>
      CVal.ptrAddr <$> Addr.addOffset { block := block, offset := offset } off
  -- Logical ops use isTruthy (must precede float dispatch so and/or on float works)
  | .and, a, b => some (.int (if isTruthy a && isTruthy b then 1 else 0))
  | .or, a, b => some (.int (if isTruthy a || isTruthy b then 1 else 0))
  | .lAnd, a, b => some (.int (if isTruthy a && isTruthy b then 1 else 0))
  | .lOr, a, b => some (.int (if isTruthy a || isTruthy b then 1 else 0))
  -- Float dispatches (delegated to helpers to keep match small; see leanprover/lean4#11546)
  | op, .float a, .float b => evalFloatArithmetic op a b
  | op, .float a, .int b => evalFloatArithmetic op a (Float.ofInt b)
  | op, .int a, .float b => evalFloatArithmetic op (Float.ofInt a) b
  | .eq, .ptr ba oa, .ptr bb ob => some (.int (if ba = bb ∧ oa = ob then 1 else 0))
  | .ne, .ptr ba oa, .ptr bb ob => some (.int (if ba = bb ∧ oa = ob then 0 else 1))
  | .eq, .null, .null => some (.int 1)
  | .eq, .null, .ptr _ _ => some (.int 0)
  | .eq, .ptr _ _, .null => some (.int 0)
  | .ne, .null, .null => some (.int 0)
  | .ne, .null, .ptr _ _ => some (.int 1)
  | .ne, .ptr _ _, .null => some (.int 1)
  | _, _, _ => none

@[simp] theorem evalBinOp_and_eq_lAnd (a b : CVal) :
    evalBinOp .and a b = evalBinOp .lAnd a b := by
  cases a <;> cases b <;> rfl

@[simp] theorem evalBinOp_or_eq_lOr (a b : CVal) :
    evalBinOp .or a b = evalBinOp .lOr a b := by
  cases a <;> cases b <;> rfl

@[simp] theorem evalBinOp_lAnd_int_int (a b : Int) :
    evalBinOp .lAnd (.int a) (.int b) = some (.int (if a ≠ 0 ∧ b ≠ 0 then 1 else 0)) := by
  rfl

@[simp] theorem evalBinOp_lAnd_uint_uint (a b : Nat) (asz bsz : IntSize) :
    evalBinOp .lAnd (.uint a asz) (.uint b bsz) =
      some (.int (if a % uintModulus (promoteUIntSize asz bsz) ≠ 0 ∧
                      b % uintModulus (promoteUIntSize asz bsz) ≠ 0 then 1 else 0)) := by
  rfl

@[simp] theorem evalBinOp_lOr_int_int (a b : Int) :
    evalBinOp .lOr (.int a) (.int b) = some (.int (if a ≠ 0 ∨ b ≠ 0 then 1 else 0)) := by
  rfl

@[simp] theorem evalBinOp_lOr_uint_uint (a b : Nat) (asz bsz : IntSize) :
    evalBinOp .lOr (.uint a asz) (.uint b bsz) =
      some (.int (if a % uintModulus (promoteUIntSize asz bsz) ≠ 0 ∨
                      b % uintModulus (promoteUIntSize asz bsz) ≠ 0 then 1 else 0)) := by
  rfl

@[simp] theorem evalBinOp_eq_int_int (a b : Int) :
    evalBinOp .eq (.int a) (.int b) = some (.int (if a = b then 1 else 0)) := by
  rfl

@[simp] theorem evalBinOp_ne_int_int (a b : Int) :
    evalBinOp .ne (.int a) (.int b) = some (.int (if a ≠ b then 1 else 0)) := by
  rfl

@[simp] theorem evalBinOp_add_int_int (a b : Int) :
    evalBinOp .add (.int a) (.int b) = some (.int (a + b)) := by
  rfl

@[simp] theorem evalBinOp_sub_int_int (a b : Int) :
    evalBinOp .sub (.int a) (.int b) = some (.int (a - b)) := by
  rfl

@[simp] theorem evalBinOp_lt_int_int (a b : Int) :
    evalBinOp .lt (.int a) (.int b) = some (.int (if a < b then 1 else 0)) := by
  rfl

@[simp] theorem evalBinOp_gt_int_int (a b : Int) :
    evalBinOp .gt (.int a) (.int b) = some (.int (if a > b then 1 else 0)) := by
  rfl

@[simp] theorem evalBinOp_add_ptr_int (block : Block) (offset : Offset) (off : Int) :
    evalBinOp .add (.ptr block offset) (.int off) =
      CVal.ptrAddr <$> Addr.addOffset { block := block, offset := offset } off := by
  rfl

@[simp] theorem evalBinOp_add_int_ptr (off : Int) (block : Block) (offset : Offset) :
    evalBinOp .add (.int off) (.ptr block offset) =
      CVal.ptrAddr <$> Addr.addOffset { block := block, offset := offset } off := by
  rfl

/-- Field offsets are centralized here so semantics and WP stay aligned. -/
def fieldOffset : String → Nat :=
  StructLayout.defaultFieldOffset

/-- Evaluate the static fragment of C expressions with no env/heap dependency. -/
def evalStaticExpr : CExpr → Option CVal
  | .intLit n => some (.int n)
  | .floatLit v => some (.float v)
  | .null => some .null
  | .sizeOf ty => some (.int (Int.ofNat (typeSize ty)))
  | .cast ty e => do
      let v ← evalStaticExpr e
      match ty, v with
      | .int, .int n => some (.int n)
      | .intSized .Signed sz, .int n => some (.int (wrapSignedInt sz n))
      | .intSized .Unsigned sz, .int n => some (.uint (wrapUnsignedNat sz n) sz)
      | .int, .uint n _ => some (.int (Int.ofNat n))
      | .intSized .Signed sz, .uint n _ => some (.int (wrapSignedInt sz (Int.ofNat n)))
      | .intSized .Unsigned sz, .uint n _ => some (.uint (n % uintModulus sz) sz)
      | .int, .null => some (.int 0)
      | .int, .ptr _ offset => some (.int offset)
      | .intSized .Signed sz, .null => some (.int (wrapSignedInt sz 0))
      | .intSized .Unsigned sz, .null => some (.uint 0 sz)
      | .intSized .Signed sz, .ptr _ offset => some (.int (wrapSignedInt sz offset))
      | .intSized .Unsigned sz, .ptr _ offset =>
          some (.uint (wrapUnsignedNat sz offset) sz)
      | .ptr _, .int n =>
          if _h : 0 ≤ n then some (.ptr 0 n) else none
      | .ptr _, .uint n _ => some (.ptr 0 (Int.ofNat n))
      | .ptr _, .null => some .null
      | .ptr _, .ptr block offset => some (.ptr block offset)
      | .struct _, .ptr block offset => some (.ptr block offset)
      | .struct _, .null => some .null
      | .union _, .ptr block offset => some (.ptr block offset)
      | .union _, .null => some .null
      | .enum _, .int n => some (.int n)
      | .enum _, .uint n _ => some (.int (Int.ofNat n))
      | .enum _, .null => some (.int 0)
      | .typedef _, v => some v
      | .array _ _, .ptr block offset => some (.ptr block offset)
      | .array _ _, .null => some .null
      | .funcPtr _ _, .ptr block offset => some (.ptr block offset)
      | .funcPtr _ _, .null => some .null
      -- Float casts (operational, not IEEE-certified).
      | .float, .int n => some (.float (Float.ofInt n))
      | .float, .uint n _ => some (.float (Float.ofNat n))
      | .float, .float v => some (.float v)
      | .double, .int n => some (.float (Float.ofInt n))
      | .double, .uint n _ => some (.float (Float.ofNat n))
      | .double, .float v => some (.float v)
      | .int, .float v => some (.int (Int.ofNat v.toUInt64.toNat))
      | .intSized .Signed sz, .float v =>
          some (.int (wrapSignedInt sz (Int.ofNat v.toUInt64.toNat)))
      | .intSized .Unsigned sz, .float v =>
          some (.uint (v.toUInt64.toNat % uintModulus sz) sz)
      | .void, _ => some CVal.undef
      | _, .undef => some CVal.undef
      | _, _ => none
  | .binop op e1 e2 => do
      let v1 ← evalStaticExpr e1
      let v2 ← evalStaticExpr e2
      evalBinOp op v1 v2
  | _ => none

/-- C statements (deep embedding). -/
inductive CStmt where
  | skip : CStmt
  | assign : CExpr → CExpr → CStmt      -- lhs = rhs (includes *p = e)
  | seq : CStmt → CStmt → CStmt
  | ite : CExpr → CStmt → CStmt → CStmt
  | whileInv : CExpr → HProp → CStmt → CStmt  -- while with loop invariant
  | block : List (String × CType) → CStmt → CStmt
  | switch : CExpr → Int → CStmt → CStmt → CStmt
  | forLoop : CStmt → CExpr → CStmt → CStmt → CStmt
  | break : CStmt
  | continue : CStmt
  | ret : CExpr → CStmt
  | alloc : String → Nat → CStmt        -- x = malloc block with explicit cell count
  | free : CExpr → Nat → CStmt          -- free a block with explicit cell count
  | decl : String → CType → CStmt       -- local variable declaration

/-- Declare a list of locals by sequencing the existing `decl` form. -/
def declareBlock : List (String × CType) → CStmt
  | [] => .skip
  | (x, ty) :: rest => .seq (.decl x ty) (declareBlock rest)

/-- Build a multi-case switch as a right-nested chain of binary `switch`
constructors. This preserves a convenient list-shaped authoring surface without
making `CStmt` a nested inductive. -/
def switchMany (e : CExpr) (cases : List (Int × CStmt)) (default : CStmt) : CStmt :=
  match cases with
  | [] => default
  | (tag, body) :: rest => .switch e tag body (switchMany e rest default)

/-- Structured block desugaring used by the verification surfaces. The
operational semantics may refine scope restoration, but this provides the common
statement shape consumed by `swp` and related helper predicates. -/
def desugarBlock (decls : List (String × CType)) (body : CStmt) : CStmt :=
  .seq (declareBlock decls) body

/-- A C function with separation logic specification. -/
structure CFunSpec where
  name : String
  params : List (String × CType)
  retType : CType
  pre : HProp                             -- Require
  post : CVal → HProp                    -- Ensure (parameterized by return value)
  body : CStmt

/-- For-loop desugaring used by the proof surfaces. This matches the executable
semantics when the loop body does not use `continue`; that scope is recorded by
`NoContinue` below and made explicit in the corresponding theorem statements. -/
def desugarFor (init : CStmt) (cond : CExpr) (step body : CStmt) : CStmt :=
  .seq init (.whileInv cond HProp.htrue (.seq body step))

/-- Syntactic predicate excluding `continue`. Needed because direct for-loop
execution handles `continue` more precisely than the simple desugaring above. -/
def NoContinue : CStmt → Prop
  | .skip => True
  | .assign _ _ => True
  | .seq s1 s2 => NoContinue s1 ∧ NoContinue s2
  | .ite _ th el => NoContinue th ∧ NoContinue el
  | .whileInv _ _ body => NoContinue body
  | .block _ body => NoContinue body
  | .switch _ _ caseBody default => NoContinue caseBody ∧ NoContinue default
  | .forLoop init _ step body => NoContinue init ∧ NoContinue step ∧ NoContinue body
  | .break => True
  | .continue => False
  | .ret _ => True
  | .alloc _ _ => True
  | .free _ _ => True
  | .decl _ _ => True

end HeytingLean.LeanCP
