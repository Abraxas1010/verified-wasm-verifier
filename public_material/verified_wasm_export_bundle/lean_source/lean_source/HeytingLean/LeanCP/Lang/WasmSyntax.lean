import HeytingLean.LeanCP.Lang.CSyntax

/-!
# LeanCP WebAssembly Syntax — Deep Embedding

Wasm IR types targeting the WebAssembly Text Format (WAT).
Wasm is a stack machine — no registers, no variables (only locals).
Key differences from C IR:
- Stack-based: operations push/pop from an implicit operand stack
- Typed locals: i32, i64, f32, f64 (no pointers — linear memory instead)
- Linear memory: flat byte array accessed via load/store instructions
- Structured control flow: block/loop/if/br (no goto)
-/

namespace HeytingLean.LeanCP.Wasm

/-- Wasm value types (MVP spec). -/
inductive WasmValType where
  | i32 | i64 | f32 | f64
  deriving Repr, Inhabited, DecidableEq

/-- Wasm instructions. -/
inductive WasmInstr where
  -- Constants
  | i32Const : Int → WasmInstr
  | i64Const : Int → WasmInstr
  | f32Const : Float → WasmInstr
  | f64Const : Float → WasmInstr
  -- Local variable ops
  | localGet : Nat → WasmInstr
  | localSet : Nat → WasmInstr
  | localTee : Nat → WasmInstr
  -- Arithmetic (i32)
  | i32Add | i32Sub | i32Mul | i32DivS | i32DivU | i32RemS | i32RemU
  | i32And | i32Or | i32Xor | i32Shl | i32ShrS | i32ShrU
  | i32Eqz | i32Eq | i32Ne | i32LtS | i32LtU | i32GtS | i32GtU
  | i32LeS | i32LeU | i32GeS | i32GeU
  -- Arithmetic (i64)
  | i64Add | i64Sub | i64Mul | i64DivS
  -- Arithmetic (f32/f64)
  | f32Add | f32Sub | f32Mul | f32Div
  | f64Add | f64Sub | f64Mul | f64Div
  -- Memory
  | i32Load : Nat → WasmInstr    -- offset
  | i32Store : Nat → WasmInstr   -- offset
  | i64Load : Nat → WasmInstr
  | i64Store : Nat → WasmInstr
  -- Control flow
  | block : List WasmInstr → WasmInstr
  | loop : List WasmInstr → WasmInstr
  | if_ : List WasmInstr → List WasmInstr → WasmInstr
  | br : Nat → WasmInstr          -- branch to label depth
  | brIf : Nat → WasmInstr
  | return_ : WasmInstr
  | call : Nat → WasmInstr        -- function index
  -- Misc
  | drop : WasmInstr
  | nop : WasmInstr
  | unreachable : WasmInstr
  deriving Repr, Inhabited

/-- A Wasm function. -/
structure WasmFunc where
  name : String
  params : List WasmValType
  results : List WasmValType
  locals : List WasmValType
  body : List WasmInstr

/-- A Wasm module. -/
structure WasmModule where
  funcs : List WasmFunc
  memoryPages : Nat := 1       -- linear memory size in 64KB pages
  exportedFuncs : List (String × Nat)  -- (export name, func index)

end HeytingLean.LeanCP.Wasm
