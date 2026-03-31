namespace HeytingLean
namespace WasmMini

/-!
# HeytingLean.WasmMini.Syntax

A tiny, structured WebAssembly-like instruction set sufficient for the Phase-1
MiniC backend. This is **not** the full WASM spec; it is only the subset we
emit in `HeytingLean.WasmMini.EmitWAT`.

Design goals:
- Values are modeled as `Int` (representing `i64`), with booleans encoded as `0/1`.
- Control flow is structured via `block/loop/if/br/return`.
- This IR is intended for proof-level reasoning and differential testing; it is
  *not* a bytecode format.
-/

abbrev Label := String

/-- Total store used by WasmMini execution (mirrors `MiniC.TotalStore`). -/
abbrev Store := String → Int

/-- Stack of runtime values (top at head). -/
abbrev Stack := List Int

inductive Instr where
  | i64Const (n : Int)
  | localGet (x : String)
  | localSet (x : String)
  | i64Add
  | i64Sub
  | i64Mul
  | i64LeS
  | i64Eq
  | i64Ne
  | i64Eqz
  | i64ExtendI32u
  | if_ (then_ else_ : List Instr)
  | block (lbl : Label) (body : List Instr)
  | loop (lbl : Label) (body : List Instr)
  | br (lbl : Label)
  | return_
  deriving Repr

structure Fun where
  name : String
  params : List String
  locals : List String
  body : List Instr
  deriving Repr

end WasmMini
end HeytingLean
