import HeytingLean.LeanCP.Lang.WasmSyntax

/-!
# LeanCP Wasm Emission

Pure pretty-printer from Wasm IR to WebAssembly Text Format (WAT).
WAT is the standard text representation of Wasm, parseable by `wat2wasm`.

Conventions:
- 2-space indentation (WAT convention)
- S-expression format per the WebAssembly spec
- deterministic output (no IO, no randomness)
-/

namespace HeytingLean.LeanCP.Wasm.Emit

open HeytingLean.LeanCP.Wasm

/-- Index a list: produce (index, element) pairs starting from 0. -/
private def indexed (xs : List α) : List (Nat × α) :=
  go 0 xs
where
  go (i : Nat) : List α → List (Nat × α)
  | [] => []
  | x :: rest => (i, x) :: go (i + 1) rest

private def indent (n : Nat) : String :=
  String.intercalate "" (List.replicate (2 * n) " ")

private def sanitizeIdent (s : String) : String :=
  let s' := s.map (fun c => if c.isAlphanum || c = '_' then c else '_')
  if s'.isEmpty then "_empty" else s'

/-- Render a WasmValType as its WAT keyword. -/
def valTypeStr : WasmValType → String
  | .i32 => "i32"
  | .i64 => "i64"
  | .f32 => "f32"
  | .f64 => "f64"

/-- Render a WasmInstr as WAT instruction lines. -/
partial def instrLines (n : Nat) : WasmInstr → List String
  -- Constants
  | .i32Const v => [indent n ++ "i32.const " ++ toString v]
  | .i64Const v => [indent n ++ "i64.const " ++ toString v]
  | .f32Const v => [indent n ++ "f32.const " ++ toString v]
  | .f64Const v => [indent n ++ "f64.const " ++ toString v]
  -- Local variable ops
  | .localGet idx => [indent n ++ "local.get " ++ toString idx]
  | .localSet idx => [indent n ++ "local.set " ++ toString idx]
  | .localTee idx => [indent n ++ "local.tee " ++ toString idx]
  -- Arithmetic (i32)
  | .i32Add  => [indent n ++ "i32.add"]
  | .i32Sub  => [indent n ++ "i32.sub"]
  | .i32Mul  => [indent n ++ "i32.mul"]
  | .i32DivS => [indent n ++ "i32.div_s"]
  | .i32DivU => [indent n ++ "i32.div_u"]
  | .i32RemS => [indent n ++ "i32.rem_s"]
  | .i32RemU => [indent n ++ "i32.rem_u"]
  | .i32And  => [indent n ++ "i32.and"]
  | .i32Or   => [indent n ++ "i32.or"]
  | .i32Xor  => [indent n ++ "i32.xor"]
  | .i32Shl  => [indent n ++ "i32.shl"]
  | .i32ShrS => [indent n ++ "i32.shr_s"]
  | .i32ShrU => [indent n ++ "i32.shr_u"]
  | .i32Eqz  => [indent n ++ "i32.eqz"]
  | .i32Eq   => [indent n ++ "i32.eq"]
  | .i32Ne   => [indent n ++ "i32.ne"]
  | .i32LtS  => [indent n ++ "i32.lt_s"]
  | .i32LtU  => [indent n ++ "i32.lt_u"]
  | .i32GtS  => [indent n ++ "i32.gt_s"]
  | .i32GtU  => [indent n ++ "i32.gt_u"]
  | .i32LeS  => [indent n ++ "i32.le_s"]
  | .i32LeU  => [indent n ++ "i32.le_u"]
  | .i32GeS  => [indent n ++ "i32.ge_s"]
  | .i32GeU  => [indent n ++ "i32.ge_u"]
  -- Arithmetic (i64)
  | .i64Add  => [indent n ++ "i64.add"]
  | .i64Sub  => [indent n ++ "i64.sub"]
  | .i64Mul  => [indent n ++ "i64.mul"]
  | .i64DivS => [indent n ++ "i64.div_s"]
  -- Arithmetic (f32)
  | .f32Add  => [indent n ++ "f32.add"]
  | .f32Sub  => [indent n ++ "f32.sub"]
  | .f32Mul  => [indent n ++ "f32.mul"]
  | .f32Div  => [indent n ++ "f32.div"]
  -- Arithmetic (f64)
  | .f64Add  => [indent n ++ "f64.add"]
  | .f64Sub  => [indent n ++ "f64.sub"]
  | .f64Mul  => [indent n ++ "f64.mul"]
  | .f64Div  => [indent n ++ "f64.div"]
  -- Memory
  | .i32Load off  => [indent n ++ "i32.load offset=" ++ toString off]
  | .i32Store off => [indent n ++ "i32.store offset=" ++ toString off]
  | .i64Load off  => [indent n ++ "i64.load offset=" ++ toString off]
  | .i64Store off => [indent n ++ "i64.store offset=" ++ toString off]
  -- Control flow
  | .block body =>
      [indent n ++ "block"] ++
      (body.map (instrLines (n + 1))).flatten ++
      [indent n ++ "end"]
  | .loop body =>
      [indent n ++ "loop"] ++
      (body.map (instrLines (n + 1))).flatten ++
      [indent n ++ "end"]
  | .if_ th el =>
      [indent n ++ "if"] ++
      (th.map (instrLines (n + 1))).flatten ++
      [indent n ++ "else"] ++
      (el.map (instrLines (n + 1))).flatten ++
      [indent n ++ "end"]
  | .br depth     => [indent n ++ "br " ++ toString depth]
  | .brIf depth   => [indent n ++ "br_if " ++ toString depth]
  | .return_      => [indent n ++ "return"]
  | .call idx     => [indent n ++ "call " ++ toString idx]
  -- Misc
  | .drop         => [indent n ++ "drop"]
  | .nop          => [indent n ++ "nop"]
  | .unreachable  => [indent n ++ "unreachable"]

/-- Emit a WasmFunc as a WAT function definition. -/
def funcDecl (f : WasmFunc) (idx : Nat) : String :=
  let paramDecls := f.params.map fun ty => " (param " ++ valTypeStr ty ++ ")"
  let resultDecls := f.results.map fun ty => " (result " ++ valTypeStr ty ++ ")"
  let localDecls := f.locals.map fun ty => " (local " ++ valTypeStr ty ++ ")"
  let header := "  (func $" ++ sanitizeIdent f.name ++
    String.join paramDecls ++ String.join resultDecls ++ String.join localDecls
  let bodyLines := (f.body.map (instrLines 2)).flatten
  let exportLine := "  (export \"" ++ sanitizeIdent f.name ++ "\" (func " ++ toString idx ++ "))"
  String.intercalate "\n" ([header] ++ bodyLines ++ ["  )", exportLine])

/-- Emit a WasmModule as a complete WAT module. -/
def moduleDecl (m : WasmModule) : String :=
  let memoryDecl := "  (memory (export \"memory\") " ++ toString m.memoryPages ++ ")"
  let funcDecls := (indexed m.funcs).map fun (i, f) => funcDecl f i
  String.intercalate "\n" (["(module", memoryDecl] ++ funcDecls ++ [")"])  ++ "\n"

end HeytingLean.LeanCP.Wasm.Emit
