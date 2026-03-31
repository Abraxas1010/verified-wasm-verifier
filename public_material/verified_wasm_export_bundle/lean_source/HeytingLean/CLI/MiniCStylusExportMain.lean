import HeytingLean.LambdaIR.Add1EndToEnd
import HeytingLean.LambdaIR.Add2EndToEnd
import HeytingLean.LambdaIR.Certified
import HeytingLean.LambdaIR.Compile
import HeytingLean.MiniC.Semantics
import HeytingLean.MiniC.ToWasmMini
import HeytingLean.WasmMini.EmitWAT

/-!
# `minic_stylus_export` (MiniC → Stylus WASM + Solidity wrapper)

This is the next step after the Phase-1 WASM backend: produce a **Stylus-compatible**
WAT/WASM module (exports `user_entrypoint`) plus a **Solidity wrapper** for calling it.

Important:
- The verified core remains: MiniC → WasmMini compilation + correctness proofs.
- The Stylus adapter and Solidity wrapper are currently **unverified glue** and are intended
  for smoke-level integration while we iterate.

Outputs:
- `kernel_stylus.wat`  (Stylus-compatible module with imports + `user_entrypoint`)
- `kernel_stylus.wasm` (assembled, if `wat2wasm` exists)
- `HeytingMiniCStylus.sol` (Solidity wrapper using a tiny custom ABI)

The custom ABI is described in `WasmMini.emitStylusModule`.
-/

namespace HeytingLean
namespace CLI
namespace MiniCStylusExport

open HeytingLean
open HeytingLean.Certified
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.Add1EndToEnd
open HeytingLean.LambdaIR.Add1MiniCProof
open HeytingLean.LambdaIR.Add2EndToEnd
open HeytingLean.LambdaIR.Add2MiniCProof
open HeytingLean.LambdaIR.CertifiedCompile
open HeytingLean.MiniC

structure Config where
  outDir : String := "dist/minic_stylus_export"
  assemble : Bool := true
deriving Repr

private def usage : String :=
  String.intercalate "\n"
    [ "minic_stylus_export"
    , ""
    , "Emits:"
    , "  - kernel_stylus.wat        (Stylus-compatible WAT)"
    , "  - kernel_stylus.wasm       (assembled if `wat2wasm` exists)"
    , "  - HeytingMiniCStylus.sol   (Solidity wrapper)"
    , ""
    , "Flags:"
    , "  --out <dir>         output directory (relative to repo root unless absolute)"
    , "  --no-assemble       do not attempt wat2wasm"
    , "  --help              show this message"
    ]

private partial def parseArgs (args : List String) (cfg : Config := {}) : IO (Config × Bool) :=
  match args with
  | [] => pure (cfg, false)
  | "--" :: rest => parseArgs rest cfg
  | "--help" :: _ => pure (cfg, true)
  | "--no-assemble" :: rest => parseArgs rest { cfg with assemble := false }
  | "--out" :: dir :: rest => parseArgs rest { cfg with outDir := dir }
  | x :: _ => throw <| IO.userError s!"unknown arg: {x} (try --help)"

private def repoRoot : IO System.FilePath := do
  let cwd ← IO.currentDir
  if cwd.fileName == some "lean" then
    return cwd.parent.getD cwd
  else
    return cwd

private def resolveOutDir (dir : String) : IO System.FilePath := do
  if dir.startsWith "/" then
    return System.FilePath.mk dir
  let root ← repoRoot
  return root / dir

private def writeFile (path : System.FilePath) (contents : String) : IO Unit := do
  let some parent := path.parent
    | throw <| IO.userError s!"could not compute parent directory for {path}"
  IO.FS.createDirAll parent
  IO.FS.writeFile path contents

private def runCmd? (cmd : String) (args : List String) (cwd : Option System.FilePath := none) :
    IO (Option IO.Process.Output) := do
  try
    let out ← IO.Process.output { cmd := cmd, args := args.toArray, cwd := cwd }
    return some out
  catch _ =>
    return none

private def shQuote (s : String) : String :=
  "'" ++ (s.replace "'" "'\"'\"'") ++ "'"

private def hasCmd (cmd : String) : IO Bool := do
  match ← runCmd? "bash" ["-lc", s!"command -v {cmd} >/dev/null 2>&1"] with
  | some out => pure (out.exitCode == 0)
  | none => pure false

private def toolchainBinDir : IO System.FilePath := do
  let root ← repoRoot
  return root / "tools" / "wasm_toolchain" / "bin"

private def findTool? (name : String) : IO (Option System.FilePath) := do
  -- 1) env override
  let envKey :=
    if name == "wat2wasm" then "HEYTING_WAT2WASM"
    else if name == "wasm-validate" then "HEYTING_WASM_VALIDATE"
    else if name == "wasm-tools" then "HEYTING_WASM_TOOLS"
    else ""
  if !envKey.isEmpty then
    if let some p ← IO.getEnv envKey then
      let fp := System.FilePath.mk p
      if (← fp.pathExists) then return some fp

  -- 2) repo-local toolchain
  let binDir ← toolchainBinDir
  let cand := binDir / name
  if (← cand.pathExists) then
    return some cand

  -- 3) PATH
  if (← hasCmd name) then
    return some (System.FilePath.mk name)

  return none

private def assembleWasm (watPath wasmPath : System.FilePath) : IO (Except String Unit) := do
  match ← findTool? "wat2wasm" with
  | none => return .error "missing tool: wat2wasm (WABT)"
  | some exe =>
      match ← runCmd? exe.toString [watPath.toString, "-o", wasmPath.toString] with
      | none => return .error "failed to spawn wat2wasm"
      | some out =>
          if out.exitCode == 0 then
            return .ok ()
          else
            return .error s!"wat2wasm failed rc={out.exitCode}\n{out.stderr.trim}"

private def validateWasm (wasmPath : System.FilePath) : IO (Except String Unit) := do
  if let some exe ← findTool? "wasm-validate" then
    match ← runCmd? exe.toString [wasmPath.toString] with
    | some out =>
        if out.exitCode == 0 then return .ok ()
        else return .error s!"wasm-validate failed rc={out.exitCode}\n{out.stderr.trim}"
    | none => return .error "failed to spawn wasm-validate"
  if let some exe ← findTool? "wasm-tools" then
    match ← runCmd? exe.toString ["validate", wasmPath.toString] with
    | some out =>
        if out.exitCode == 0 then return .ok ()
        else return .error s!"wasm-tools validate failed rc={out.exitCode}\n{out.stderr.trim}"
    | none => return .error "failed to spawn wasm-tools"
  return .ok ()

private def solidityWrapperSource : String :=
  String.intercalate "\n"
    [ "// SPDX-License-Identifier: MIT"
    , "pragma solidity ^0.8.20;"
    , ""
    , "/// @notice Solidity wrapper for the HeytingLean MiniC Stylus module."
    , "/// @dev Calls use a tiny custom ABI (not standard Solidity ABI)."
    , "///      calldata = tag:u8 | args..."
    , "///        tag=0 => add1(x:i64)"
    , "///        tag=1 => add2(x:i64,y:i64)"
    , "///        tag=2 => ceiFlag(x:i64,y:i64)   (demo checker: returns 1 if x > y else 0)"
    , "///"
    , "///      NOTE: args + return are encoded **little-endian** to match WASM's i64.load/store."
    , "///      return data is 32 bytes; the first 8 bytes are a little-endian u64 result."
    , "library HeytingMiniCStylusCalls {"
    , "  function _le64(uint64 x) private pure returns (bytes memory) {"
    , "    bytes memory out = new bytes(8);"
    , "    for (uint256 i = 0; i < 8; i++) {"
    , "      out[i] = bytes1(uint8(x >> (8 * i)));"
    , "    }"
    , "    return out;"
    , "  }"
    , ""
    , "  function _readLeU64(bytes memory ret) private pure returns (uint64) {"
    , "    require(ret.length >= 8, \"short return\");"
    , "    uint64 x = 0;"
    , "    for (uint256 i = 0; i < 8; i++) {"
    , "      x |= uint64(uint8(ret[i])) << (8 * i);"
    , "    }"
    , "    return x;"
    , "  }"
    , ""
    , "  function add1(address target, uint64 x) internal view returns (uint64) {"
    , "    bytes memory data = bytes.concat(bytes1(uint8(0)), _le64(x));"
    , "    (bool ok, bytes memory ret) = target.staticcall(data);"
    , "    require(ok && ret.length == 32, \"stylus call failed\");"
    , "    return _readLeU64(ret);"
    , "  }"
    , ""
    , "  function add2(address target, uint64 x, uint64 y) internal view returns (uint64) {"
    , "    bytes memory data = bytes.concat(bytes1(uint8(1)), _le64(x), _le64(y));"
    , "    (bool ok, bytes memory ret) = target.staticcall(data);"
    , "    require(ok && ret.length == 32, \"stylus call failed\");"
    , "    return _readLeU64(ret);"
    , "  }"
    , ""
    , "  /// @notice Example \"checker\" export: returns 1 if x > y, else 0."
    , "  function ceiFlag(address target, uint64 x, uint64 y) internal view returns (uint64) {"
    , "    bytes memory data = bytes.concat(bytes1(uint8(2)), _le64(x), _le64(y));"
    , "    (bool ok, bytes memory ret) = target.staticcall(data);"
    , "    require(ok && ret.length == 32, \"stylus call failed\");"
    , "    return _readLeU64(ret);"
    , "  }"
    , "}"
    , ""
    ]

def main (argv : List String) : IO UInt32 := do
  try
    let (cfg, showHelp) ← parseArgs argv
    if showHelp then
      IO.println usage
      return (0 : UInt32)

    let outDir ← resolveOutDir cfg.outDir
    let watPath := outDir / "kernel_stylus.wat"
    let wasmPath := outDir / "kernel_stylus.wasm"
    let solPath := outDir / "HeytingMiniCStylus.sol"

    let add1Minic :=
      (compileNat1Fun (funName := "heyting_add1") (paramName := "x") (t := termAdd1IR)
          termAdd1_isNatFun).val
    let add2Minic :=
      (compileNat2Fun (funName := "heyting_add2") (t := termAdd2IR)
          termAdd2_isNat2Fun).val
    let ceiFlagMinic : MiniC.Fun :=
      { name := "heyting_cei_flag"
        params := ["x", "y"]
        body :=
          -- returns 1 if x > y, else 0 (tiny demo "checker")
          MiniC.Stmt.if_ (MiniC.Expr.le (MiniC.Expr.var "x") (MiniC.Expr.var "y"))
            (MiniC.Stmt.return (MiniC.Expr.intLit 0))
            (MiniC.Stmt.return (MiniC.Expr.intLit 1))
      }
    let funsWasm : List HeytingLean.WasmMini.Fun :=
      ([add1Minic, add2Minic, ceiFlagMinic] : List MiniC.Fun).map HeytingLean.MiniC.ToWasmMini.compileFun

    let wat := HeytingLean.WasmMini.emitStylusModule funsWasm
    writeFile watPath wat
    writeFile solPath solidityWrapperSource
    IO.println s!"[minic_stylus_export] wrote {watPath}"
    IO.println s!"[minic_stylus_export] wrote {solPath}"

    if !cfg.assemble then
      return (0 : UInt32)

    match ← assembleWasm watPath wasmPath with
    | .error e =>
        IO.eprintln s!"[minic_stylus_export] WARN: assemble skipped ({e})"
        return (0 : UInt32)
    | .ok () =>
        IO.println s!"[minic_stylus_export] wrote {wasmPath}"
        match ← validateWasm wasmPath with
        | .ok () => return (0 : UInt32)
        | .error e =>
            IO.eprintln s!"[minic_stylus_export] wasm validation failed: {e}"
            return (1 : UInt32)
  catch e =>
    IO.eprintln s!"[minic_stylus_export] error: {e}"
    return (1 : UInt32)

end MiniCStylusExport
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.MiniCStylusExport.main args
