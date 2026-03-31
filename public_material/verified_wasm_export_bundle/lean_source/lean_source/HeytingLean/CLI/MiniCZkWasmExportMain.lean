import HeytingLean.LambdaIR.Add1EndToEnd
import HeytingLean.LambdaIR.Add2EndToEnd
import HeytingLean.LambdaIR.Certified
import HeytingLean.LambdaIR.Compile
import HeytingLean.MiniC.Semantics
import HeytingLean.MiniC.ToWasmMini
import HeytingLean.WasmMini.EmitWAT

/-!
# `minic_zkwasm_export` (MiniC → zkWASM WAT/WASM)

Produce a `zkWasm`-compatible WASM image for “prove execution of WASM” workflows.

Important:
- The verified core remains: MiniC → WasmMini compilation + correctness proofs.
- The `zkmain` adapter is currently **unverified glue** (see `WasmMini.emitZkWasmModule`).

Outputs:
- `kernel_zkwasm.wat`  (zkWASM-compatible module with imports + `zkmain`)
- `kernel_zkwasm.wasm` (assembled, if `wat2wasm` exists)
- Optional validation via `wasm-validate` / `wasm-tools validate`.
-/

namespace HeytingLean
namespace CLI
namespace MiniCZkWasmExport

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
  outDir : String := "dist/minic_zkwasm_export"
  assemble : Bool := true
deriving Repr

private def usage : String :=
  String.intercalate "\n"
    [ "minic_zkwasm_export"
    , ""
    , "Emits:"
    , "  - kernel_zkwasm.wat        (zkWASM-compatible WAT)"
    , "  - kernel_zkwasm.wasm       (assembled if `wat2wasm` exists)"
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

def main (argv : List String) : IO UInt32 := do
  try
    let (cfg, showHelp) ← parseArgs argv
    if showHelp then
      IO.println usage
      return (0 : UInt32)

    let outDir ← resolveOutDir cfg.outDir
    let watPath := outDir / "kernel_zkwasm.wat"
    let wasmPath := outDir / "kernel_zkwasm.wasm"

    let add1Minic :=
      (compileNat1Fun (funName := "heyting_add1") (paramName := "x") (t := termAdd1IR)
          termAdd1_isNatFun).val
    let add2Minic :=
      (compileNat2Fun (funName := "heyting_add2") (t := termAdd2IR)
          termAdd2_isNat2Fun).val
    let funsWasm : List HeytingLean.WasmMini.Fun :=
      ([add1Minic, add2Minic] : List MiniC.Fun).map HeytingLean.MiniC.ToWasmMini.compileFun

    let wat := HeytingLean.WasmMini.emitZkWasmModule funsWasm
    writeFile watPath wat
    IO.println s!"[minic_zkwasm_export] wrote {watPath}"

    if !cfg.assemble then
      return (0 : UInt32)

    match ← assembleWasm watPath wasmPath with
    | .error e =>
        IO.eprintln s!"[minic_zkwasm_export] assemble skipped/failed: {e}"
        return (0 : UInt32)
    | .ok () =>
        match ← validateWasm wasmPath with
        | .ok () =>
            IO.println s!"[minic_zkwasm_export] wrote {wasmPath}"
            return (0 : UInt32)
        | .error e =>
            IO.eprintln s!"[minic_zkwasm_export] wasm validation failed: {e}"
            return (1 : UInt32)
  catch e =>
    IO.eprintln s!"[minic_zkwasm_export] error: {e.toString}"
    return (1 : UInt32)

end MiniCZkWasmExport
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.MiniCZkWasmExport.main args
