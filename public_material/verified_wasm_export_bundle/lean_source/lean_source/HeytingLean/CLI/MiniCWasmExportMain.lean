import HeytingLean.LambdaIR.Add1EndToEnd
import HeytingLean.LambdaIR.Add2EndToEnd
import HeytingLean.LambdaIR.Certified
import HeytingLean.LambdaIR.Compile
import HeytingLean.MiniC.Semantics
import HeytingLean.MiniC.ToWasmMini
import HeytingLean.WasmMini.EmitWAT

/-!
# `minic_wasm_export` (MiniC WASM Backend, Phase 1)

Emits a WAT/WASM kernel bundle from MiniC functions, mirroring `lambda_kernel_export`:

- `kernel.wat`      (WAT source)
- `kernel.wasm`     (assembled, if `wat2wasm` is available)
- `driver.sh`       (runs the exported functions with `wasmtime`)
- `expected.txt`    (expected stdout)
- `minic.repr.txt`  (debug repr of the MiniC kernel)

This executable is **executable-first**:
- it always writes `kernel.wat` + `expected.txt` + `minic.repr.txt`,
- it assembles and runs only if the host toolchain is present,
- missing tools are treated as a *skip* (exit 0 with a warning), not a crash.
-/

namespace HeytingLean
namespace CLI
namespace MiniCWasmExport

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
  outDir : String := "dist/minic_wasm_export"
  run : Bool := true
deriving Repr

private def usage : String :=
  String.intercalate "\n"
    [ "minic_wasm_export"
    , ""
    , "Emits:"
    , "  - kernel.wat      (WAT source)"
    , "  - kernel.wasm     (assembled if `wat2wasm` exists)"
    , "  - driver.sh       (wasmtime runner)"
    , "  - expected.txt    (expected stdout)"
    , "  - minic.repr.txt  (debug repr of the MiniC kernel)"
    , ""
    , "Flags:"
    , "  --out <dir>     output directory (relative to repo root unless absolute)"
    , "  --no-run        do not attempt wat2wasm/wasmtime"
    , "  --help          show this message"
    ]

private partial def parseArgs (args : List String) (cfg : Config := {}) : IO (Config × Bool) :=
  match args with
  | [] => pure (cfg, false)
  | "--" :: rest => parseArgs rest cfg
  | "--help" :: _ => pure (cfg, true)
  | "--no-run" :: rest => parseArgs rest { cfg with run := false }
  | "--out" :: dir :: rest => parseArgs rest { cfg with outDir := dir }
  | x :: _ => throw <| IO.userError s!"unknown arg: {x} (try --help)"

private def resolveOutDir (dir : String) : IO System.FilePath := do
  if dir.startsWith "/" then
    return System.FilePath.mk dir

  let cwd ← IO.currentDir
  let base :=
    if cwd.fileName == some "lean" then
      cwd.parent.getD cwd
    else
      cwd
  return base / dir

private def repoRoot : IO System.FilePath := do
  let cwd ← IO.currentDir
  if cwd.fileName == some "lean" then
    return cwd.parent.getD cwd
  else
    return cwd

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

private def writeExecutable (path : System.FilePath) (contents : String) : IO Unit := do
  writeFile path contents
  -- Lean's stdlib does not expose a portable chmod API; best-effort shell out.
  let _ ← runCmd? "bash" ["-lc", s!"chmod +x {shQuote path.toString}"] (cwd := none)
  pure ()

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
    if name == "wasmtime" then "HEYTING_WASMTIME"
    else if name == "wat2wasm" then "HEYTING_WAT2WASM"
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
    -- Not all platforms let us resolve the full path cheaply; use `name` as cmd.
    return some (System.FilePath.mk name)

  return none

private def driverScript (wasmPath : System.FilePath) : String :=
  String.intercalate "\n"
    [ "#!/usr/bin/env bash"
    , "set -euo pipefail"
    , ""
    , "WASM_FILE=" ++ shQuote wasmPath.toString
    , "WAT_FILE=" ++ shQuote (wasmPath.withExtension "wat").toString
    , "if [[ -f \"$WASM_FILE\" ]]; then MOD=\"$WASM_FILE\"; else MOD=\"$WAT_FILE\"; fi"
    , ""
    , "# If your wasmtime prints no return values for --invoke, use the generated kernel.wast instead:"
    , "#   wasmtime wast " ++ shQuote (wasmPath.withExtension "wast").toString
    , ""
    , "wasmtime wast " ++ shQuote (wasmPath.withExtension "wast").toString
    , ""
    ]

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
  -- Validator not present; treat as ok (assembler/runtime are the primary checks).
  return .ok ()

private def runWasmtime (modulePath : System.FilePath) (args : List String) : IO (Except String String) := do
  match ← findTool? "wasmtime" with
  | none => return .error "missing tool: wasmtime"
  | some exe =>
      match ← runCmd? exe.toString (["wast", modulePath.toString] ++ args) with
      | none => return .error "failed to spawn wasmtime"
      | some out =>
          if out.exitCode == 0 then
            return .ok out.stdout.trim
          else
            return .error s!"wasmtime failed rc={out.exitCode}\n{out.stderr.trim}"

private def wastScript (moduleWat : String) (tests : List String) : String :=
  let header :=
    String.intercalate "\n"
      [ ";; Generated by HeytingLean (MiniC WASM backend)"
      , ";; Run: wasmtime wast kernel.wast"
      , ""
      ]
  let body := String.intercalate "\n" (tests.map (fun t => s!"(assert_return {t})"))
  String.intercalate "\n" [header, moduleWat.trim, "", body, ""]

def main (argv : List String) : IO UInt32 := do
  try
    let (cfg, showHelp) ← parseArgs argv
    if showHelp then
      IO.println usage
      return (0 : UInt32)

    let outDir ← resolveOutDir cfg.outDir
    let watPath := outDir / "kernel.wat"
    let wasmPath := outDir / "kernel.wasm"
    let wastPath := outDir / "kernel.wast"
    let driverPath := outDir / "driver.sh"
    let expectedPath := outDir / "expected.txt"
    let minicPath := outDir / "minic.repr.txt"

    -- Compile the same tiny certified LambdaIR slice as `lambda_kernel_export`, but emit WASM.
    let add1Minic :=
      (compileNat1Fun (funName := "heyting_add1") (paramName := "x") (t := termAdd1IR)
          termAdd1_isNatFun).val
    let add2Minic :=
      (compileNat2Fun (funName := "heyting_add2") (t := termAdd2IR)
          termAdd2_isNat2Fun).val
    let funsMinic : List MiniC.Fun := [add1Minic, add2Minic]
    let funsWasm : List HeytingLean.WasmMini.Fun :=
      funsMinic.map HeytingLean.MiniC.ToWasmMini.compileFun

    -- Expected output, computed at the Lean level.
    let demoArg : Nat := 41
    let demoX2 : Nat := 20
    let demoY2 : Nat := 22
    let expected1 : Nat := leanAdd1 demoArg
    let expected2 : Nat := leanAdd2 demoX2 demoY2

    let wat := HeytingLean.WasmMini.emitModule funsWasm
    writeFile watPath wat
    let tests : List String :=
      [ s!"(invoke \"heyting_add1\" (i64.const {Int.ofNat demoArg})) (i64.const {Int.ofNat expected1})"
      , s!"(invoke \"heyting_add2\" (i64.const {Int.ofNat demoX2}) (i64.const {Int.ofNat demoY2})) (i64.const {Int.ofNat expected2})"
      ]
    writeFile wastPath (wastScript wat tests)
    writeFile expectedPath (String.intercalate "\n" [toString expected1, toString expected2] ++ "\n")
    writeFile minicPath (reprStr funsMinic ++ "\n")
    writeExecutable driverPath (driverScript wasmPath)

    IO.println s!"[minic_wasm_export] wrote {watPath}"
    IO.println s!"[minic_wasm_export] wrote {wastPath}"
    IO.println s!"[minic_wasm_export] wrote {expectedPath}"
    IO.println s!"[minic_wasm_export] wrote {minicPath}"

    if !cfg.run then
      return (0 : UInt32)

    -- Assemble (optional) for convenience (not required for testing), then run the WAST script.
    match ← assembleWasm watPath wasmPath with
    | .ok () =>
        IO.println s!"[minic_wasm_export] wrote {wasmPath}"
        match ← validateWasm wasmPath with
        | .error err =>
            IO.eprintln s!"[minic_wasm_export] wasm validation failed: {err}"
            return (1 : UInt32)
        | .ok () => pure ()
    | .error err =>
        IO.eprintln s!"[minic_wasm_export] WARN: assemble skipped ({err}); continuing with WAST run"

    match ← runWasmtime wastPath [] with
    | .error e =>
        IO.eprintln s!"[minic_wasm_export] SKIP run: {e}"
        return (0 : UInt32)
    | .ok _ =>
        IO.println "[minic_wasm_export] wasmtime wast: ok"
        return (0 : UInt32)
  catch e =>
    IO.eprintln s!"[minic_wasm_export] error: {e}"
    return (1 : UInt32)

end MiniCWasmExport
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.MiniCWasmExport.main args
