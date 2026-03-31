import Mathlib.Tactic

import HeytingLean.C.Emit
import HeytingLean.MiniC.Semantics
import HeytingLean.Quantum.TWA.Compile

/-!
# `twa_codegen_demo` (Phase 4)

Repo-local, end-to-end hook for the "Quantum on a Laptop" pipeline:

1. Construct a tiny `LindbladSpec` and `Dynamics` (Phase 1/2 interface),
2. Provide a compilable MiniC approximation (`CompilableSDESystem`) (Phase 3 boundary),
3. Generate a MiniC program + tiny-C AST, then **emit actual C source** to `dist/`,
4. Emit a small driver `main()` that calls one generated function and prints the result,
   together with an `expected.txt` computed via the MiniC semantics.

The corresponding build/run script lives at `scripts/build_twa_local.sh`.
-/

namespace HeytingLean
namespace CLI
namespace TWACodegenDemo

open scoped Classical

open HeytingLean
open HeytingLean.C
open HeytingLean.C.Emit
open HeytingLean.MiniC
open HeytingLean.MiniC.SDE
open HeytingLean.Quantum
open HeytingLean.Quantum.TWA

/-! ## Demo model (tiny and deterministic) -/

private def demoSpec : LindbladSpec :=
  { N := 1
    nJumps := 1
    H := fun _ => 0
    jumps := fun _ => JumpOperator.custom "demo"
    Γ := 0
    Γ_psd := by
      simpa using (HeytingLean.Quantum.PosSemidef.zero (ι := Fin 1)) }

private def demoDyn : Dynamics demoSpec :=
  { field := fun _ => fun _ => ⟨0, 0, 0⟩
    diffusion := fun _ => 0 }

private abbrev ι := StateIndex demoSpec.N
private abbrev κ := Fin demoSpec.nJumps

/-- Helper: sum a list of MiniC integer expressions. -/
private def sumExpr (es : List Expr) : Expr :=
  es.foldl (fun acc e => Expr.add acc e) (Expr.intLit 0)

/-- Integer codegen approximation used for the demo.

We intentionally reference *all* state coordinates in drift/diffusion to keep the emitted C
warning-clean under `-Wall -Wextra` (no unused parameters/locals). -/
private def demoCodegen : CompilableSDESystem ι κ :=
  { drift := fun N _i =>
      sumExpr ((FinEnum.toList ι).map (fun j => Expr.var (N.x j)))
    diffusion := fun N _i _k =>
      sumExpr ((FinEnum.toList ι).map (fun j => Expr.var (N.x j))) }

private def mkCompiled (steps : Nat) : CompiledTWA demoSpec :=
  { dyn := demoDyn
    sdeCodegen := demoCodegen
    steps := steps
    correctness := True }

/-! ## CLI config -/

structure Config where
  outDir : String := "dist/twa_codegen_demo"
  steps : Nat := 2
deriving Repr

private def usage : String :=
  String.intercalate "\n"
    [ "twa_codegen_demo (Phase 4)"
    , ""
    , "Emits:"
    , "  - generated.c        (C source for generated functions + driver main)"
    , "  - expected.txt       (expected stdout from driver main)"
    , "  - minic.repr.txt     (debug repr of the MiniC program)"
    , ""
    , "Flags:"
    , "  --out   <dir>   output directory (relative to repo root unless absolute)"
    , "  --steps <nat>   unrolled steps for simulate_* functions (default: 2)"
    , "  --help          show this message"
    ]

private partial def parseArgs (args : List String) (cfg : Config := {}) : IO (Config × Bool) :=
  match args with
  | [] => pure (cfg, false)
  | "--" :: rest => parseArgs rest cfg
  | "--help" :: _ => pure (cfg, true)
  | "--out" :: dir :: rest => parseArgs rest { cfg with outDir := dir }
  | "--steps" :: n :: rest =>
      match n.toNat? with
      | some k => parseArgs rest { cfg with steps := k }
      | none => throw <| IO.userError s!"invalid --steps: {n}"
  | x :: _ => throw <| IO.userError s!"unknown arg: {x} (try --help)"

private def resolveOutDir (dir : String) : System.FilePath :=
  if dir.startsWith "/" then
    System.FilePath.mk dir
  else
    System.FilePath.mk ".." / dir

private def findDef (p : Program) (nm : String) : Option Fun :=
  p.defs.find? (fun f => decide (f.name = nm))

private def writeFile (path : System.FilePath) (contents : String) : IO Unit := do
  let some parent := path.parent
    | throw <| IO.userError s!"could not compute parent directory for {path}"
  IO.FS.createDirAll parent
  IO.FS.writeFile path contents

private def driverMainSource (fnName : String) (args : List Int) : String :=
  let argsStr := String.intercalate ", " (args.map toString)
  String.intercalate "\n"
    [ "int main(void) {"
    , s!"  long long out = {fnName}({argsStr});"
    , "  printf(\"%lld\\n\", out);"
    , "  return 0;"
    , "}"
    ]

def main (argv : List String) : IO UInt32 := do
  try
    let (cfg, showHelp) ← parseArgs argv
    if showHelp then
      IO.println usage
      return (0 : UInt32)

    let compiled := mkCompiled cfg.steps
    let outDir := resolveOutDir cfg.outDir

    -- Compute the expected value via MiniC semantics (ensures the emitted driver is meaningful).
    let fnName := "sde_simulate_stratonovich_0"
    let names : Names ι κ := Names.default
    let args : List Val :=
      (Val.int 2) :: (List.replicate names.xParams.length (Val.int 1)
        ++ List.replicate (names.dWParamsSteps cfg.steps |>.length) (Val.int 0))
    let fn ←
      match findDef compiled.minic fnName with
      | some f => pure f
      | none => throw <| IO.userError s!"generated program is missing {fnName}"
    let expectedInt ←
      match MiniC.runFun fn args with
      | some (Val.int n) => pure n
      | some v => throw <| IO.userError s!"expected Int return from {fnName}, got {repr v}"
      | none => throw <| IO.userError s!"failed to run {fnName} under MiniC semantics"

    let cPath := outDir / "generated.c"
    let expectedPath := outDir / "expected.txt"
    let minicPath := outDir / "minic.repr.txt"

    let cHeader :=
      String.intercalate "\n"
        [ "/* Generated by HeytingLean (twa_codegen_demo) — Phase 4"
        , s!"   steps={cfg.steps}"
        , "*/"
        , "#include <stdio.h>"
        , ""
        ]
    let cDefs := Emit.funDefs (compiled.c.defs ++ [compiled.c.main])
    let driver := driverMainSource fnName (args.map (fun v =>
      match v with
      | Val.int n => n
      | Val.bool b => if b then 1 else 0))
    let cSource := cHeader ++ cDefs ++ "\n\n" ++ driver ++ "\n"

    writeFile cPath cSource
    writeFile expectedPath (toString expectedInt ++ "\n")
    writeFile minicPath (reprStr compiled.minic ++ "\n")

    IO.println s!"[twa_codegen_demo] wrote {cPath}"
    IO.println s!"[twa_codegen_demo] wrote {expectedPath} (expected stdout)"
    return (0 : UInt32)
  catch e =>
    IO.eprintln s!"[twa_codegen_demo] error: {e}"
    return (1 : UInt32)

end TWACodegenDemo
end CLI
end HeytingLean

/-! Expose entry point for the Lake executable target. -/

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.TWACodegenDemo.main args
