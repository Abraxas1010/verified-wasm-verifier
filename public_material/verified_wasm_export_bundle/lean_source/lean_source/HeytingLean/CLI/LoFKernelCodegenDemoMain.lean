import HeytingLean.C.Emit
import HeytingLean.C.Semantics
import HeytingLean.MiniC.Syntax
import HeytingLean.MiniC.ToC
import HeytingLean.LoF.LoFPrimary.Normalization
import HeytingLean.LoF.LoFPrimary.Optimize
import HeytingLean.LoF.LoFPrimary.MuxNet
import HeytingLean.LoF.LoFPrimary.GateSpec
import HeytingLean.LoF.LoFPrimary.AIG

/-!
# `lof_kernel_codegen_demo`

Repo-local end-to-end demo for the “LoF kernel slice”:

* Choose a small set of `LoFPrimary.Expr 2` terms.
* Compile each expression to a MiniC boolean expression (0/1 encoded in the emitted C).
* Emit a single `generated.c` containing one C function per expression plus a driver `main()`.
* Write `expected.txt` containing the driver stdout as computed by Lean (truth-table lines).

The corresponding compile-and-run hook lives at `scripts/build_lof_kernel_local.sh`.
-/

namespace HeytingLean
namespace CLI
namespace LoFKernelCodegenDemo

open HeytingLean
open HeytingLean.C
open HeytingLean.C.Emit
open HeytingLean.LoF
open HeytingLean.LoF.LoFPrimary
open HeytingLean.MiniC

structure Config where
  outDir : String := "dist/lof_kernel_codegen_demo"
  emitGates : Bool := false
  emitAig : Bool := false
deriving Repr

private def usage : String :=
  String.intercalate "\n"
    [ "lof_kernel_codegen_demo"
    , ""
    , "Emits:"
    , "  - generated.c        (C source for LoFPrimary eval functions + driver main)"
    , "  - expected.txt       (expected stdout from driver main)"
    , "  - minic.repr.txt     (debug repr of the MiniC functions)"
    , "  - gates.repr.txt     (debug repr of GateSpec netlists; requires --emit-gates)"
    , "  - circuit.aag        (AIGER ASCII; requires --emit-aig)"
    , ""
    , "Flags:"
    , "  --out <dir>    output directory (relative to repo root unless absolute)"
    , "  --emit-gates   also emit GateSpec netlists (debug)"
    , "  --emit-aig     also emit AIGER ASCII (first demo expr)"
    , "  --help         show this message"
    ]

private partial def parseArgs (args : List String) (cfg : Config := {}) : IO (Config × Bool) :=
  match args with
  | [] => pure (cfg, false)
  | "--" :: rest => parseArgs rest cfg
  | "--help" :: _ => pure (cfg, true)
  | "--out" :: dir :: rest => parseArgs rest { cfg with outDir := dir }
  | "--emit-gates" :: rest => parseArgs rest { cfg with emitGates := true }
  | "--emit-aig" :: rest => parseArgs rest { cfg with emitAig := true }
  | x :: _ => throw <| IO.userError s!"unknown arg: {x} (try --help)"

private def resolveOutDir (dir : String) : System.FilePath :=
  if dir.startsWith "/" then
    System.FilePath.mk dir
  else
    System.FilePath.mk ".." / dir

private def writeFile (path : System.FilePath) (contents : String) : IO Unit := do
  let some parent := path.parent
    | throw <| IO.userError s!"could not compute parent directory for {path}"
  IO.FS.createDirAll parent
  IO.FS.writeFile path contents

/-! ## LoFPrimary → MiniC -/

private def paramName (i : Fin 2) : String :=
  s!"x{i.val}"

private def optimizeToMiniC (A : Expr 2) : MiniC.Expr :=
  HeytingLean.LoF.LoFPrimary.MuxNet.toMiniCExpr paramName (HeytingLean.LoF.LoFPrimary.MuxNet.toMuxNet A)

private def emitGateNetlist (nl : GateSpec.Netlist) : String :=
  let gateLines := nl.gates.map (fun g => reprStr g)
  String.intercalate "\n" (gateLines ++ [s!"-- output: {nl.output}"])

private def mkFun (name : String) (A : Expr 2) : MiniC.Fun :=
  { name := name
    params := [paramName ⟨0, by decide⟩, paramName ⟨1, by decide⟩]
    body := .return (optimizeToMiniC A) }

/-! ## Demo expressions (n = 2) -/

private def demoExprs : List (String × Expr 2) :=
  [ ("void", Expr.void)
  , ("marked", Expr.marked)
  , ("x0", Expr.var ⟨0, by decide⟩)
  , ("x1", Expr.var ⟨1, by decide⟩)
  , ("¬x0", Expr.mark (Expr.var ⟨0, by decide⟩))
  , ("x0∨x1", Expr.juxt (Expr.var ⟨0, by decide⟩) (Expr.var ⟨1, by decide⟩))
  , ("x0∨¬x1", Expr.juxt (Expr.var ⟨0, by decide⟩) (Expr.mark (Expr.var ⟨1, by decide⟩)))
  , ("¬(x0∨x1)", Expr.mark (Expr.juxt (Expr.var ⟨0, by decide⟩) (Expr.var ⟨1, by decide⟩)))
  ]

private def valuations : List (List Int × (Fin 2 → Bool)) :=
  let mkρ (b0 b1 : Bool) : Fin 2 → Bool
    | ⟨0, _⟩ => b0
    | ⟨1, _⟩ => b1
  [ ([0, 0], mkρ false false)
  , ([0, 1], mkρ false true)
  , ([1, 0], mkρ true false)
  , ([1, 1], mkρ true true)
  ]

private def intOfBool (b : Bool) : Int :=
  if b then 1 else 0

private def driverMainSource (calls : List String) : String :=
  let body := calls.map (fun c => s!"  printf(\"%lld\\n\", {c});")
  String.intercalate "\n"
    ([ "int main(void) {"
     ] ++ body ++
     [ "  return 0;"
     , "}"
     ])

private def checkEq (got expected : Int) (ctx : String) : IO Unit := do
  if got != expected then
    throw <| IO.userError s!"mismatch: {ctx}: got={got} expected={expected}"

private def buildFns : List (String × Expr 2) → Nat → List (String × MiniC.Fun)
  | [], _ => []
  | (label, A) :: rest, i =>
      (label, mkFun (name := s!"lof_eval_{i}") A) :: buildFns rest (i + 1)

private partial def processVals
    (fnName label : String) (A : Expr 2) (cFun : CFun)
    (vals : List (List Int × (Fin 2 → Bool)))
    (expectedAcc driverAcc : List String) : IO (List String × List String) :=
  match vals with
  | [] => pure (expectedAcc, driverAcc)
  | (args, ρ) :: rest => do
      let exp := intOfBool (LoFPrimary.eval A ρ)
      let got ←
        match HeytingLean.C.runCFunFrag cFun args with
        | some v => pure v
        | none => throw <| IO.userError s!"failed to evaluate compiled C fun {fnName} on args={args}"
      checkEq got exp s!"{label} / {fnName} / args={args}"
      let argsStr := String.intercalate ", " (args.map toString)
      processVals fnName label A cFun rest (toString exp :: expectedAcc) (s!"{fnName}({argsStr})" :: driverAcc)

private partial def processExprs
    (es : List (String × Expr 2)) (cFuns : List CFun) (idx : Nat)
    (expectedAcc driverAcc : List String) : IO (List String × List String) :=
  match es, cFuns with
  | [], [] => pure (expectedAcc, driverAcc)
  | (label, A) :: es', cFun :: cFuns' => do
      let fnName := s!"lof_eval_{idx}"
      let (expectedAcc', driverAcc') ←
        processVals fnName label A cFun valuations expectedAcc driverAcc
      processExprs es' cFuns' (idx + 1) expectedAcc' driverAcc'
  | _, _ => throw <| IO.userError "internal error: demoExprs and cFuns length mismatch"

def main (argv : List String) : IO UInt32 := do
  try
    let (cfg, showHelp) ← parseArgs argv
    if showHelp then
      IO.println usage
      return (0 : UInt32)

    let outDir := resolveOutDir cfg.outDir
    let cPath := outDir / "generated.c"
    let expectedPath := outDir / "expected.txt"
    let minicPath := outDir / "minic.repr.txt"
    let gatesPath := outDir / "gates.repr.txt"
    let aigPath := outDir / "circuit.aag"

    -- Build MiniC functions and their compiled-C counterparts.
    let fns : List (String × MiniC.Fun) := buildFns demoExprs 0
    let cFuns : List CFun := fns.map (fun (_, fn) => MiniC.ToC.compileFun fn)

    -- Compute expected output and validate the compiled-C semantics on 0/1 inputs.
    let (expectedRev, driverRev) ← processExprs demoExprs cFuns 0 [] []
    let expectedLines := expectedRev.reverse
    let driverCalls := driverRev.reverse

    let cHeader :=
      String.intercalate "\n"
        [ "/* Generated by HeytingLean (lof_kernel_codegen_demo)"
        , "   LoFPrimary truth-table demo (n=2)"
        , "*/"
        , "#include <stdio.h>"
        , ""
        ]
    let cDefs := Emit.funDefs cFuns
    let driver := driverMainSource driverCalls
    let cSource := cHeader ++ cDefs ++ "\n\n" ++ driver ++ "\n"

    writeFile cPath cSource
    writeFile expectedPath (String.intercalate "\n" expectedLines ++ "\n")
    writeFile minicPath (reprStr fns ++ "\n")

    if cfg.emitGates then
      let nets : List (String × GateSpec.Netlist) :=
        demoExprs.map (fun (label, A) => (label, GateSpec.toNetlist (n := 2) (MuxNet.toMuxNet A)))
      let gatesText :=
        String.intercalate "\n\n" <|
          nets.map (fun (label, nl) => s!"-- {label}\n{emitGateNetlist nl}")
      writeFile gatesPath (gatesText ++ "\n")

    if cfg.emitAig then
      match demoExprs with
      | [] =>
          throw <| IO.userError "internal error: demoExprs is empty"
      | (_, firstExpr) :: _ =>
          let aig := AIG.ofMuxNet (MuxNet.toMuxNet firstExpr)
          writeFile aigPath (aig.toAigerAscii ++ "\n")

    IO.println s!"[lof_kernel_codegen_demo] wrote {cPath}"
    IO.println s!"[lof_kernel_codegen_demo] wrote {expectedPath} (expected stdout)"
    if cfg.emitGates then
      IO.println s!"[lof_kernel_codegen_demo] wrote {gatesPath} (gate netlists)"
    if cfg.emitAig then
      IO.println s!"[lof_kernel_codegen_demo] wrote {aigPath} (AIGER ASCII)"
    return (0 : UInt32)
  catch e =>
    IO.eprintln s!"[lof_kernel_codegen_demo] error: {e}"
    return (1 : UInt32)

end LoFKernelCodegenDemo
end CLI
end HeytingLean

/-! Expose entry point for the Lake executable target. -/

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.LoFKernelCodegenDemo.main args
