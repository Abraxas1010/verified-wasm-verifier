import HeytingLean.C.Emit
import HeytingLean.CLI.Args
import HeytingLean.Experiments.EulerSheafSurreal.GenerativeControls
import HeytingLean.Experiments.EulerSheafSurreal.Kernel
import HeytingLean.LambdaIR.Compile
import HeytingLean.LambdaIR.Nat2FunFragment
import HeytingLean.LambdaIR.NatFunFragment
import HeytingLean.Meta.LeanTT0.ExportCAB
import HeytingLean.MiniC.ToC

/-!
# `euler_sheaf_surreal_export`

Exports a depth-10 Euler/Sheaf/Surreal kernel through the certified pipeline:

`Lean -> LambdaIR (Nat fragment) -> MiniC -> C`

The bundle is CAB-certified and intended for direct benchmarking.
-/

namespace HeytingLean
namespace CLI
namespace EulerSheafSurrealExport

open HeytingLean
open HeytingLean.C
open HeytingLean.C.Emit
open HeytingLean.Certified
open HeytingLean.Experiments.EulerSheafSurreal
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.NatFunFragment
open HeytingLean.LambdaIR.Nat2FunFragment
open HeytingLean.LambdaIR.CertifiedCompile
open HeytingLean.Meta.LeanTT0.ExportCAB

structure Config where
  outDir : String := "dist/euler_sheaf_surreal_export"
  generateCAB : Bool := true
  writeMiniCRepr : Bool := false
deriving Repr

private def usage : String :=
  String.intercalate "\n"
    [ "euler_sheaf_surreal_export"
    , ""
    , "Emits a certified Euler/Sheaf/Surreal depth-10 kernel bundle."
    , ""
    , "Outputs:"
    , "  - kernel.c"
    , "  - kernel.h"
    , "  - driver.c"
    , "  - expected.txt"
    , "  - provenance.json"
    , "  - certificate.json (if --cab)"
    , ""
    , "Flags:"
    , "  --out <dir>      output directory (relative to repo root unless absolute)"
    , "  --cab            enable CAB certificate (default: yes)"
    , "  --no-cab         disable CAB certificate"
    , "  --minic-repr     emit minic.repr.txt"
    , "  --no-minic-repr  skip minic.repr.txt (default)"
    , "  --help           show this message"
    ]

private partial def parseArgs (args : List String) (cfg : Config := {}) : IO (Config × Bool) :=
  match args with
  | [] => pure (cfg, false)
  | "--" :: rest => parseArgs rest cfg
  | "--help" :: _ => pure (cfg, true)
  | "--out" :: dir :: rest => parseArgs rest { cfg with outDir := dir }
  | "--cab" :: rest => parseArgs rest { cfg with generateCAB := true }
  | "--no-cab" :: rest => parseArgs rest { cfg with generateCAB := false }
  | "--minic-repr" :: rest => parseArgs rest { cfg with writeMiniCRepr := true }
  | "--no-minic-repr" :: rest => parseArgs rest { cfg with writeMiniCRepr := false }
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

private def writeFile (path : System.FilePath) (contents : String) : IO Unit := do
  let some parent := path.parent
    | throw <| IO.userError s!"could not compute parent directory for {path}"
  IO.FS.createDirAll parent
  IO.FS.writeFile path contents

private abbrev NatTy : HeytingLean.Core.Ty := HeytingLean.Core.Ty.nat
private abbrev BoolTy : HeytingLean.Core.Ty := HeytingLean.Core.Ty.bool

private def mkEq1 (k : Nat) : LambdaIR.Term [NatTy] BoolTy :=
  LambdaIR.Term.app
    (LambdaIR.Term.app LambdaIR.Term.primEqNat (LambdaIR.Term.var HeytingLean.Core.Var.vz))
    (LambdaIR.Term.constNat k)

private def mkEq2First (k : Nat) : LambdaIR.Term [NatTy, NatTy] BoolTy :=
  LambdaIR.Term.app
    (LambdaIR.Term.app LambdaIR.Term.primEqNat
      (LambdaIR.Term.var (HeytingLean.Core.Var.vs HeytingLean.Core.Var.vz)))
    (LambdaIR.Term.constNat k)

private def mkEq2Second (k : Nat) : LambdaIR.Term [NatTy, NatTy] BoolTy :=
  LambdaIR.Term.app
    (LambdaIR.Term.app LambdaIR.Term.primEqNat (LambdaIR.Term.var HeytingLean.Core.Var.vz))
    (LambdaIR.Term.constNat k)

private def mkIsBoolEq1 (k : Nat) : IsBoolExpr (mkEq1 k) :=
  IsBoolExpr.eqNat IsNatExpr.var (IsNatExpr.constNat k)

private def mkIsBoolEq2First (k : Nat) : IsBoolExpr₂ (mkEq2First k) :=
  IsBoolExpr₂.eqNat IsNatExpr₂.varFirst (IsNatExpr₂.constNat k)

private def mkIsBoolEq2Second (k : Nat) : IsBoolExpr₂ (mkEq2Second k) :=
  IsBoolExpr₂.eqNat IsNatExpr₂.varSecond (IsNatExpr₂.constNat k)

private structure NatBodyWithProof where
  term : LambdaIR.Term [NatTy] NatTy
  proof : IsNatBody term

private structure NatBody2WithProof where
  term : LambdaIR.Term [NatTy, NatTy] NatTy
  proof : IsNatBody₂ term

private def mkConstBody (v : Nat) : NatBodyWithProof :=
  { term := LambdaIR.Term.constNat v
    proof := IsNatBody.expr (IsNatExpr.constNat v) }

private def mkConstBody2 (v : Nat) : NatBody2WithProof :=
  { term := LambdaIR.Term.constNat v
    proof := IsNatBody₂.expr (IsNatExpr₂.constNat v) }

private def mkTableBody1 (defaultVal : Nat) : List (Nat × Nat) → NatBodyWithProof
  | [] => mkConstBody defaultVal
  | (k, v) :: rest =>
      let c := mkEq1 k
      let thenB := mkConstBody v
      let elseB := mkTableBody1 defaultVal rest
      { term := LambdaIR.Term.if_ c thenB.term elseB.term
        proof := IsNatBody.if_ (mkIsBoolEq1 k) thenB.proof elseB.proof }

private def mkRowBody2 (defaultVal : Nat) : List (Nat × Nat) → NatBody2WithProof
  | [] => mkConstBody2 defaultVal
  | (k, v) :: rest =>
      let c := mkEq2Second k
      let thenB := mkConstBody2 v
      let elseB := mkRowBody2 defaultVal rest
      { term := LambdaIR.Term.if_ c thenB.term elseB.term
        proof := IsNatBody₂.if_ (mkIsBoolEq2Second k) thenB.proof elseB.proof }

private def mkTableBody2 (defaultVal : Nat) : List (Nat × List (Nat × Nat)) → NatBody2WithProof
  | [] => mkConstBody2 defaultVal
  | (k, row) :: rest =>
      let c := mkEq2First k
      let thenB := mkRowBody2 defaultVal row
      let elseB := mkTableBody2 defaultVal rest
      { term := LambdaIR.Term.if_ c thenB.term elseB.term
        proof := IsNatBody₂.if_ (mkIsBoolEq2First k) thenB.proof elseB.proof }

private def mkNatFunFromTable (pairs : List (Nat × Nat)) (defaultVal : Nat) :
    { t : LambdaIR.Term [] (HeytingLean.Core.Ty.arrow NatTy NatTy) // IsNatFun t } :=
  let body := mkTableBody1 defaultVal pairs
  ⟨LambdaIR.Term.lam body.term, ⟨body.term, rfl, body.proof⟩⟩

private def mkNat2FunFromRows (rows : List (Nat × List (Nat × Nat))) (defaultVal : Nat) :
    { t : LambdaIR.Term [] (HeytingLean.Core.Ty.arrow NatTy (HeytingLean.Core.Ty.arrow NatTy NatTy))
    // IsNat2Fun t } :=
  let body := mkTableBody2 defaultVal rows
  ⟨LambdaIR.Term.lam (LambdaIR.Term.lam body.term), ⟨body.term, rfl, body.proof⟩⟩

private def domainVals : List Nat :=
  List.range (maxDepth + 1)

private def projectPairs : List (Nat × Nat) :=
  domainVals.map (fun k => (k, projectDepth10 k))

private def complementPairs : List (Nat × Nat) :=
  domainVals.map (fun k => (k, complementDepth10 k))

private def shiftPairs : List (Nat × Nat) :=
  domainVals.map (fun k => (k, eulerShiftDepth10 k))

private def compatRows : List (Nat × List (Nat × Nat)) :=
  domainVals.map (fun a =>
    (a, domainVals.map (fun b => (b, compatPenaltyDepth10 a b))))

private def headerSource (funs : List CFun) : String :=
  let protos :=
    funs.map (fun f =>
      let params :=
        if f.params.isEmpty then
          "void"
        else
          String.intercalate ", " (f.params.map (fun p => s!"long long {p}"))
      s!"long long {f.name}({params});")
  String.intercalate "\n"
    ([ "#pragma once"
     , ""
     , "#ifdef __cplusplus"
     , "extern \"C\" {"
     , "#endif"
     , ""
     ] ++ protos ++
     [ ""
     , "#ifdef __cplusplus"
     , "}"
     , "#endif"
     , ""
     ])

private def driverSource : String :=
  String.intercalate "\n"
    [ "#include <stdio.h>"
    , "#include \"kernel.h\""
    , ""
    , "int main(void) {"
    , "  printf(\"%lld\\n\", heyting_set_project(17));"
    , "  printf(\"%lld\\n\", heyting_surreal_complement(3));"
    , "  printf(\"%lld\\n\", heyting_euler_shift(10));"
    , "  printf(\"%lld\\n\", heyting_compat_penalty(3, 7));"
    , "  printf(\"%lld\\n\", heyting_compat_penalty(3, 4));"
    , "  return 0;"
    , "}"
    , ""
    ]

private def expectedOutput : String :=
  String.intercalate "\n" ["10", "7", "0", "0", "1"] ++ "\n"

private def provenanceJson : Lean.Json :=
  Lean.Json.mkObj
    [ ("bundle_id", Lean.Json.str "euler_sheaf_surreal_depth10")
    , ("description", Lean.Json.str "Certified depth-10 Euler/Sheaf/Surreal kernel export.")
    , ("lean_modules",
        Lean.Json.arr #[
          Lean.Json.str "HeytingLean.Experiments.EulerSheafSurreal.GenerativeControls",
          Lean.Json.str "HeytingLean.Experiments.EulerSheafSurreal.Kernel",
          Lean.Json.str "HeytingLean.LambdaIR.Compile",
          Lean.Json.str "HeytingLean.Meta.LeanTT0.ExportCAB"
        ])
    , ("lean_theorems",
        Lean.Json.arr #[
          Lean.Json.str "HeytingLean.Experiments.EulerSheafSurreal.projectDepth10_idempotent",
          Lean.Json.str "HeytingLean.Experiments.EulerSheafSurreal.complementDepth10_involutive_to_projected",
          Lean.Json.str "HeytingLean.Experiments.EulerSheafSurreal.compatPenaltyDepth10_self_zero",
          Lean.Json.str "HeytingLean.Experiments.EulerSheafSurreal.compatPenaltyDepth10_complement_zero",
          Lean.Json.str "HeytingLean.Experiments.EulerSheafSurreal.eulerSheafSurrealStep_in_range",
          Lean.Json.str "HeytingLean.Experiments.EulerSheafSurreal.reentry_lane_glues",
          Lean.Json.str "HeytingLean.Ontology.reentry_nucleus_euler_sheaf_glue",
          Lean.Json.str "HeytingLean.Ontology.reentry_driverWitness",
          Lean.Json.str "HeytingLean.Ontology.reentry_driverWitness_sheafGlue",
          Lean.Json.str "HeytingLean.Ontology.reentry_driverWitness_ratchetTrajectory",
          Lean.Json.str "HeytingLean.Experiments.EulerSheafSurreal.psrPenalty_zero_iff",
          Lean.Json.str "HeytingLean.Experiments.EulerSheafSurreal.controlObjective_of_perfect",
          Lean.Json.str "HeytingLean.Experiments.EulerSheafSurreal.psrPenalty_zero_of_proof"
        ])
    , ("c_api",
        Lean.Json.arr #[
          Lean.Json.str "heyting_set_project(n)",
          Lean.Json.str "heyting_surreal_complement(n)",
          Lean.Json.str "heyting_euler_shift(n)",
          Lean.Json.str "heyting_compat_penalty(a,b)"
        ])
    , ("notes",
        Lean.Json.arr #[
          Lean.Json.str "All runtime functions are emitted from certified Nat/Nat2 LambdaIR fragments.",
          Lean.Json.str "Depth fixed to 10 per experiment design."
        ])
    ]

def main (argv : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs argv
  try
    let (cfg, showHelp) ← parseArgs args
    if showHelp then
      IO.println usage
      return (0 : UInt32)

    let outDir ← resolveOutDir cfg.outDir
    let kernelCPath := outDir / "kernel.c"
    let kernelHPath := outDir / "kernel.h"
    let driverCPath := outDir / "driver.c"
    let expectedPath := outDir / "expected.txt"
    let provenancePath := outDir / "provenance.json"

    let tProject := mkNatFunFromTable projectPairs maxDepth
    let tComplement := mkNatFunFromTable complementPairs 0
    let tShift := mkNatFunFromTable shiftPairs 0
    let tCompat := mkNat2FunFromRows compatRows 1

    let fProject :=
      (compileNat1Fun (funName := "heyting_set_project") (paramName := "n")
        (t := tProject.val) tProject.property).val
    let fComplement :=
      (compileNat1Fun (funName := "heyting_surreal_complement") (paramName := "n")
        (t := tComplement.val) tComplement.property).val
    let fShift :=
      (compileNat1Fun (funName := "heyting_euler_shift") (paramName := "n")
        (t := tShift.val) tShift.property).val
    let fCompat :=
      (compileNat2Fun (funName := "heyting_compat_penalty")
        (t := tCompat.val) tCompat.property).val

    let funsMinic : List HeytingLean.MiniC.Fun := [fProject, fComplement, fShift, fCompat]
    let funsC : List CFun := funsMinic.map HeytingLean.MiniC.ToC.compileFun

    let cHeader :=
      String.intercalate "\n"
        [ "/* Generated by HeytingLean (euler_sheaf_surreal_export)"
        , "   Certified LambdaIR Nat/Nat2 fragment kernel (depth 10)."
        , "*/"
        , ""
        , "#include \"kernel.h\""
        , ""
        ]
    let cSource := cHeader ++ Emit.funDefs funsC ++ "\n"

    writeFile kernelCPath cSource
    writeFile kernelHPath (headerSource funsC)
    writeFile driverCPath driverSource
    writeFile expectedPath expectedOutput
    writeFile provenancePath (Lean.Json.pretty provenanceJson)

    IO.println s!"[euler_sheaf_surreal_export] wrote {kernelCPath}"
    IO.println s!"[euler_sheaf_surreal_export] wrote {kernelHPath}"
    IO.println s!"[euler_sheaf_surreal_export] wrote {driverCPath}"
    IO.println s!"[euler_sheaf_surreal_export] wrote {expectedPath}"
    IO.println s!"[euler_sheaf_surreal_export] wrote {provenancePath}"

    let mut artifacts : List Artifact := [
      { name := "kernel.c", content := cSource },
      { name := "kernel.h", content := headerSource funsC },
      { name := "driver.c", content := driverSource },
      { name := "expected.txt", content := expectedOutput },
      { name := "provenance.json", content := Lean.Json.pretty provenanceJson }
    ]

    if cfg.writeMiniCRepr then
      let minicPath := outDir / "minic.repr.txt"
      let minicRepr := reprStr funsMinic ++ "\n"
      writeFile minicPath minicRepr
      IO.println s!"[euler_sheaf_surreal_export] wrote {minicPath}"
      artifacts := artifacts ++ [{ name := "minic.repr.txt", content := minicRepr }]

    if cfg.generateCAB then
      let cert := generateCertificate
        "euler_sheaf_surreal_depth10"
        artifacts
        [ "HeytingLean.Experiments.EulerSheafSurreal.projectDepth10_idempotent"
        , "HeytingLean.Experiments.EulerSheafSurreal.complementDepth10_involutive_to_projected"
        , "HeytingLean.Experiments.EulerSheafSurreal.compatPenaltyDepth10_self_zero"
        , "HeytingLean.Experiments.EulerSheafSurreal.compatPenaltyDepth10_complement_zero"
        , "HeytingLean.Experiments.EulerSheafSurreal.psrPenalty_zero_iff"
        , "HeytingLean.Experiments.EulerSheafSurreal.controlObjective_of_perfect"
        , "HeytingLean.Experiments.EulerSheafSurreal.psrPenalty_zero_of_proof"
        , "HeytingLean.LambdaIR.NatCompileFragCorrectness.compileNatFunFrag_correct"
        , "HeytingLean.LambdaIR.Nat2CompileFragCorrectness.compileNat2FunFrag_correct"
        ]
        [ "HeytingLean.CLI.EulerSheafSurrealExportMain"
        , "HeytingLean.Experiments.EulerSheafSurreal.GenerativeControls"
        , "HeytingLean.Experiments.EulerSheafSurreal.Kernel"
        ]
        "Certified depth-10 Euler/Sheaf/Surreal kernel export bundle."
      let certPath := outDir / "certificate.json"
      writeFile certPath (Lean.Json.pretty cert)
      IO.println s!"[euler_sheaf_surreal_export] wrote {certPath}"

    return (0 : UInt32)
  catch e =>
    IO.eprintln s!"[euler_sheaf_surreal_export] error: {e}"
    return (1 : UInt32)

end EulerSheafSurrealExport
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.EulerSheafSurrealExport.main args
