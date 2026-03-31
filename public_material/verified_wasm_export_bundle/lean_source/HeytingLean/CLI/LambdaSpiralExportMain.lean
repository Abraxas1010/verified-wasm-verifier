import Init.Data.SInt.Float

import HeytingLean.C.Emit
import HeytingLean.CLI.Args
import HeytingLean.Compiler.TensorLogic.ParseFacts
import HeytingLean.LambdaIR.Compile
import HeytingLean.LambdaIR.NatFunFragment
import HeytingLean.Meta.LeanTT0.ExportCAB
import HeytingLean.MiniC.ToC

/-!
# `lambda_spiral_export` (Kernel Bundle v1)

Goal: route the IteratedVirtual “spiral/helix embedding” through the existing

`Lean → LambdaIR (Nat fragment) → MiniC → C`

*certified* compiler path, then emit an auditable C bundle plus a CAB certificate.

Important constraint: the certified LambdaIR compiler fragment is **Nat→Nat** with:
- constants, addition, equality, and `if`.

So we cannot compute `cos/sin` inside the fragment. Instead we:
1. Precompute a finite table of helix points in Lean (using `Float.cos/sin`);
2. Quantize each coordinate to a signed fixed-point `Int`;
3. Encode signed ints into `Nat` via zigzag encoding;
4. Emit three certified Nat→Nat functions `heyting_spiral_{x,y,z}` that map index `k` to the
   zigzag-encoded coordinate at that index (via nested `if (k==i) then ... else ...`).

This yields a pipeline-produced C library where the *runtime* is purely the certified Nat fragment,
yet the produced embedding still instantiates the spiral geometry for a chosen finite range.
-/

namespace HeytingLean
namespace CLI
namespace LambdaSpiralExport

open HeytingLean
open HeytingLean.C
open HeytingLean.C.Emit
open HeytingLean.Certified
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.NatFunFragment
open HeytingLean.LambdaIR.CertifiedCompile
open HeytingLean.Meta.LeanTT0.ExportCAB
open HeytingLean.Compiler.TensorLogic

structure Config where
  outDir : String := "dist/lambda_spiral_export"
  n : Nat := 256
  step : Float := 0.35
  pitch : Float := 0.15
  scale : Float := 1000000.0
  generateCAB : Bool := true
  writeMiniCRepr : Bool := false
deriving Repr

private def usage : String :=
  String.intercalate "\n"
    [ "lambda_spiral_export"
    , ""
    , "Emits a certified LambdaIR→MiniC→C kernel bundle implementing a finite spiral embedding table."
    , ""
    , "Outputs:"
    , "  - kernel.c        (C source, no main)"
    , "  - kernel.h        (C header for FFI)"
    , "  - driver.c        (tiny test main)"
    , "  - expected.txt    (expected stdout)"
    , "  - minic.repr.txt  (debug repr of the MiniC kernel)"
    , "  - provenance.json (Lean provenance metadata)"
    , "  - certificate.json (CAB, if enabled)"
    , ""
    , "Flags:"
    , "  --out <dir>       output directory (relative to repo root unless absolute)"
    , "  --n <Nat>         number of steps (default: 512)"
    , "  --step <Float>    angular step in radians (default: 0.35)"
    , "  --pitch <Float>   z pitch per radian (default: 0.15)"
    , "  --scale <Float>   fixed-point scale (default: 1e6)"
    , "  --cab             enable CAB certificate (default: yes)"
    , "  --no-cab          disable CAB certificate"
    , "  --minic-repr      write minic.repr.txt (default: no)"
    , "  --no-minic-repr   do not write minic.repr.txt"
    , "  --help            show this message"
    ]

private partial def parseArgs (args : List String) (cfg : Config := {}) : IO (Config × Bool) :=
  match args with
  | [] => pure (cfg, false)
  | "--" :: rest => parseArgs rest cfg
  | "--help" :: _ => pure (cfg, true)
  | "--out" :: dir :: rest => parseArgs rest { cfg with outDir := dir }
  | "--n" :: v :: rest =>
      match String.toNat? v with
      | some n => parseArgs rest { cfg with n := n }
      | none => throw <| IO.userError s!"invalid --n {v}"
  | "--step" :: v :: rest =>
      match parseFloatLit v with
      | .ok f => parseArgs rest { cfg with step := f }
      | .error _ => throw <| IO.userError s!"invalid --step {v}"
  | "--pitch" :: v :: rest =>
      match parseFloatLit v with
      | .ok f => parseArgs rest { cfg with pitch := f }
      | .error _ => throw <| IO.userError s!"invalid --pitch {v}"
  | "--scale" :: v :: rest =>
      match parseFloatLit v with
      | .ok f => parseArgs rest { cfg with scale := f }
      | .error _ => throw <| IO.userError s!"invalid --scale {v}"
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

private def zigzagEncode (i : Int) : Nat :=
  if _h : 0 ≤ i then
    2 * i.toNat
  else
    (2 * (-i).toNat) - 1

private abbrev NatTy : HeytingLean.Core.Ty := HeytingLean.Core.Ty.nat
private abbrev BoolTy : HeytingLean.Core.Ty := HeytingLean.Core.Ty.bool

private def mkEq (k : Nat) : LambdaIR.Term [NatTy] BoolTy :=
  LambdaIR.Term.app
    (LambdaIR.Term.app LambdaIR.Term.primEqNat (LambdaIR.Term.var HeytingLean.Core.Var.vz))
    (LambdaIR.Term.constNat k)

private def mkIsBoolEq (k : Nat) : IsBoolExpr (mkEq k) :=
  IsBoolExpr.eqNat IsNatExpr.var (IsNatExpr.constNat k)

private structure NatBodyWithProof where
  term : LambdaIR.Term [NatTy] NatTy
  proof : IsNatBody term

private def mkConstBody (v : Nat) : NatBodyWithProof :=
  { term := LambdaIR.Term.constNat v
    proof := IsNatBody.expr (IsNatExpr.constNat v) }

private def mkTableBody : List (Nat × Nat) → NatBodyWithProof
  | [] =>
      -- Default value if index not in table
      mkConstBody 0
  | (k, v) :: rest =>
      let c := mkEq k
      let hc := mkIsBoolEq k
      let thenB := mkConstBody v
      let elseB := mkTableBody rest
      { term := LambdaIR.Term.if_ c thenB.term elseB.term
        proof := IsNatBody.if_ hc thenB.proof elseB.proof }

private def mkNatFunFromTable (pairs : List (Nat × Nat)) :
    { t : LambdaIR.Term [] (HeytingLean.Core.Ty.arrow NatTy NatTy) // IsNatFun t } :=
  let body := mkTableBody pairs
  ⟨LambdaIR.Term.lam body.term, ⟨body.term, rfl, body.proof⟩⟩

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

private def driverSource (n : Nat) : String :=
  String.intercalate "\n"
    [ "#include <inttypes.h>"
    , "#include <stdio.h>"
    , "#include \"kernel.h\""
    , ""
    , "static int64_t zigzag_decode(uint64_t zz) {"
    , "  if (zz & 1ULL) {"
    , "    return -(int64_t)((zz + 1ULL) >> 1);"
    , "  } else {"
    , "    return (int64_t)(zz >> 1);"
    , "  }"
    , "}"
    , ""
    , "int main(void) {"
    , "  /* Print first and last points (decoded) as a smoke test. */"
    , "  uint64_t x0 = (uint64_t)heyting_spiral_x(0);"
    , "  uint64_t y0 = (uint64_t)heyting_spiral_y(0);"
    , "  uint64_t z0 = (uint64_t)heyting_spiral_z(0);"
    , "  printf(\"%\" PRId64 \" %\" PRId64 \" %\" PRId64 \"\\n\", zigzag_decode(x0), zigzag_decode(y0), zigzag_decode(z0));"
    , ""
    , s!"  uint64_t xn = (uint64_t)heyting_spiral_x({n});"
    , s!"  uint64_t yn = (uint64_t)heyting_spiral_y({n});"
    , s!"  uint64_t zn = (uint64_t)heyting_spiral_z({n});"
    , "  printf(\"%\" PRId64 \" %\" PRId64 \" %\" PRId64 \"\\n\", zigzag_decode(xn), zigzag_decode(yn), zigzag_decode(zn));"
    , "  return 0;"
    , "}"
    , ""
    ]

private def provenanceJson (cfg : Config) : Lean.Json :=
  Lean.Json.mkObj
    [ ("bundle_id", Lean.Json.str "lambda_spiral_export_v1")
    , ("description", Lean.Json.str "Certified LambdaIR→MiniC→C export of a finite spiral embedding table (zigzag-encoded fixed-point coordinates).")
    , ("params",
        Lean.Json.mkObj
          [ ("n", Lean.Json.num cfg.n)
          , ("step", Lean.Json.str (toString cfg.step))
          , ("pitch", Lean.Json.str (toString cfg.pitch))
          , ("scale", Lean.Json.str (toString cfg.scale))
          ])
    , ("lean_modules",
        Lean.Json.arr #[
          Lean.Json.str "HeytingLean.LambdaIR.Compile",
          Lean.Json.str "HeytingLean.LambdaIR.NatCompileFragCorrectness",
          Lean.Json.str "HeytingLean.MiniC.ToC",
          Lean.Json.str "HeytingLean.Meta.LeanTT0.ExportCAB"
        ])
    , ("c_api",
        Lean.Json.arr #[
          Lean.Json.str "heyting_spiral_x(k) -> zigzag(scaled x_k)",
          Lean.Json.str "heyting_spiral_y(k) -> zigzag(scaled y_k)",
          Lean.Json.str "heyting_spiral_z(k) -> zigzag(scaled z_k)"
        ])
    , ("notes",
        Lean.Json.arr #[
          Lean.Json.str "This uses the certified Nat fragment compiler; cos/sin are precomputed in Lean, then embedded as Nat constants.",
          Lean.Json.str "The emitted C runtime is purely the certified Nat fragment (addition/equality/if)."
        ])
    ]

private def quantizeSignedInt (x : Float) (scale : Float) : Int :=
  (Float.toInt64 (x * scale)).toInt

private def pointTable (cfg : Config) : List (Nat × (Int × Int × Int)) :=
  (List.range (cfg.n + 1)).map fun k =>
    let t := cfg.step * Float.ofNat k
    let x := quantizeSignedInt (Float.cos t) cfg.scale
    let y := quantizeSignedInt (Float.sin t) cfg.scale
    let z := quantizeSignedInt (cfg.pitch * t) cfg.scale
    (k, (x, y, z))

private def mkCoordPairs (table : List (Nat × (Int × Int × Int))) (proj : (Int × Int × Int) → Int) :
    List (Nat × Nat) :=
  table.map fun (k, p) => (k, zigzagEncode (proj p))

def main (argv : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs argv
  try
    let (cfg, showHelp) ← parseArgs args
    if showHelp then
      IO.println usage
      return (0 : UInt32)

    if cfg.n > 5000 then
      throw <| IO.userError s!"n too large for nested-if table export: {cfg.n} (try ≤ 5000)"
    if cfg.scale ≤ 0.0 then
      throw <| IO.userError s!"scale must be positive"

    let outDir ← resolveOutDir cfg.outDir
    let kernelCPath := outDir / "kernel.c"
    let kernelHPath := outDir / "kernel.h"
    let driverCPath := outDir / "driver.c"
    let expectedPath := outDir / "expected.txt"
    let provenancePath := outDir / "provenance.json"

    let tbl := pointTable cfg
    let xs := mkCoordPairs tbl (fun (x, _, _) => x)
    let ys := mkCoordPairs tbl (fun (_, y, _) => y)
    let zs := mkCoordPairs tbl (fun (_, _, z) => z)

    let tx := mkNatFunFromTable xs
    let ty := mkNatFunFromTable ys
    let tz := mkNatFunFromTable zs

    let fx := (compileNat1Fun (funName := "heyting_spiral_x") (paramName := "k") (t := tx.val) tx.property).val
    let fy := (compileNat1Fun (funName := "heyting_spiral_y") (paramName := "k") (t := ty.val) ty.property).val
    let fz := (compileNat1Fun (funName := "heyting_spiral_z") (paramName := "k") (t := tz.val) tz.property).val

    let funsMinic : List HeytingLean.MiniC.Fun := [fx, fy, fz]
    let funsC : List CFun := funsMinic.map HeytingLean.MiniC.ToC.compileFun

    let cHeader :=
      String.intercalate "\n"
        [ "/* Generated by HeytingLean (lambda_spiral_export)"
        , "   Kernel bundle v1: certified LambdaIR Nat fragment (if/eq/add) with precomputed constants."
        , "*/"
        , ""
        , "#include \"kernel.h\""
        , ""
        ]
    let cSource := cHeader ++ Emit.funDefs funsC ++ "\n"

    writeFile kernelCPath cSource
    writeFile kernelHPath (headerSource funsC)
    writeFile driverCPath (driverSource cfg.n)

    -- Expected output: decoded (x0,y0,z0) and (xn,yn,zn) as Ints.
    let p0 := tbl.headD (0, (0, 0, 0))
    let pn := tbl.getLastD (0, (0, 0, 0))
    let (x0, y0, z0) := p0.2
    let (xn, yn, zn) := pn.2
    writeFile expectedPath (String.intercalate "\n" [s!"{x0} {y0} {z0}", s!"{xn} {yn} {zn}"] ++ "\n")

    writeFile provenancePath (Lean.Json.pretty (provenanceJson cfg))

    IO.println s!"[lambda_spiral_export] wrote {kernelCPath}"
    IO.println s!"[lambda_spiral_export] wrote {kernelHPath}"
    IO.println s!"[lambda_spiral_export] wrote {driverCPath}"
    IO.println s!"[lambda_spiral_export] wrote {expectedPath}"
    IO.println s!"[lambda_spiral_export] wrote {provenancePath}"

    let mut artifacts : List Artifact := [
      { name := "kernel.c", content := cSource },
      { name := "kernel.h", content := headerSource funsC },
      { name := "driver.c", content := driverSource cfg.n },
      { name := "expected.txt", content := String.intercalate "\n" [s!"{x0} {y0} {z0}", s!"{xn} {yn} {zn}"] ++ "\n" },
      { name := "provenance.json", content := Lean.Json.pretty (provenanceJson cfg) }
    ]

    if cfg.writeMiniCRepr then
      let minicPath := outDir / "minic.repr.txt"
      let minicRepr := reprStr funsMinic ++ "\n"
      writeFile minicPath minicRepr
      IO.println s!"[lambda_spiral_export] wrote {minicPath}"
      -- `minic.repr.txt` can be large; include it only if explicitly requested.
      artifacts := artifacts ++ [{ name := "minic.repr.txt", content := minicRepr }]

    if cfg.generateCAB then
      let cert := generateCertificate
        "lambda_spiral_export_v1"
        artifacts
        [ "HeytingLean.LambdaIR.NatCompileFragCorrectness.compileNatFunFrag_correct" ]
        [ "HeytingLean.CLI.LambdaSpiralExportMain" ]
        "Certified LambdaIR Nat fragment: finite spiral embedding lookup table."
      let certPath := outDir / "certificate.json"
      writeFile certPath (Lean.Json.pretty cert)
      IO.println s!"[lambda_spiral_export] wrote {certPath}"

    return (0 : UInt32)
  catch e =>
    IO.eprintln s!"[lambda_spiral_export] error: {e}"
    return (1 : UInt32)

end LambdaSpiralExport
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.LambdaSpiralExport.main args
