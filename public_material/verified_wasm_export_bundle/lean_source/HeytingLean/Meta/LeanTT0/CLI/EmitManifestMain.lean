import Lean
import Lean.Data.Json
import HeytingLean.Meta.LeanTT0.Hash
import HeytingLean.CLI.Args

/-!
  tt0_emit_manifest: emits a reproducible manifest.json capturing
  toolchain, dependency revision, and CAB/kernel digests.
-/

namespace HeytingLean.Meta.LeanTT0.CLI
namespace EmitManifestMain

open Lean

private def usage : String :=
  String.intercalate "\n"
    [ "tt0_emit_manifest"
    , ""
    , "Emit a reproducible manifest.json capturing toolchain, dependency revision, and CAB/kernel digests."
    , ""
    , "Usage:"
    , "  tt0_emit_manifest --cab CAB.json --kernel KERNEL.json --out OUT_DIR [--tensorgraph RELPATH ...]"
    , ""
    , "Notes:"
    , "  - `--tensorgraph` paths are relative to the bundle root (= parent of `--out`)."
    , "  - With no arguments, prints this help and exits 0 (Dev Mode smoke-run)."
    ]

private def readFileTrim (p : System.FilePath) : IO String := do
  let s ← IO.FS.readFile p
  pure (s.trim)

private def readMathlibRev? : IO (Option String) := do
  let p := System.FilePath.mk "lake-manifest.json"
  try
    let s ← IO.FS.readFile p
    match Json.parse s with
    | .error _ => pure none
    | .ok j =>
      let arr := match j.getObjVal? "packages" with | .ok (.arr a) => a | _ => #[]
      for i in [0:arr.size] do
        match arr[i]! |>.getObj? with
        | .ok o =>
          let isMathlib := match o.get? "name" with | some (.str n) => (n == "mathlib") | _ => false
          if isMathlib then
            match o.get? "rev" with
            | some (.str r) => return some r
            | _ => pure ()
          else
            pure ()
        | .error _ => pure ()
      pure none
  catch _ => pure none

private def hexOf (ba : ByteArray) : String :=
  let parts := ba.toList.map (fun b =>
    let s := (Nat.toDigits 16 b.toNat).asString
    if s.length = 1 then "0" ++ s else s)
  "0x" ++ String.intercalate "" parts

private def hexField (o : Json) (k : String) : Option String :=
  match o.getObjVal? k with | .ok (.str s) => some s | _ => none

private structure ManifestArgs where
  cabPath : String := "out/cab.json"
  kerPath : String := "out/kernel.json"
  outDir : String := "out"
  /-- Tensor graph paths, relative to the bundle root (= parent of `outDir`). -/
  tensorGraphs : List String := []
  deriving Repr

private def parseManifestArgs (xs : List String) (acc : ManifestArgs := {}) : ManifestArgs :=
  match xs with
  | [] => acc
  | "--cab" :: p :: xs' => parseManifestArgs xs' { acc with cabPath := p }
  | "--kernel" :: p :: xs' => parseManifestArgs xs' { acc with kerPath := p }
  | "--out" :: d :: xs' => parseManifestArgs xs' { acc with outDir := d }
  | "--tensorgraph" :: p :: xs' =>
      parseManifestArgs xs' { acc with tensorGraphs := acc.tensorGraphs ++ [p] }
  | _ :: xs' => parseManifestArgs xs' acc

def main (args : List String) : IO UInt32 := do
  let argv := HeytingLean.CLI.stripLakeArgs args
  if argv.isEmpty || argv.any (· == "--help") then
    IO.println usage
    return 0
  -- Args:
  --   --cab <path> --kernel <path> --out <dir>
  --   [--tensorgraph <bundle-relative-path>]*
  let margs := parseManifestArgs argv
  let cabPath := margs.cabPath
  let kerPath := margs.kerPath
  let outDir := margs.outDir
  IO.FS.createDirAll outDir

  let outDirFp := System.FilePath.mk outDir
  let bundleRootFp := outDirFp.parent.getD outDirFp

  -- toolchain + dep rev
  let toolchain ←
    try
      readFileTrim (System.FilePath.mk "lean-toolchain")
    catch _ =>
      pure "unknown"
  let mathlibRev ← (readMathlibRev?) >>= (fun x => pure (x.getD "unknown"))

  let fail {α} (msg : String) : ExceptT UInt32 IO α := do
    ExceptT.lift (IO.eprintln msg)
    throw 2

  let readFileE (label path : String) : ExceptT UInt32 IO String := do
    try
      ExceptT.lift (IO.FS.readFile path)
    catch e =>
      fail s!"{label} read error at {path}: {e}"

  let parseJsonE (label : String) (raw : String) : ExceptT UInt32 IO Json := do
    match Json.parse raw with
    | .ok j => pure j
    | .error e => fail s!"{label}: {e}"

  let expectObjE (label : String) (j : Json) : ExceptT UInt32 IO Unit := do
    match j.getObj? with
    | .ok _ => pure ()
    | .error _ => fail s!"{label}: not object"

  let job : ExceptT UInt32 IO Unit := do
    -- read cab + kernel digests
    let cabRaw ← readFileE "cab" cabPath
    let cabJ ← parseJsonE "cab" cabRaw
    expectObjE "cab" cabJ
    let fnd := hexField cabJ "foundationCommitment" |>.getD "0x"
    let rrt := hexField cabJ "rulesRoot" |>.getD "0x"

    let kerRaw ← readFileE "kernel" kerPath
    let kerJ ← parseJsonE "kernel" kerRaw
    expectObjE "kernel" kerJ
    let kcm := hexField kerJ "kernelCommitment" |>.getD "0x"

    -- optional tensor-graph hashes (sha256 over bytes)
    let mut tgObjs : Array Json := #[]
    for rel in margs.tensorGraphs do
      let tgPath := toString (bundleRootFp / rel)
      let bytes ←
        try
          ExceptT.lift (IO.FS.readBinFile (System.FilePath.mk tgPath))
        catch e =>
          fail s!"tensorgraph read error at {tgPath}: {e}"
      let digest := HeytingLean.Meta.LeanTT0.sha256 bytes
      tgObjs := tgObjs.push (Json.mkObj
        [ ("path", Json.str rel)
        , ("sha256", Json.str (hexOf digest))
        ])

    let manifest := Json.mkObj [
      ("schema", Json.str "LoF/Manifest/v1"),
      ("lean_toolchain", Json.str toolchain),
      ("mathlib_rev", Json.str mathlibRev),
      ("platform", Json.mkObj [("os", Json.str ("linux")), ("arch", Json.str ("x86_64"))]),
      ("algos", Json.mkObj [("hash", Json.str "sha256"), ("merkle", Json.str "sha256"), ("poseidon", Json.str "sha256-domain")]),
      ("foundationCommitment", Json.str fnd),
      ("rulesRoot", Json.str rrt),
      ("kernelCommitment", Json.str kcm),
      ("tensor_graphs", Json.arr tgObjs)
    ]
    let outPath := s!"{outDir}/manifest.json"
    ExceptT.lift (IO.FS.writeFile outPath (Json.compress manifest))
    ExceptT.lift (IO.println s!"Wrote {outPath}")

  match (← job.run) with
  | .ok _ => pure 0
  | .error c => pure c

end EmitManifestMain
end HeytingLean.Meta.LeanTT0.CLI

def main (args : List String) : IO UInt32 :=
  HeytingLean.Meta.LeanTT0.CLI.EmitManifestMain.main args
