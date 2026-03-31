import Lean
import Lean.Data.Json
import HeytingLean.CLI.Args
import HeytingLean.Util.JCS
import HeytingLean.BountyHunter.AlgebraIR
import HeytingLean.BountyHunter.AlgebraIR.SlotRef
import HeytingLean.BountyHunter.YulMini
import HeytingLean.BountyHunter.Solc.ExtractIR
import HeytingLean.BountyHunter.Solc.Audit
import HeytingLean.BountyHunter.Solc.Coverage
import HeytingLean.BountyHunter.Solc.Fixtures
import HeytingLean.BountyHunter.Solc.YulTextMini
import HeytingLean.BountyHunter.AlgebraIR2
import HeytingLean.BountyHunter.Foundry.Gen
import HeytingLean.BountyHunter.Foundry.ParityGen
import HeytingLean.Util.SHA

/-!
# `bounty_hunter_algebrair_cli`

Executable-first Phase 0 entrypoint:
- read an AlgebraIR graph from JSON
- run a dominance-style CEI check
- emit deterministic JSON verdict (+ witness on failure)

This CLI is intentionally minimal and robust to hostile I/O.
-/

open IO
open HeytingLean.BountyHunter.AlgebraIR

private def eprintlnErr (msg : String) : IO Unit :=
  IO.eprintln msg

private def readFileE (path : System.FilePath) : IO (Except String String) := do
  try
    let s ← FS.readFile path
    pure (.ok s)
  catch e =>
    pure (.error s!"read error at {path}: {e}")

private def relPathFromRoot (root path : System.FilePath) : String :=
  -- Best-effort, deterministic relative-path rendering for solc standard-json `sources` keys.
  let normalizeUnitPath (s : String) : String :=
    let parts := s.splitOn "/"
    let rec go (ps : List String) (acc : List String) : List String :=
      match ps with
      | [] => acc.reverse
      | p :: rest =>
          if p = "" || p = "." then
            go rest acc
          else if p = ".." then
            match acc with
            | [] => go rest (".." :: acc)
            | _ :: acc' => go rest acc'
          else
            go rest (p :: acc)
    String.intercalate "/" (go parts [])
  let r := root.normalize.toString
  let p := path.normalize.toString
  if p.startsWith r then
    let rest := p.drop r.length
    normalizeUnitPath (if rest.startsWith "/" then rest.drop 1 else rest)
  else
    p

private def solcSourceUnitKey (root : System.FilePath) (nodeModuleRoots : List System.FilePath) (path : System.FilePath) : String :=
  -- Deterministic key selection for solc standard-json `sources`:
  -- - for files under `root`, use a root-relative unit name;
  -- - for files under any `node_modules` root, use the `node_modules`-relative unit name (e.g. `@openzeppelin/...`);
  -- - otherwise, fall back to an absolute path string.
  let p := path.normalize.toString
  let best : Option System.FilePath :=
    nodeModuleRoots.foldl
      (fun acc nm =>
        let nmS := nm.normalize.toString
        if p.startsWith nmS then
          match acc with
          | none => some nm
          | some cur =>
              if nmS.length > cur.normalize.toString.length then some nm else acc
        else acc)
      none
  match best with
  | some nm => relPathFromRoot nm path
  | none => relPathFromRoot root path

private partial def collectSolFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out : Array System.FilePath := #[]
  for e in (← System.FilePath.readDir dir) do
    if (← e.path.isDir) then
      out := out ++ (← collectSolFiles e.path)
    else if e.path.extension = some "sol" then
      out := out.push e.path
  return out

private partial def stripSolidityComments (src : String) : String :=
  -- Minimal, deterministic comment stripping to support import scanning.
  -- Not a full lexer; good enough for standard Solidity `import "...";` patterns.
  let rec go (cs : List Char) (inLine : Bool) (inBlock : Bool) (acc : List Char) : List Char :=
    match cs with
    | [] => acc.reverse
    | c :: cs' =>
        if inLine then
          if c = '\n' then
            go cs' false false ('\n' :: acc)
          else
            go cs' true false acc
        else if inBlock then
          match c, cs' with
          | '*', '/' :: rest => go rest false false acc
          | _, _ => go cs' false true acc
        else
          match c, cs' with
          | '/', '/' :: rest => go rest true false acc
          | '/', '*' :: rest => go rest false true acc
          | _, _ => go cs' false false (c :: acc)
  String.mk (go src.data false false [])

private partial def scanSolidityImports (src : String) : List String :=
  let cs := (stripSolidityComments src).data
  let rec findQuote (cs : List Char) : Option (Char × List Char) :=
    match cs with
    | [] => none
    | c :: rest =>
        if c = '"' || c = '\'' then some (c, rest) else findQuote rest
  let rec takeUntilQuote (q : Char) (cs : List Char) (acc : List Char) : Option (String × List Char) :=
    match cs with
    | [] => none
    | c :: rest =>
        if c = q then
          some (String.mk acc.reverse, rest)
        else
          takeUntilQuote q rest (c :: acc)
  let rec go (cs : List Char) (acc : List String) : List String :=
    match cs with
    | [] => acc.reverse
    | 'i' :: 'm' :: 'p' :: 'o' :: 'r' :: 't' :: rest =>
        match findQuote rest with
        | none => acc.reverse
        | some (q, afterQ) =>
            match takeUntilQuote q afterQ [] with
            | none => acc.reverse
            | some (p, after) => go after (p :: acc)
    | _ :: rest => go rest acc
  go cs []

private def readFoundryRemappingsE (root : System.FilePath) : IO (List (String × System.FilePath)) := do
  -- Minimal Foundry support: parse `remappings.txt` when present.
  -- Format: `prefix=path` (typically both end with `/`).
  let p := root / System.FilePath.mk "remappings.txt"
  let ok ← p.pathExists
  if !ok then
    return []
  match (← readFileE p) with
  | .error _ => return []
  | .ok content =>
      let mut out : List (String × System.FilePath) := []
      for line in content.splitOn "\n" do
        let t := line.trim
        if t = "" || t.startsWith "#" then
          continue
        match t.splitOn "=" with
        | [lhs, rhs] =>
            let k := lhs.trim
            let v := rhs.trim
            if k = "" || v = "" then
              continue
            out := (k, System.FilePath.mk v) :: out
        | _ => continue
      return out.reverse

private def resolveRemappingCandidates (root : System.FilePath) (remaps : List (String × System.FilePath)) (imp : String) :
    List System.FilePath :=
  let p := System.FilePath.mk imp
  let rec go (rs : List (String × System.FilePath)) (acc : List System.FilePath) : List System.FilePath :=
    match rs with
    | [] => acc.reverse
    | (k, v) :: rest =>
        if imp.startsWith k then
          let suffix := imp.drop k.length
          let suffix := if suffix.startsWith "/" then suffix.drop 1 else suffix
          go rest ((root / v / System.FilePath.mk suffix) :: acc)
        else
          go rest acc
  go remaps [p]

private def resolveImportCandidates (root curDir : System.FilePath) (nodeModuleRoots : List System.FilePath) (imp : String) :
    List System.FilePath :=
  let p := System.FilePath.mk imp
  if imp.startsWith "./" || imp.startsWith "../" then
    [curDir / p]
  else if imp.startsWith "/" then
    [root / System.FilePath.mk (imp.drop 1)]
  else if imp.startsWith "@" then
    [curDir / p, root / p] ++ (nodeModuleRoots.map (fun nm => nm / p))
  else
    [curDir / p, root / p]

private partial def collectImportClosureE
    (root : System.FilePath)
    (nodeModuleRoots : List System.FilePath)
    (remaps : List (String × System.FilePath))
    (todo : List System.FilePath)
    (seen : List String)
    (acc : List System.FilePath)
    : IO (Except String (List System.FilePath)) := do
  match todo with
  | [] => pure (.ok acc.reverse)
  | p :: rest =>
      let key := p.normalize.toString
      if seen.contains key then
        collectImportClosureE root nodeModuleRoots remaps rest seen acc
      else
        let ok ← p.pathExists
        if !ok then
          collectImportClosureE root nodeModuleRoots remaps rest (key :: seen) acc
        else
          match (← readFileE p) with
          | .error e => pure (.error e)
          | .ok content =>
              let curDir := p.parent.getD root
              let mut more : List System.FilePath := []
              for imp in scanSolidityImports content do
                let base := resolveRemappingCandidates root remaps imp
                let cands := (base ++ resolveImportCandidates root curDir nodeModuleRoots imp).eraseDups
                for cand in cands do
                  let okC ← cand.pathExists
                  if okC then
                    more := cand :: more
              collectImportClosureE root nodeModuleRoots remaps (more ++ rest) (key :: seen) (p :: acc)

private def sourcesJsonFromEntryClosureE (dir : System.FilePath) (srcUnit : String) : IO (Except String Lean.Json) := do
  let ok ← dir.pathExists
  if !ok then
    return .error s!"--solc-compile-dir: directory not found: {dir}"
  let entry := dir / System.FilePath.mk srcUnit
  let cwd ← IO.currentDir
  let rec collectNodeModuleRoots (p : System.FilePath) (fuel : Nat) (acc : List System.FilePath) :
      List System.FilePath :=
    if fuel = 0 then
      acc
    else
      let acc := (p / System.FilePath.mk "node_modules") :: acc
      match p.parent with
      | none => acc
      | some p' => collectNodeModuleRoots p' (fuel - 1) acc
  -- Resolve `@openzeppelin/...` and similar imports from multiple likely roots:
  -- - project-local `node_modules` (at or above `--solc-compile-dir`)
  -- - Heyting repo-local `node_modules` (cwd)
  -- This is best-effort: if deps are not present anywhere, we remain OUT_OF_SCOPE.
  let remaps ← readFoundryRemappingsE dir
  let nodeModuleRoots :=
    let fromCompileDir := collectNodeModuleRoots dir 6 []
    let fromCwd := [cwd / System.FilePath.mk "node_modules"]
    (fromCompileDir ++ fromCwd).eraseDups
  match (← collectImportClosureE dir nodeModuleRoots remaps [entry] [] []) with
  | .error e => return .error e
  | .ok ps =>
      let mut pairs : List (String × Lean.Json) := []
      let psSorted := ps.mergeSort (fun a b => decide (a.toString ≤ b.toString))
      for p in psSorted do
        match (← readFileE p) with
        | .error e => return .error e
        | .ok content =>
            -- We use `content` (not `urls`). The solc CLI does not support an import callback,
            -- so `urls` entries can cause "File import callback not supported" failures on
            -- multi-file projects.
            let key := solcSourceUnitKey dir nodeModuleRoots p
            pairs := (key, Lean.Json.mkObj [("content", Lean.Json.str content)]) :: pairs
      return .ok (Lean.Json.mkObj pairs.reverse)

private def sourcesJsonFromDirE (dir : System.FilePath) : IO (Except String Lean.Json) := do
  let ok ← dir.pathExists
  if !ok then
    return .error s!"--solc-compile-dir: directory not found: {dir}"
  let cwd ← IO.currentDir
  let rec collectNodeModuleRoots (p : System.FilePath) (fuel : Nat) (acc : List System.FilePath) :
      List System.FilePath :=
    if fuel = 0 then
      acc
    else
      let acc := (p / System.FilePath.mk "node_modules") :: acc
      match p.parent with
      | none => acc
      | some p' => collectNodeModuleRoots p' (fuel - 1) acc
  let nodeModuleRoots :=
    let fromCompileDir := collectNodeModuleRoots dir 6 []
    let fromCwd := [cwd / System.FilePath.mk "node_modules"]
    (fromCompileDir ++ fromCwd).eraseDups
  let ps ← collectSolFiles dir
  let mut pairs : List (String × Lean.Json) := []
  let psSorted := ps.toList.mergeSort (fun a b => decide (a.toString ≤ b.toString))
  for p in psSorted do
    match (← readFileE p) with
    | .error e => return .error e
    | .ok content =>
        let key := solcSourceUnitKey dir nodeModuleRoots p
        pairs := (key, Lean.Json.mkObj [("content", Lean.Json.str content)]) :: pairs
  return .ok (Lean.Json.mkObj pairs.reverse)

private partial def runSolcStandardJsonE (stdin : String) (cwd? : Option System.FilePath := none) :
    IO (Except String String) := do
  -- NOTE: `IO.Process.output` uses `IO.FS.Handle.readToEnd`, which can truncate stdout
  -- on our solcjs-based toolchain (commonly failing around 64KiB). To make long-corpus
  -- runs robust, we route solc I/O through temp files and only read those files.
  let shQuote := fun (s : String) =>
    "'" ++ (s.replace "'" "'\\''") ++ "'"

  let dropNonJsonPrefix (s : String) : String :=
    let rec go (i : Nat) : List Char → String
      | [] => s
      | c :: cs =>
          if c = '{' || c = '[' then
            s.drop i
          else
            go (i + 1) cs
    go 0 s.data

  let tmpDir ← IO.FS.createTempDir
  try
    let inPath := tmpDir / "solc_in.json"
    let outPath := tmpDir / "solc_out.json"
    let errPath := tmpDir / "solc_err.txt"

    IO.FS.writeFile inPath stdin

    let solcCmd := (← IO.getEnv "SOLC").getD "solc"
    let script :=
      s!"{shQuote solcCmd} --standard-json < {shQuote inPath.toString} > {shQuote outPath.toString} 2> {shQuote errPath.toString}"

    let r ← IO.Process.output
      { cmd := "bash"
      , args := #["-lc", script]
      , cwd := cwd?
      , stdin := .null
      , stdout := .null
      , stderr := .null
      } none

    let stdoutS := (← IO.FS.readFile outPath)
    let stderrS := (← IO.FS.readFile errPath)

    if r.exitCode = 0 then
      pure (.ok (dropNonJsonPrefix stdoutS))
    else
      pure (.error s!"solc failed (code {r.exitCode}): {stderrS}\n{stdoutS}")
  catch e =>
    pure (.error s!"failed to run solc: {e}")
  finally
    IO.FS.removeDirAll tmpDir

private def looksLikeMissingImportError (e : String) : Bool :=
  let s := e.toLower
  let containsSubstr (hay needle : String) : Bool :=
    if needle.isEmpty then
      true
    else
      Id.run do
        let max := hay.length - needle.length
        let mut found := false
        for i in [:max.succ] do
          if (!found) && (hay.drop i).startsWith needle then
            found := true
        return found
  containsSubstr s "source \"" && containsSubstr s "not found"

private def usage : String :=
  String.intercalate "\n"
    [ "usage:"
    , "  bounty_hunter_algebrair_cli --input <file.json> --check-cei (--slot <n> | --slot-expr <expr> | --slot-auto) [--emit-evidence]"
    , "  bounty_hunter_algebrair_cli --example etherstore_vuln|etherstore_fixed --check-cei (--slot <n> | --slot-expr <expr> | --slot-auto) [--emit-evidence]"
    , "  bounty_hunter_algebrair_cli --dump-example etherstore_vuln|etherstore_fixed"
    , "  bounty_hunter_algebrair_cli --roundtrip (--input <file.json> | --example <name>)"
    , "  bounty_hunter_algebrair_cli --selftest"
    , "  bounty_hunter_algebrair_cli --yulmini-input <file.json> [--func <name>] (--emit-algebrair | --check-cei (--slot <n> | --slot-expr <expr> | --slot-auto) [--emit-evidence])"
    , "  bounty_hunter_algebrair_cli --yulmini-example etherstore_vuln|etherstore_fixed [--func <name>] (--emit-algebrair | --check-cei (--slot <n> | --slot-expr <expr> | --slot-auto) [--emit-evidence])"
    , "  bounty_hunter_algebrair_cli --dump-yulmini-example etherstore_vuln|etherstore_fixed"
    , "  bounty_hunter_algebrair_cli --yulmini-roundtrip (--yulmini-input <file.json> | --yulmini-example <name>)"
    , "  bounty_hunter_algebrair_cli --solc-output <out.json> --solc-source <unit> --solc-contract <name> [--solc-field ir|irOptimized] --solc-emit"
    , "  bounty_hunter_algebrair_cli --solc-output <out.json> --solc-source <unit> --solc-contract <name> [--solc-field ir|irOptimized] --solc-coverage [--coverage-strict]"
    , "  bounty_hunter_algebrair_cli --solc-output <out.json> --solc-source <unit> --solc-contract <name> [--solc-field ir|irOptimized] --solc-emit-algebrair2-yul"
    , "  bounty_hunter_algebrair_cli --solc-output <out.json> --solc-source <unit> --solc-contract <name> [--solc-field ir|irOptimized] --solc-check-cei (--slot <n> | --slot-expr <expr> | --slot-auto) [--solc-func <name>] [--emit-evidence] [--emit-replay]"
    , "  bounty_hunter_algebrair_cli --solc-output <out.json> --solc-source <unit> --solc-contract <name> [--solc-field ir|irOptimized] --solc-check-cei-all-auto [--emit-evidence] [--emit-replay]"
    , "  bounty_hunter_algebrair_cli --solc-output <out.json> --solc-source <unit> --solc-contract <name> [--solc-field ir|irOptimized] --solc-scan-inconsistencies"
    , "  bounty_hunter_algebrair_cli --solc-output <out.json> --solc-source <unit> --solc-contract <name> [--solc-field ir|irOptimized] --solc-scan-call-interface"
    , "  bounty_hunter_algebrair_cli --solc-output <out.json> --solc-source <unit> --solc-contract <name> [--solc-field ir|irOptimized] --solc-summarize"
    , "  bounty_hunter_algebrair_cli --solc-output <out.json> --solc-source <unit> --solc-contract <name> [--solc-field ir|irOptimized] --solc-reachability --k 1|2|3"
    , "  bounty_hunter_algebrair_cli --solc-output <out.json> --solc-source <unit> --solc-contract <name> [--solc-field ir|irOptimized] --solc-check-inconsistency-closure --k 1|2|3"
    , "  bounty_hunter_algebrair_cli --solc-output <out.json> --solc-source <unit> --solc-contract <name> [--solc-field ir|irOptimized] --solc-check-temporal --query \"<dsl>\" --k <n>"
    , "  bounty_hunter_algebrair_cli --solc-output <out.json> --solc-source <unit> --solc-contract <name> [--solc-field ir|irOptimized] --solc-mine-invariants --k 1|2|3"
    , "  bounty_hunter_algebrair_cli --solc-output <out.json> --solc-source <unit> --solc-contract <caller> [--solc-field ir|irOptimized] --solc-check-cross-contract-assumptions --solc-callee-contract <callee>"
    , "  bounty_hunter_algebrair_cli --solc-output <out.json> --solc-source <unit> --solc-contract <name> [--solc-field ir|irOptimized] --solc-emit-algebrair [--solc-func <name>]"
    , "  bounty_hunter_algebrair_cli --solc-output <out.json> --solc-source <unit> --solc-contract <name> [--solc-field ir|irOptimized] --solc-scan-risks [--solc-func <name>] [--emit-audit]"
    , "  bounty_hunter_algebrair_cli --solc-output <out.json> --solc-source <unit> --solc-contract <name> [--solc-field ir|irOptimized] --solc-scan-risks-all [--emit-audit]"
    , "  bounty_hunter_algebrair_cli --solc-output <out.json> --solc-source <unit> [--solc-field ir|irOptimized] --solc-scan-risks-all-contracts [--emit-audit]"
    , "  (alternative) replace --solc-output with --solc-compile <file.sol> (requires `solc` on PATH)"
    , "  (alternative) for multi-file projects: use --solc-compile-dir <dir> --solc-source <entry.sol> (loads entry + import-closure under <dir>)"
    , "  (any CEI check) add --emit-replay to attach a deterministic replay trace (vulnerable only)"
    , "  (solc CEI check) add --emit-audit to attach a deterministic translation audit artifact"
    , "  (solc CEI check) add --emit-foundry to attach a Foundry src+test scaffold (requires --solc-compile)"
    , "  (solc) add --emit-foundry-parity to attach a Foundry parity harness (strict semantics gate; requires --solc-compile)"
    , "  (solc) add --write-foundry-parity <dir> to write the parity harness to disk"
    , "  (solc) add --run-forge-parity to run `forge test` for the parity harness (requires --write-foundry-parity)"
    , "  (solc parity) optional: --parity-decompiler solc_ir|algebrair2 (default: solc_ir)"
    , "  (solc) add --solc-decompile-solidity to emit a decompiled Solidity artifact (init-code bootstrap via delegatecall)"
    , "  (solc compile) requests `abi` + `storageLayout` by default (standard-json)"
    , "  (solc CEI check) add --write-foundry <dir> to write the Foundry scaffold to disk"
    , "  (solc CEI check) add --run-forge-test to run `forge test` in that dir (requires --write-foundry)"
    , ""
    , "notes:"
    , "  - exits 0 on SAFE, 2 on VULNERABLE, 3 on OUT_OF_SCOPE, 1 on CLI/IO errors"
    ]

private def findArgVal (args : List String) (k : String) : Option String :=
  let rec go : List String → Option String
    | [] => none
    | a :: b :: rest => if a = k then some b else go (b :: rest)
    | _ :: [] => none
  go args

private def hasFlag (args : List String) (k : String) : Bool :=
  args.any (· = k)

private def jsonInsertObjField (j : Lean.Json) (k : String) (v : Lean.Json) : Lean.Json :=
  match j with
  | .obj kvs => Lean.Json.obj (kvs.insert k v)
  | other => other

private inductive SlotChoice where
  | literal (slot : Nat)
  | dyn (slotExpr : String)

private def resolveSlotChoiceE (args : List String) (g : Graph) : Except String SlotChoice := do
  match findArgVal args "--slot-expr" with
  | some s => return .dyn s
  | none =>
      if hasFlag args "--slot-auto" then
        match HeytingLean.BountyHunter.AlgebraIR.pickAutoSlotExpr? g with
        | some s => return .dyn s
        | none =>
            match HeytingLean.BountyHunter.AlgebraIR.pickAutoSlot? g with
            | some slot => return .literal slot
            | none => pure ()
      let slotOpt :=
        match findArgVal args "--slot" with
        | some s => s.toNat?
        | none => none
      match slotOpt with
      | some slot => return .literal slot
      | none => throw "missing/invalid slot selection: provide --slot <nat>, --slot-expr <expr>, or --slot-auto"

private def solcField (args : List String) : String :=
  match findArgVal args "--solc-field" with
  | some s => s
  | none => "ir"

private def solcFuncName (args : List String) : String :=
  match findArgVal args "--solc-func" with
  | some s => s
  | none => "withdraw"

private def solcSourceUnit (args : List String) (fallback : String) : String :=
  match findArgVal args "--solc-source" with
  | some s => s
  | none => fallback

private def resolveSolcFuncNameE (ir : String) (desired : String) : Except String String := do
  let names ← HeytingLean.BountyHunter.Solc.YulTextMini.listFunctionNamesE ir
  if names.toList.any (· = desired) then
    return desired
  let pickMatchE (pfx : String) : Except String (Option String) := do
    let ms := names.toList.filter (fun n => n.startsWith pfx)
    match ms with
    | [] => return none
    | [m] => return some m
    | _ =>
        let preview := (ms.take 40).intersperse ", " |>.foldl (· ++ ·) ""
        throw s!"ambiguous function selector: {desired} (matches: {preview})"
  let p1 := s!"fun_{desired}_"
  match (← pickMatchE p1) with
  | some n => return n
  | none =>
      let p2 := s!"external_fun_{desired}_"
      match (← pickMatchE p2) with
      | some n => return n
      | none =>
          let preview := (names.toList.take 40).intersperse ", " |>.foldl (· ++ ·) ""
          throw s!"function not found: {desired} (available: {preview})"

private def loadSolcOutputJsonE (args : List String) : IO (Except String (Lean.Json × String × String)) := do
  let c? := findArgVal args "--solc-contract"
  let field := solcField args
  match c? with
  | none => pure (.error "missing --solc-contract")
  | some cName =>
      match findArgVal args "--solc-compile-dir" with
      | some dirPath =>
          match findArgVal args "--solc-source" with
          | none => pure (.error "missing --solc-source (required with --solc-compile-dir)")
          | some srcUnit =>
              let dir : System.FilePath := dirPath
              match (← sourcesJsonFromEntryClosureE dir srcUnit) with
              | .error e => return .error e
              | .ok sourcesJ =>
                  let input : Lean.Json :=
                    Lean.Json.mkObj
                      [ ("language", Lean.Json.str "Solidity")
                      , ("sources", sourcesJ)
                      , ("settings",
                          Lean.Json.mkObj
                            [ ("outputSelection",
                              let outs :=
                                Lean.Json.arr #[Lean.Json.str field, Lean.Json.str "abi", Lean.Json.str "storageLayout"]
                              Lean.Json.mkObj
                                  [ ("*", Lean.Json.mkObj [ ("*", outs) ]) ]) ])
                      ]
                  match (← runSolcStandardJsonE (HeytingLean.Util.JCS.canonicalString input) (some dir)) with
                  | .ok raw =>
                      match Lean.Json.parse raw with
                      | .ok j => pure (.ok (j, srcUnit, cName))
                      | .error e => pure (.error s!"solc JSON parse error: {e}")
                  | .error e =>
                      -- Fallback: retry by sending all `.sol` sources under `--solc-compile-dir`.
                      -- This can recover cases where the entry import scanner misses uncommon patterns.
                      if looksLikeMissingImportError e then
                        match (← sourcesJsonFromDirE dir) with
                        | .error e2 => return .error e2
                        | .ok allSources =>
                            let input2 : Lean.Json :=
                              Lean.Json.mkObj
                                [ ("language", Lean.Json.str "Solidity")
                                , ("sources", allSources)
                                , ("settings",
                                    Lean.Json.mkObj
                                      [ ("outputSelection",
                                        let outs :=
                                          Lean.Json.arr #[Lean.Json.str field, Lean.Json.str "abi", Lean.Json.str "storageLayout"]
                                        Lean.Json.mkObj
                                            [ ("*", Lean.Json.mkObj [ ("*", outs) ]) ]) ])
                                ]
                            let raw2 ←
                              match (← runSolcStandardJsonE (HeytingLean.Util.JCS.canonicalString input2) (some dir)) with
                              | .ok s => pure s
                              | .error e3 => return .error e3
                            match Lean.Json.parse raw2 with
                            | .ok j => pure (.ok (j, srcUnit, cName))
                            | .error e4 => pure (.error s!"solc JSON parse error: {e4}")
                      else
                        return .error e
      | none =>
          match findArgVal args "--solc-compile" with
          | some solPath =>
              let fp : System.FilePath := solPath
              let unitFallback := fp.fileName.getD "Contract.sol"
              let srcUnit := solcSourceUnit args unitFallback
              let content ←
                match (← readFileE fp) with
                | .ok s => pure s
                | .error m => return .error m
              let input : Lean.Json :=
                Lean.Json.mkObj
                  [ ("language", Lean.Json.str "Solidity")
                  , ("sources",
                      Lean.Json.mkObj
                        [ (srcUnit, Lean.Json.mkObj [("content", Lean.Json.str content)]) ])
                  , ("settings",
                      Lean.Json.mkObj
                        [ ("outputSelection",
                          let outs :=
                            -- Default-on: we rely on `abi` today (Foundry harness args) and will rely
                            -- on `storageLayout` for broader dynamic-slot coverage.
                            Lean.Json.arr #[Lean.Json.str field, Lean.Json.str "abi", Lean.Json.str "storageLayout"]
                          Lean.Json.mkObj
                              [ ("*", Lean.Json.mkObj [ ("*", outs) ]) ]) ])
                  ]
              let raw ←
                match (← runSolcStandardJsonE (HeytingLean.Util.JCS.canonicalString input)) with
                | .ok s => pure s
                | .error e => return .error e
              match Lean.Json.parse raw with
              | .ok j => pure (.ok (j, srcUnit, cName))
              | .error e => pure (.error s!"solc JSON parse error: {e}")
          | none =>
              let outPath? := findArgVal args "--solc-output"
              let src? := findArgVal args "--solc-source"
              match outPath?, src? with
              | some outPath, some srcUnit =>
                  let raw ←
                    match (← readFileE outPath) with
                    | .ok s => pure s
                    | .error m => return .error m
                  match Lean.Json.parse raw with
                  | .ok j => pure (.ok (j, srcUnit, cName))
                  | .error e => pure (.error s!"JSON parse error: {e}")
              | _, _ =>
                  pure (.error "missing --solc-output/--solc-source (or use --solc-compile)")

private def loadSolcOutputJsonEAnyContract (args : List String) : IO (Except String (Lean.Json × String)) := do
  let field := solcField args
  match findArgVal args "--solc-compile-dir" with
  | some dirPath =>
      match findArgVal args "--solc-source" with
      | none => pure (.error "missing --solc-source (required with --solc-compile-dir)")
      | some srcUnit =>
          let dir : System.FilePath := dirPath
          match (← sourcesJsonFromEntryClosureE dir srcUnit) with
          | .error e => return .error e
          | .ok sourcesJ =>
              let input : Lean.Json :=
                Lean.Json.mkObj
                  [ ("language", Lean.Json.str "Solidity")
                  , ("sources", sourcesJ)
                  , ("settings",
                      Lean.Json.mkObj
                        [ ("outputSelection",
                          let outs :=
                            Lean.Json.arr #[Lean.Json.str field, Lean.Json.str "abi", Lean.Json.str "storageLayout"]
                          Lean.Json.mkObj
                              [ ("*", Lean.Json.mkObj [ ("*", outs) ]) ]) ])
                  ]
              match (← runSolcStandardJsonE (HeytingLean.Util.JCS.canonicalString input) (some dir)) with
              | .ok raw =>
                  match Lean.Json.parse raw with
                  | .ok j => pure (.ok (j, srcUnit))
                  | .error e => pure (.error s!"solc JSON parse error: {e}")
              | .error e =>
                  if looksLikeMissingImportError e then
                    match (← sourcesJsonFromDirE dir) with
                    | .error e2 => return .error e2
                    | .ok allSources =>
                        let input2 : Lean.Json :=
                          Lean.Json.mkObj
                            [ ("language", Lean.Json.str "Solidity")
                            , ("sources", allSources)
                            , ("settings",
                                Lean.Json.mkObj
                                  [ ("outputSelection",
                                    let outs :=
                                      Lean.Json.arr #[Lean.Json.str field, Lean.Json.str "abi", Lean.Json.str "storageLayout"]
                                    Lean.Json.mkObj
                                        [ ("*", Lean.Json.mkObj [ ("*", outs) ]) ]) ])
                            ]
                        let raw2 ←
                          match (← runSolcStandardJsonE (HeytingLean.Util.JCS.canonicalString input2) (some dir)) with
                          | .ok s => pure s
                          | .error e3 => return .error e3
                        match Lean.Json.parse raw2 with
                        | .ok j => pure (.ok (j, srcUnit))
                        | .error e4 => pure (.error s!"solc JSON parse error: {e4}")
                  else
                    return .error e
  | none =>
      match findArgVal args "--solc-compile" with
      | some solPath =>
          let fp : System.FilePath := solPath
          let unitFallback := fp.fileName.getD "Contract.sol"
          let srcUnit := solcSourceUnit args unitFallback
          let content ←
            match (← readFileE fp) with
            | .ok s => pure s
            | .error m => return .error m
          let input : Lean.Json :=
            Lean.Json.mkObj
              [ ("language", Lean.Json.str "Solidity")
              , ("sources",
                  Lean.Json.mkObj
                    [ (srcUnit, Lean.Json.mkObj [("content", Lean.Json.str content)]) ])
              , ("settings",
                  Lean.Json.mkObj
                    [ ("outputSelection",
                      let outs :=
                        -- Keep consistent with `loadSolcOutputJsonE`.
                        Lean.Json.arr #[Lean.Json.str field, Lean.Json.str "abi", Lean.Json.str "storageLayout"]
                      Lean.Json.mkObj
                          [ ("*", Lean.Json.mkObj [ ("*", outs) ]) ]) ])
              ]
          let raw ←
            match (← runSolcStandardJsonE (HeytingLean.Util.JCS.canonicalString input)) with
            | .ok s => pure s
            | .error e => return .error e
          match Lean.Json.parse raw with
          | .ok j => pure (.ok (j, srcUnit))
          | .error e => pure (.error s!"solc JSON parse error: {e}")
      | none =>
          let outPath? := findArgVal args "--solc-output"
          let src? := findArgVal args "--solc-source"
          match outPath?, src? with
          | some outPath, some srcUnit =>
              let raw ←
                match (← readFileE outPath) with
                | .ok s => pure s
                | .error m => return .error m
              match Lean.Json.parse raw with
              | .ok j => pure (.ok (j, srcUnit))
              | .error e => pure (.error s!"JSON parse error: {e}")
          | _, _ =>
              pure (.error "missing --solc-output/--solc-source (or use --solc-compile)")

private def mergeRisk (a b : HeytingLean.BountyHunter.Solc.YulTextMini.RiskReport) :
    HeytingLean.BountyHunter.Solc.YulTextMini.RiskReport :=
  { a with
    boundaryTargets := a.boundaryTargets ++ b.boundaryTargets
    usesOrigin := a.usesOrigin || b.usesOrigin
    usesTimestamp := a.usesTimestamp || b.usesTimestamp
    usesBlockhash := a.usesBlockhash || b.usesBlockhash
    usesPrevrandao := a.usesPrevrandao || b.usesPrevrandao
    usesSelfdestruct := a.usesSelfdestruct || b.usesSelfdestruct
    usesDelegatecall := a.usesDelegatecall || b.usesDelegatecall
    usesCallcode := a.usesCallcode || b.usesCallcode
    usesCreate := a.usesCreate || b.usesCreate
    usesCreate2 := a.usesCreate2 || b.usesCreate2
    uncheckedCallReturn := a.uncheckedCallReturn || b.uncheckedCallReturn
  }

structure RiskScanStats where
  version : String := "bh.solc_risk_scan_stats.v0"
  contractsTotal : Nat := 0
  contractsWithAnyParsedFn : Nat := 0
  functionsTotal : Nat := 0
  functionsParsed : Nat := 0
  failures : Array (String × String × String) := #[] -- (contract, fn, error)
  deriving Repr, Inhabited

structure CEIAllAutoStats where
  version : String := "bh.solc_cei_all_auto_stats.v0"
  functionsTotal : Nat := 0
  functionsSelected : Nat := 0
  functionsParsed : Nat := 0
  functionsWithAnySlot : Nat := 0
  checksRun : Nat := 0
  vulnerableCount : Nat := 0
  failures : Array (String × String) := #[] -- (fn, error)
  deriving Repr, Inhabited

structure InconsistencyScanStats where
  version : String := "bh.solc_inconsistency_scan_stats.v0"
  functionsTotal : Nat := 0
  functionsSelected : Nat := 0
  functionsParsed : Nat := 0
  functionsWithAnyUpdate : Nat := 0
  findingsCount : Nat := 0
  failures : Array (String × String) := #[] -- (fn, error)
  deriving Repr, Inhabited

private def riskScanStatsToJson (s : RiskScanStats) : Lean.Json :=
  Lean.Json.mkObj
    [ ("version", Lean.Json.str s.version)
    , ("contractsTotal", Lean.Json.num s.contractsTotal)
    , ("contractsWithAnyParsedFn", Lean.Json.num s.contractsWithAnyParsedFn)
    , ("functionsTotal", Lean.Json.num s.functionsTotal)
    , ("functionsParsed", Lean.Json.num s.functionsParsed)
    , ("failures",
        Lean.Json.arr <|
          s.failures.map (fun (p : String × String × String) =>
            Lean.Json.mkObj
              [ ("contract", Lean.Json.str p.1)
              , ("fn", Lean.Json.str p.2.1)
              , ("error", Lean.Json.str p.2.2)
              ]))
    ]

private def ceiAllAutoStatsToJson (s : CEIAllAutoStats) : Lean.Json :=
  Lean.Json.mkObj
    [ ("version", Lean.Json.str s.version)
    , ("functionsTotal", Lean.Json.num s.functionsTotal)
    , ("functionsSelected", Lean.Json.num s.functionsSelected)
    , ("functionsParsed", Lean.Json.num s.functionsParsed)
    , ("functionsWithAnySlot", Lean.Json.num s.functionsWithAnySlot)
    , ("checksRun", Lean.Json.num s.checksRun)
    , ("vulnerableCount", Lean.Json.num s.vulnerableCount)
    , ("failures",
        Lean.Json.arr <|
          s.failures.map (fun (p : String × String) =>
            Lean.Json.mkObj
              [ ("fn", Lean.Json.str p.1)
              , ("error", Lean.Json.str p.2)
              ]))
    ]

private def inconsistencyScanStatsToJson (s : InconsistencyScanStats) : Lean.Json :=
  Lean.Json.mkObj
    [ ("version", Lean.Json.str s.version)
    , ("functionsTotal", Lean.Json.num s.functionsTotal)
    , ("functionsSelected", Lean.Json.num s.functionsSelected)
    , ("functionsParsed", Lean.Json.num s.functionsParsed)
    , ("functionsWithAnyUpdate", Lean.Json.num s.functionsWithAnyUpdate)
    , ("findingsCount", Lean.Json.num s.findingsCount)
    , ("failures",
        Lean.Json.arr <|
          s.failures.map (fun (p : String × String) =>
            Lean.Json.mkObj
              [ ("fn", Lean.Json.str p.1)
              , ("error", Lean.Json.str p.2)
              ]))
    ]

private def isInterestingSolcFnName (n : String) : Bool :=
  n.startsWith "fun_" || n.startsWith "external_fun_" || n.startsWith "getter_fun_" ||
    n = "fallback" || n = "receive"

private def collectSlotChoices (g : Graph) : Array SlotChoice :=
  Id.run do
    let mut litsRaw : Array Nat := #[]
    let mut dynsRaw : Array String := #[]
    for n in g.nodes do
      for e in n.effects do
        match e with
        | .storageWrite slot => litsRaw := litsRaw.push slot
        | .storageWriteDyn se =>
            if HeytingLean.BountyHunter.AlgebraIR.slotRefParse? se |>.isSome then
              dynsRaw := dynsRaw.push se
        | _ => pure ()
    let litsSorted :=
      Id.run do
        let ys := litsRaw.qsort (fun a b => a < b)
        let mut out : Array Nat := #[]
        for x in ys do
          match out.back? with
          | none => out := out.push x
          | some y =>
              if x = y then
                continue
              else
                out := out.push x
        return out
    let dynsSorted :=
      Id.run do
        let ys := dynsRaw.qsort (fun a b => a < b)
        let mut out : Array String := #[]
        for x in ys do
          match out.back? with
          | none => out := out.push x
          | some y =>
              if x = y then
                continue
              else
                out := out.push x
        return out
    let mut out : Array SlotChoice := #[]
    for se in dynsSorted do
      out := out.push (.dyn se)
    for slot in litsSorted do
      out := out.push (.literal slot)
    -- Avoid runaway work on very large functions: check a bounded number of candidate slots deterministically.
    return out.take 6

private def scanRisksAllFunctionsE (ir : String) :
    Except String (HeytingLean.BountyHunter.Solc.YulTextMini.RiskReport × RiskScanStats) := do
  let fns ← HeytingLean.BountyHunter.Solc.YulTextMini.listFunctionNamesE ir
  let mut stats : RiskScanStats := { contractsTotal := 1, functionsTotal := fns.size }
  let mut anyParsed := false
  let mut r : HeytingLean.BountyHunter.Solc.YulTextMini.RiskReport := {}
  for fn in fns do
    match HeytingLean.BountyHunter.Solc.YulTextMini.parseFunctionBodyE ir fn with
    | .ok body =>
        anyParsed := true
        stats := { stats with functionsParsed := stats.functionsParsed + 1 }
        let r2 :=
          HeytingLean.BountyHunter.Solc.YulTextMini.normalize
            (HeytingLean.BountyHunter.Solc.YulTextMini.scanStmts body)
        r := mergeRisk r r2
    | .error e =>
        stats := { stats with failures := stats.failures.push ("<contract>", fn, e) }
  if anyParsed then
    stats := { stats with contractsWithAnyParsedFn := 1 }
  return (HeytingLean.BountyHunter.Solc.YulTextMini.normalize r, stats)

private def parseExample (name : String) : Except String Graph :=
  match name with
  | "etherstore_vuln" => .ok (etherStoreVuln 0)
  | "etherstore_fixed" => .ok (etherStoreFixed 0)
  | _ => .error s!"unknown example '{name}'"

private def parseYulMiniExample (name : String) : Except String HeytingLean.BountyHunter.YulMini.Program :=
  match name with
  | "etherstore_vuln" => .ok HeytingLean.BountyHunter.YulMini.etherStoreVuln
  | "etherstore_fixed" => .ok HeytingLean.BountyHunter.YulMini.etherStoreFixed
  | _ => .error s!"unknown yulmini example '{name}'"

private def findFuncName (args : List String) : String :=
  match findArgVal args "--func" with
  | some s => s
  | none => "withdraw"

private def outputJson (j : Lean.Json) : IO Unit :=
  IO.println (HeytingLean.Util.JCS.canonicalString j)

private def maybeAttachEvidence (args : List String) (g : Graph) (slot : Nat)
    (v : Verdict) (w? : Option CEIWitness) (base : Lean.Json) : Lean.Json :=
  if !hasFlag args "--emit-evidence" then
    base
  else
    let slotExpr? : Option String :=
      match findArgVal args "--slot-expr" with
      | some s => some s
      | none =>
          if hasFlag args "--slot-auto" then
            HeytingLean.BountyHunter.AlgebraIR.pickAutoSlotExpr? g
          else
            none
    let e0 :=
      HeytingLean.BountyHunter.AlgebraIR.Evidence.merge
        (HeytingLean.BountyHunter.AlgebraIR.Evidence.deltaOfGraph g)
        (HeytingLean.BountyHunter.AlgebraIR.Evidence.deltaOfCEIResult slot slotExpr? v w?)
    let e1 := HeytingLean.BountyHunter.AlgebraIR.Evidence.close e0
    match base with
    | .obj kvs =>
        Lean.Json.obj (kvs.insert "evidence" (HeytingLean.BountyHunter.AlgebraIR.Evidence.evidenceToJson e1))
    | other => other

private def maybeAttachReplay (args : List String) (g : Graph) (_slot : Nat)
    (v : Verdict) (w? : Option CEIWitness) (base : Lean.Json) : Lean.Json :=
  if !hasFlag args "--emit-replay" then
    base
  else
    match v, w? with
    | Verdict.vulnerable, some w =>
        match HeytingLean.BountyHunter.AlgebraIR.Replay.traceFromCEIWitnessE g w with
        | .error err =>
            match base with
            | .obj kvs => Lean.Json.obj (kvs.insert "replayError" (Lean.Json.str err))
            | other => other
        | .ok t =>
            match base with
            | .obj kvs =>
                Lean.Json.obj
                  (kvs.insert "replay" (HeytingLean.BountyHunter.AlgebraIR.Replay.traceToJson t))
            | other => other
    | _, _ => base

private def jsonObjGet? (j : Lean.Json) (k : String) : Option Lean.Json :=
  match j with
  | .obj kvs => kvs.get? k
  | _ => none

private def jsonArr? (j : Lean.Json) : Option (Array Lean.Json) :=
  match j with
  | .arr xs => some xs
  | _ => none

private def jsonStr? (j : Lean.Json) : Option String :=
  match j with
  | .str s => some s
  | _ => none

private def defaultCallArgOfAbiType? (ty : String) : Option String :=
  if ty.startsWith "uint" then
    some "uint256(1)"
  else if ty.startsWith "int" then
    some "int256(1)"
  else if ty = "address" then
    -- Calls are made from the attacker contract in the generated harness.
    some "address(this)"
  else if ty = "bool" then
    some "true"
  else if ty = "bytes32" then
    some "bytes32(uint256(0))"
  else if ty = "bytes" then
    some "hex\"\""
  else if ty = "string" then
    some "\"\""
  else
    none

private def ctorInputsFromSolcAbiE (solcJson : Lean.Json) (srcUnit : String) (contractName : String) :
    Except String (Array Lean.Json) := do
  let getE {α : Type} (o : Option α) (err : String) : Except String α :=
    match o with
    | some x => .ok x
    | none => .error err
  let contractsJ ← getE (jsonObjGet? solcJson "contracts") "solc JSON missing 'contracts'"
  let srcJ ← getE (jsonObjGet? contractsJ srcUnit) s!"solc JSON missing contracts[{srcUnit}]"
  let cJ ← getE (jsonObjGet? srcJ contractName) s!"solc JSON missing contracts[{srcUnit}][{contractName}]"
  let abiJ ← getE (jsonObjGet? cJ "abi") s!"solc JSON missing abi for {contractName} (include 'abi' in outputSelection)"
  let abiArr ← getE (jsonArr? abiJ) s!"solc abi is not an array for {contractName}"
  let cands : Array Lean.Json :=
    abiArr.foldl
      (fun acc item =>
        match item with
        | .obj kvs =>
            match kvs.get? "type" with
            | some (.str "constructor") => acc.push item
            | _ => acc
        | _ => acc)
      #[]
  if cands.isEmpty then
    return #[]
  if cands.size > 1 then
    throw "abi: multiple constructors entries (unexpected)"
  let ctorJ := cands[0]!
  let inputsJ ← getE (jsonObjGet? ctorJ "inputs") s!"abi: missing inputs for constructor"
  let inputs ← getE (jsonArr? inputsJ) s!"abi: inputs is not an array for constructor"
  for inp in inputs do
    HeytingLean.BountyHunter.Foundry.Parity.validateAbiParamE inp
  return inputs

private def callArgsFromSolcAbiE (solcJson : Lean.Json) (srcUnit : String) (contractName : String) (funcName : String) :
    Except String (Array String) := do
  let getE {α : Type} (o : Option α) (err : String) : Except String α :=
    match o with
    | some x => .ok x
    | none => .error err

  let contractsJ ← getE (jsonObjGet? solcJson "contracts") "solc JSON missing 'contracts'"
  let srcJ ← getE (jsonObjGet? contractsJ srcUnit) s!"solc JSON missing contracts[{srcUnit}]"
  let cJ ← getE (jsonObjGet? srcJ contractName) s!"solc JSON missing contracts[{srcUnit}][{contractName}]"
  let abiJ ← getE (jsonObjGet? cJ "abi") s!"solc JSON missing abi for {contractName} (include 'abi' in outputSelection)"
  let abiArr ← getE (jsonArr? abiJ) s!"solc abi is not an array for {contractName}"

  let cands : Array Lean.Json :=
    abiArr.foldl
      (fun acc item =>
        match item with
        | .obj kvs =>
            match kvs.get? "type", kvs.get? "name" with
            | some (.str "function"), some (.str nm) =>
                if nm = funcName then acc.push item else acc
            | _, _ => acc
        | _ => acc)
      #[]

  if cands.isEmpty then
    throw s!"abi: function not found: {funcName}"
  if cands.size > 1 then
    throw s!"abi: overloaded function not supported: {funcName} ({cands.size} overloads)"
  let fnJ := cands[0]!
  let inputsJ ← getE (jsonObjGet? fnJ "inputs") s!"abi: missing inputs for {funcName}"
  let inputs ← getE (jsonArr? inputsJ) s!"abi: inputs is not an array for {funcName}"
  inputs.foldlM
    (init := #[])
    (fun acc inp => do
      let tyJ ← getE (jsonObjGet? inp "type") s!"abi: input missing type for {funcName}"
      let ty ← getE (jsonStr? tyJ) s!"abi: input type is not a string for {funcName}"
      match defaultCallArgOfAbiType? ty with
      | some a => pure (acc.push a)
      | none => throw s!"abi: unsupported arg type '{ty}' for {funcName}")

private structure AbiFnInfo where
  kind : String := "function"
  signature : String
  inputs : Array Lean.Json := #[]

private def abiFnsFromSolcAbiE (solcJson : Lean.Json) (srcUnit : String) (contractName : String) :
    Except String (Array AbiFnInfo) := do
  let getE {α : Type} (o : Option α) (err : String) : Except String α :=
    match o with
    | some x => .ok x
    | none => .error err

  let contractsJ ← getE (jsonObjGet? solcJson "contracts") "solc JSON missing 'contracts'"
  let srcJ ← getE (jsonObjGet? contractsJ srcUnit) s!"solc JSON missing contracts[{srcUnit}]"
  let cJ ← getE (jsonObjGet? srcJ contractName) s!"solc JSON missing contracts[{srcUnit}][{contractName}]"
  let abiJ ← getE (jsonObjGet? cJ "abi") s!"solc JSON missing abi for {contractName} (include 'abi' in outputSelection)"
  let abiArr ← getE (jsonArr? abiJ) s!"solc abi is not an array for {contractName}"

  let mut out : Array AbiFnInfo := #[]
  for item in abiArr do
    match item with
    | .obj kvs =>
        match kvs.get? "type" with
        | some (.str "function") =>
            let nmJ ← getE (kvs.get? "name") "abi: function item missing name"
            let nm ← getE (jsonStr? nmJ) "abi: function name is not a string"
            let inputsJ ← getE (kvs.get? "inputs") s!"abi: missing inputs for {nm}"
            let inputs ← getE (jsonArr? inputsJ) s!"abi: inputs is not an array for {nm}"
            let mut tys : Array String := #[]
            let mut inps : Array Lean.Json := #[]
            for inp in inputs do
              match inp with
              | .obj kvs2 =>
                  let tyJ ← getE (kvs2.get? "type") s!"abi: input missing type for {nm}"
                  let _ty ← getE (jsonStr? tyJ) s!"abi: input type is not a string for {nm}"
                  HeytingLean.BountyHunter.Foundry.Parity.validateAbiParamE inp
                  let t ← HeytingLean.BountyHunter.Foundry.Parity.abiTyFromAbiParamJsonE inp
                  tys := tys.push (HeytingLean.BountyHunter.Foundry.Parity.canonicalTypeString t)
                  inps := inps.push inp
              | _ => throw s!"abi: malformed input item for {nm}"
            let sig := nm ++ "(" ++ String.intercalate "," tys.toList ++ ")"
            out := out.push { kind := "function", signature := sig, inputs := inps }
        | some (.str "fallback") =>
            out := out.push { kind := "fallback", signature := "", inputs := #[] }
        | some (.str "receive") =>
            out := out.push { kind := "receive", signature := "", inputs := #[] }
        | _ => pure ()
    | _ => pure ()
  return out

private def staticSlotsFromStorageLayoutE (solcJson : Lean.Json) (srcUnit : String) (contractName : String) :
    Except String (Array Nat) := do
  let getE {α : Type} (o : Option α) (err : String) : Except String α :=
    match o with
    | some x => .ok x
    | none => .error err
  let contractsJ ← getE (jsonObjGet? solcJson "contracts") "solc JSON missing 'contracts'"
  let srcJ ← getE (jsonObjGet? contractsJ srcUnit) s!"solc JSON missing contracts[{srcUnit}]"
  let cJ ← getE (jsonObjGet? srcJ contractName) s!"solc JSON missing contracts[{srcUnit}][{contractName}]"
  let slJ? := jsonObjGet? cJ "storageLayout"
  match slJ? with
  | none => return #[]
  | some slJ =>
      let storageJ ← getE (jsonObjGet? slJ "storage") "storageLayout: missing 'storage'"
      let arr ← getE (jsonArr? storageJ) "storageLayout.storage is not an array"
      let mut slots : Array Nat := #[]
      for it in arr do
        match it with
        | .obj kvs =>
            match kvs.get? "slot" with
            | some (.str s) =>
                match s.toNat? with
                | some n => slots := slots.push n
                | none => pure ()
            | _ => pure ()
        | _ => pure ()
      -- sort/dedup
      let ys := slots.qsort (· < ·)
      let mut out : Array Nat := #[]
      for x in ys do
        match out.back? with
        | none => out := out.push x
        | some y => if x = y then pure () else out := out.push x
      return out

private def mappingBaseSlotsFromStorageLayoutE (solcJson : Lean.Json) (srcUnit : String) (contractName : String) :
    Except String (Array Nat) := do
  let getE {α : Type} (o : Option α) (err : String) : Except String α :=
    match o with
    | some x => .ok x
    | none => .error err
  let contractsJ ← getE (jsonObjGet? solcJson "contracts") "solc JSON missing 'contracts'"
  let srcJ ← getE (jsonObjGet? contractsJ srcUnit) s!"solc JSON missing contracts[{srcUnit}]"
  let cJ ← getE (jsonObjGet? srcJ contractName) s!"solc JSON missing contracts[{srcUnit}][{contractName}]"
  let slJ? := jsonObjGet? cJ "storageLayout"
  match slJ? with
  | none => return #[]
  | some slJ =>
      let storageJ ← getE (jsonObjGet? slJ "storage") "storageLayout: missing 'storage'"
      let typesJ ← getE (jsonObjGet? slJ "types") "storageLayout: missing 'types'"
      let storageArr ← getE (jsonArr? storageJ) "storageLayout.storage is not an array"
      let typesObj ←
        match typesJ with
        | .obj kvs => pure kvs
        | _ => throw "storageLayout.types is not an object"
      let mut slots : Array Nat := #[]
      for it in storageArr do
        match it with
        | .obj kvs =>
            match kvs.get? "slot", kvs.get? "type" with
            | some (.str slotS), some (.str tyId) =>
                match typesObj.get? tyId with
                | some (.obj tyKvs) =>
                    match tyKvs.get? "encoding" with
                    | some (.str "mapping") =>
                        match slotS.toNat? with
                        | some n => slots := slots.push n
                        | none => pure ()
                    | _ => pure ()
                | _ => pure ()
            | _, _ => pure ()
        | _ => pure ()
      let ys := slots.qsort (· < ·)
      let mut out : Array Nat := #[]
      for x in ys do
        match out.back? with
        | none => out := out.push x
        | some y => if x = y then pure () else out := out.push x
      return out

private structure YulBytecodes where
  creation : String
  runtime : String

private def compileYulBytecodesE (ir : String) : IO (Except String YulBytecodes) := do
  let input : Lean.Json :=
    Lean.Json.mkObj
      [ ("language", Lean.Json.str "Yul")
      , ("sources",
          Lean.Json.mkObj
            [ ("BountyHunterDecompiled.yul", Lean.Json.mkObj [("content", Lean.Json.str ir)]) ])
      , ("settings",
          Lean.Json.mkObj
            [ ("outputSelection",
                Lean.Json.mkObj
                  [ ("*", Lean.Json.mkObj
                      [ ("*", Lean.Json.arr #[Lean.Json.str "evm.bytecode.object", Lean.Json.str "evm.deployedBytecode.object"]) ]) ]) ])
      ]
  let raw ← runSolcStandardJsonE (HeytingLean.Util.JCS.canonicalString input)
  match raw with
  | .error e => pure (.error e)
  | .ok s =>
      match Lean.Json.parse s with
      | .error err => pure (.error s!"solc(yul) JSON parse error: {err}")
      | .ok j =>
          let getObjValE (j : Lean.Json) (k : String) (ctx : String) : Except String Lean.Json := do
            match j with
            | .obj kvs =>
                match kvs.get? k with
                | some v => pure v
                | none => throw s!"{ctx}: missing key '{k}'"
            | _ => throw s!"{ctx}: expected object"
          let getStrE (j : Lean.Json) (ctx : String) : Except String String := do
            match j with
            | .str s => pure s
            | _ => throw s!"{ctx}: expected string"
          let checkSolcErrorsE (j : Lean.Json) : Except String Unit := do
            match j with
            | .obj kvs =>
                match kvs.get? "errors" with
                | none => pure ()
                | some (.arr es) =>
                    let errs :=
                      es.toList.filterMap (fun e =>
                        match e with
                        | .obj kvs =>
                            match kvs.get? "severity", kvs.get? "formattedMessage" with
                            | some (.str sev), some (.str msg) =>
                                if sev = "error" then some msg else none
                            | _, _ => none
                        | _ => none)
                    if errs.isEmpty then
                      pure ()
                    else
                      let preview := (errs.take 10).intersperse "\n" |>.foldl (· ++ ·) ""
                      throw s!"solc(yul) reported errors:\n{preview}"
                | some _ => pure ()
            | _ => pure ()
          pure <| (do
            checkSolcErrorsE j
            let contractsJ ← getObjValE j "contracts" "solc(yul)"
            let fileJ ← getObjValE contractsJ "BountyHunterDecompiled.yul" "solc(yul).contracts"
            let cJ :=
              match fileJ with
              | .obj kvs =>
                  match kvs.toList with
                  | [] => none
                  | (_, v) :: _ => some v
              | _ => none
            match cJ with
            | none => throw "solc(yul): expected one contract under contracts[BountyHunterDecompiled.yul]"
            | some cJ =>
                let evmJ ← getObjValE cJ "evm" "solc(yul).contract"
                let bcJ ← getObjValE evmJ "bytecode" "solc(yul).evm"
                let objJ ← getObjValE bcJ "object" "solc(yul).evm.bytecode"
                let creation ← getStrE objJ "solc(yul).evm.bytecode.object"
                let dbcJ ← getObjValE evmJ "deployedBytecode" "solc(yul).evm"
                let dobjJ ← getObjValE dbcJ "object" "solc(yul).evm.deployedBytecode"
                let runtime ← getStrE dobjJ "solc(yul).evm.deployedBytecode.object"
                pure { creation := creation, runtime := runtime })

private def compileYulCreationBytecodeE (ir : String) : IO (Except String String) := do
  match (← compileYulBytecodesE ir) with
  | .ok b => pure (.ok b.creation)
  | .error e => pure (.error e)

private def compileYulRuntimeBytecodeE (ir : String) : IO (Except String String) := do
  match (← compileYulBytecodesE ir) with
  | .ok b => pure (.ok b.runtime)
  | .error e => pure (.error e)

private def compileAlgebraIR2CreationBytecodeE (spec : HeytingLean.BountyHunter.AlgebraIR2.ReplaySpec) :
    IO (Except String String) := do
  match HeytingLean.BountyHunter.AlgebraIR2.yulObjectForCEIReplayE spec with
  | .error e => pure (.error e)
  | .ok yul => compileYulCreationBytecodeE yul

private def maybeAttachFoundry (args : List String) (solcJson : Lean.Json) (srcUnit : String) (ir : String)
    (g : Graph) (slot : Nat) (contractName : String) (funcName : String)
    (v : Verdict) (_w? : Option CEIWitness) (base : Lean.Json) : IO Lean.Json := do
  let wantEmit := hasFlag args "--emit-foundry"
  let writeDir? := findArgVal args "--write-foundry"
  let runForge := hasFlag args "--run-forge-test"
  if !wantEmit && writeDir?.isNone && !runForge then
    return base

  if runForge && writeDir?.isNone then
    match base with
    | .obj kvs =>
        return Lean.Json.obj (kvs.insert "foundryError" (Lean.Json.str "missing --write-foundry <dir> for --run-forge-test"))
    | other => return other

  let hasDynSlots : Bool :=
    g.nodes.any (fun n => n.effects.any (fun e => match e with | .storageReadDyn _ => true | .storageWriteDyn _ => true | _ => false))
  let slotExpr? : Option String :=
    match findArgVal args "--slot-expr" with
    | some s => some s
    | none =>
        if hasFlag args "--slot-auto" then
          HeytingLean.BountyHunter.AlgebraIR.pickAutoSlotExpr? g
        else
          none
  let rec slotRefOkForFoundry : HeytingLean.BountyHunter.AlgebraIR.SlotRef → Bool
    | .literal _ => true
    | .mapping b k =>
        slotRefOkForFoundry b &&
        match k with
        | .caller => true
        | .this => true
        | .nat _ => true
        | _ => false
    | .keccak b => slotRefOkForFoundry b
    | .add b off =>
        slotRefOkForFoundry b &&
        match off with
        | .nat _ => true
        | _ => false
    | .packed b _ _ => slotRefOkForFoundry b
    | .raw _ => false
  let slotExprOkForFoundry : Option String → Bool
    | none => true
    | some s =>
        match HeytingLean.BountyHunter.AlgebraIR.slotRefParse? s with
        | none => false
        | some r => slotRefOkForFoundry r
  if hasDynSlots && slotExpr?.isNone then
    match base with
    | .obj kvs =>
        return Lean.Json.obj (kvs.insert "foundryError" (Lean.Json.str "dynamic storage slots present; provide --slot-expr <expr> or --slot-auto"))
    | other => return other
  if !slotExprOkForFoundry slotExpr? then
    match base with
    | .obj kvs =>
        let se := slotExpr?.getD ""
        return Lean.Json.obj (kvs.insert "foundryError" (Lean.Json.str s!"slotExpr unsupported for Foundry vm.store: {se}"))
    | other => return other
  let solPath? := findArgVal args "--solc-compile"
  match solPath? with
  | none =>
      match base with
      | .obj kvs =>
          return Lean.Json.obj (kvs.insert "foundryError" (Lean.Json.str "missing --solc-compile (required for Foundry output/write)"))
      | other => return other
  | some p =>
      let src ←
        match (← readFileE p) with
        | .ok s => pure s
        | .error e =>
            match base with
            | .obj kvs => return Lean.Json.obj (kvs.insert "foundryError" (Lean.Json.str e))
            | other => return other
      let callArgs ←
        match callArgsFromSolcAbiE solcJson srcUnit contractName funcName with
        | .ok a => pure a
        | .error err =>
            match base with
            | .obj kvs =>
                return Lean.Json.obj (kvs.insert "foundryError" (Lean.Json.str s!"failed to derive call args from ABI: {err}"))
            | other => return other
      let expectVuln? : Option Bool :=
        match v with
        | Verdict.vulnerable => some true
        | Verdict.safe => some false
        | Verdict.outOfScope _ => none
      let decompiledCreationBytecode? : Option String ←
        if runForge then
          match (← compileYulCreationBytecodeE ir) with
          | .ok hex => pure (some hex)
          | .error e =>
              match base with
              | .obj kvs =>
                  return Lean.Json.obj (kvs.insert "foundryError" (Lean.Json.str s!"failed to compile IR as Yul for decompiler check: {e}"))
              | other => return other
        else
          pure none

      let algebraIR2CreationBytecode? : Option String ←
        if runForge then
          match v with
          | Verdict.safe | Verdict.vulnerable =>
              let order :=
                match v with
                | Verdict.safe => HeytingLean.BountyHunter.AlgebraIR2.CEIOrder.writeThenCall
                | Verdict.vulnerable => HeytingLean.BountyHunter.AlgebraIR2.CEIOrder.callThenWrite
                | _ => HeytingLean.BountyHunter.AlgebraIR2.CEIOrder.writeThenCall
              let spec : HeytingLean.BountyHunter.AlgebraIR2.ReplaySpec :=
                { order := order, slot := slot, slotExpr? := slotExpr?, writeValue := 0 }
              match (← compileAlgebraIR2CreationBytecodeE spec) with
              | .ok hex => pure (some hex)
              | .error e =>
                  match base with
                  | .obj kvs =>
                      return Lean.Json.obj (kvs.insert "foundryError" (Lean.Json.str s!"failed to compile AlgebraIR2 decompiler Yul: {e}"))
                  | other => return other
          | _ => pure none
        else
          pure none
      let files :=
        HeytingLean.BountyHunter.Foundry.gen src contractName funcName slot slotExpr? callArgs expectVuln?
          decompiledCreationBytecode? algebraIR2CreationBytecode?
      let base :=
        if wantEmit then
          match base with
          | .obj kvs => Lean.Json.obj (kvs.insert "foundry" (HeytingLean.BountyHunter.Foundry.filesToJson files))
          | other => other
        else
          base

      let resolveForgeCmd : IO String := do
        match (← IO.getEnv "FORGE") with
        | some cmd => pure cmd
        | none =>
            match (← IO.getEnv "HOME") with
            | none => pure "forge"
            | some h =>
                let p : System.FilePath := s!"{h}/.foundry/bin/forge"
                if (← p.pathExists) then pure p.toString else pure "forge"

      let forgeCmd? : Option String ←
        if runForge then
          pure (some (← resolveForgeCmd))
        else
          pure none

      let (base, outDir?) ←
        match writeDir? with
        | none => pure (base, none)
        | some dirS =>
            let outDir : System.FilePath := dirS
            let srcPath := outDir / System.FilePath.mk files.srcPath
            let testPath := outDir / System.FilePath.mk files.testPath
            let tomlPath := outDir / "foundry.toml"
            let toml :=
              String.intercalate "\n"
                [ "[profile.default]"
                , "src = \"src\""
                , "test = \"test\""
                , "out = \"out\""
                , "libs = [\"lib\"]"
                , "via_ir = true"
                , "optimizer = true"
                , "optimizer_runs = 200"
                , "fs_permissions = [{ access = \"read-write\", path = \"./\" }]"
                , ""
                ]
            try
              IO.FS.createDirAll outDir
              IO.FS.createDirAll (srcPath.parent.getD outDir)
              IO.FS.createDirAll (testPath.parent.getD outDir)
              IO.FS.writeFile srcPath files.src
              IO.FS.writeFile testPath files.test
              if !(← tomlPath.pathExists) then
                IO.FS.writeFile tomlPath toml
              let writeJ :=
                Lean.Json.mkObj
                  [ ("dir", Lean.Json.str outDir.toString)
                  , ("src", Lean.Json.str srcPath.toString)
                  , ("test", Lean.Json.str testPath.toString)
                  , ("toml", Lean.Json.str tomlPath.toString)
                  ]
              match base with
              | .obj kvs => pure (Lean.Json.obj (kvs.insert "foundryWritten" writeJ), some outDir)
              | other => pure (other, some outDir)
            catch e =>
              match base with
              | .obj kvs => pure (Lean.Json.obj (kvs.insert "foundryError" (Lean.Json.str s!"failed to write foundry files: {e}")), some outDir)
              | other => pure (other, some outDir)

      if !runForge then
        return base

      let hasAnyError : Lean.Json → Bool
        | .obj kvs => kvs.contains "foundryError" || kvs.contains "forgeError"
        | _ => false
      if hasAnyError base then
        return base

      let outDir := outDir?.get!
      let forgeCmd := forgeCmd?.get!

      try
        let testOut ← IO.Process.output { cmd := forgeCmd, args := #["test", "-vv"], cwd := some outDir }
        let j0 :=
          Lean.Json.mkObj
            [ ("cmd", Lean.Json.str forgeCmd)
            , ("args", Lean.Json.arr #[Lean.Json.str "test", Lean.Json.str "-vv"])
            , ("exitCode", Lean.Json.num testOut.exitCode.toNat)
            , ("ok", Lean.Json.bool (testOut.exitCode = 0))
            ]
        let jBase ←
          if testOut.exitCode = 0 then
            pure j0
          else
            let stdoutPreview := testOut.stdout.take 4000
            let stderrPreview := testOut.stderr.take 4000
            let stdoutSha ← HeytingLean.Util.sha256HexOfStringIO testOut.stdout
            let stderrSha ← HeytingLean.Util.sha256HexOfStringIO testOut.stderr
            match j0 with
            | .obj kvs =>
                pure <| Lean.Json.obj <| kvs
                  |>.insert "stdoutPreview" (Lean.Json.str stdoutPreview)
                  |>.insert "stderrPreview" (Lean.Json.str stderrPreview)
                  |>.insert "stdoutSha256" (Lean.Json.str stdoutSha)
                  |>.insert "stderrSha256" (Lean.Json.str stderrSha)
            | other => pure other
        let oraclePath := outDir / "bh_oracle.json"
        let j ←
          if (← oraclePath.pathExists) then
            match (← readFileE oraclePath) with
            | .error e =>
                match jBase with
                | .obj kvs => pure (Lean.Json.obj (kvs.insert "oracleError" (Lean.Json.str e)))
                | other => pure other
            | .ok s =>
                match Lean.Json.parse s with
                | .error err =>
                    match jBase with
                    | .obj kvs => pure (Lean.Json.obj (kvs.insert "oracleError" (Lean.Json.str s!"oracle JSON parse error: {err}")))
                    | other => pure other
                | .ok oj =>
                    match jBase with
                    | .obj kvs => pure (Lean.Json.obj (kvs.insert "oracle" oj))
                    | other => pure other
          else
            pure jBase
        match base with
        | .obj kvs => return Lean.Json.obj (kvs.insert "forgeTest" j)
        | other => return other
      catch e =>
        match base with
        | .obj kvs => return Lean.Json.obj (kvs.insert "forgeError" (Lean.Json.str s!"failed to run forge test: {e}"))
        | other => return other

private def decompiledSolidityFromCreationHex (creationHex : String) : String :=
  String.intercalate "\n"
    [ "// SPDX-License-Identifier: UNLICENSED"
    , "pragma solidity ^0.8.20;"
    , ""
    , "/// BountyHunter decompiler artifact (strict mode):"
    , "/// this contract bootstraps from embedded init code (creation bytecode) via delegatecall, so constructor-side"
    , "/// storage initialization is reproduced before returning the final runtime."
    , "contract __BHInitCodeHolder {"
    , "  constructor(bytes memory code) {"
    , "    assembly { return(add(code, 0x20), mload(code)) }"
    , "  }"
    , "}"
    , "contract BountyHunterDecompiled {"
    , "  constructor(bytes memory __ctorData) {"
    , s!"    bytes memory __init = bytes.concat(hex\"{creationHex}\", __ctorData);"
    , "    __BHInitCodeHolder h = new __BHInitCodeHolder(__init);"
    , "    (bool ok, bytes memory runtime) = address(h).delegatecall(\"\");"
    , "    require(ok, \"init delegatecall failed\");"
    , "    assembly { return(add(runtime, 0x20), mload(runtime)) }"
    , "  }"
    , "}"
    ]

private def maybeAttachSolcDecompileSolidity (args : List String) (srcUnit : String) (cName : String) (ir : String)
    (base : Lean.Json) : IO (Lean.Json × Bool) := do
  if !hasFlag args "--solc-decompile-solidity" then
    return (base, false)
  match (← compileYulCreationBytecodeE ir) with
  | .error e =>
      let out :=
        match base with
        | .obj kvs => Lean.Json.obj (kvs.insert "decompileError" (Lean.Json.str e))
        | other => other
      return (out, true)
  | .ok creationHex =>
      let sol := decompiledSolidityFromCreationHex creationHex
      let out :=
        match base with
        | .obj kvs =>
            Lean.Json.obj <| kvs
              |>.insert "version" (Lean.Json.str "bh.solc_decompile_solidity.v0")
              |>.insert "sourceUnit" (Lean.Json.str srcUnit)
              |>.insert "contractName" (Lean.Json.str cName)
              |>.insert "decompiledContractName" (Lean.Json.str "BountyHunterDecompiled")
              |>.insert "decompiledCreationHex" (Lean.Json.str creationHex)
              |>.insert "decompiledSolidity" (Lean.Json.str sol)
        | other => other
      return (out, true)

private def maybeAttachFoundryParity (args : List String) (solcJson : Lean.Json) (srcUnit : String) (ir : String)
    (contractName : String) (base : Lean.Json) : IO Lean.Json := do
  let wantEmit := hasFlag args "--emit-foundry-parity"
  let writeDir? := findArgVal args "--write-foundry-parity"
  let runForge := hasFlag args "--run-forge-parity"
  if !wantEmit && writeDir?.isNone && !runForge then
    return base
  if runForge && writeDir?.isNone then
    match base with
    | .obj kvs =>
        return Lean.Json.obj (kvs.insert "foundryParityError" (Lean.Json.str "missing --write-foundry-parity <dir> for --run-forge-parity"))
    | other => return other

  let abiFns : Array HeytingLean.BountyHunter.Foundry.Parity.AbiFn ←
    match abiFnsFromSolcAbiE solcJson srcUnit contractName with
    | .ok xs =>
        pure <| xs.map (fun x => ({ kind := x.kind, signature := x.signature, inputs := x.inputs } : HeytingLean.BountyHunter.Foundry.Parity.AbiFn))
    | .error e =>
        match base with
        | .obj kvs => return Lean.Json.obj (kvs.insert "foundryParityError" (Lean.Json.str e))
        | other => return other

  let staticSlots :=
    match staticSlotsFromStorageLayoutE solcJson srcUnit contractName with
    | .ok xs => xs
    | .error _ => #[]
  let mappingBases :=
    match mappingBaseSlotsFromStorageLayoutE solcJson srcUnit contractName with
    | .ok xs => xs
    | .error _ => #[]

  let parityDecompiler := (findArgVal args "--parity-decompiler").getD "solc_ir"
  let (creationHex, codegenStats?) ←
    match parityDecompiler with
    | "solc_ir" =>
        match (← compileYulCreationBytecodeE ir) with
        | .ok h => pure (h, none)
        | .error e =>
            match base with
            | .obj kvs =>
                return Lean.Json.obj (kvs.insert "foundryParityError" (Lean.Json.str s!"failed to compile IR as Yul (creation) for decompiler: {e}"))
            | other => return other
    | "algebrair2" =>
        match HeytingLean.BountyHunter.AlgebraIR2.canonicalizeYulObjectE ir with
        | .error e =>
            match base with
            | .obj kvs =>
                return Lean.Json.obj (kvs.insert "foundryParityError" (Lean.Json.str s!"algebrair2 codegen failed: {e}"))
            | other => return other
        | .ok (ir2, stats) =>
            if !stats.failures.isEmpty then
              let preview :=
                (stats.failures.toList.take 25).map (fun (p : String × String) => s!"{p.1}: {p.2}")
                |>.intersperse " | " |>.foldl (· ++ ·) ""
              match base with
              | .obj kvs =>
                  return Lean.Json.obj <| kvs
                    |>.insert "parityDecompiler" (Lean.Json.str parityDecompiler)
                    |>.insert "algebraIR2Codegen" (HeytingLean.BountyHunter.AlgebraIR2.codegenStatsToJson stats)
                    |>.insert "foundryParityError" (Lean.Json.str s!"algebrair2 codegen parse coverage failure (code blocks {stats.codeBlocksParsed}/{stats.codeBlocksTotal}, functions {stats.functionsParsed}/{stats.functionsTotal}): {preview}")
              | other => return other
            match (← compileYulCreationBytecodeE ir2) with
            | .ok h => pure (h, some (HeytingLean.BountyHunter.AlgebraIR2.codegenStatsToJson stats))
            | .error e =>
                match base with
                | .obj kvs =>
                    return Lean.Json.obj (kvs.insert "foundryParityError" (Lean.Json.str s!"failed to compile algebrair2-regenerated IR as Yul (creation): {e}"))
                | other => return other
    | other =>
        match base with
        | .obj kvs =>
            return Lean.Json.obj (kvs.insert "foundryParityError" (Lean.Json.str s!"unknown --parity-decompiler '{other}' (expected solc_ir|algebrair2)"))
        | otherJ => return otherJ

  let solPath? := findArgVal args "--solc-compile"
  match solPath? with
  | none =>
      match base with
      | .obj kvs =>
          return Lean.Json.obj (kvs.insert "foundryParityError" (Lean.Json.str "missing --solc-compile (required for parity Foundry output/write)"))
      | other => return other
  | some p =>
      let src ←
        match (← readFileE p) with
        | .ok s => pure s
        | .error e =>
            match base with
            | .obj kvs => return Lean.Json.obj (kvs.insert "foundryParityError" (Lean.Json.str e))
            | other => return other
      let ctorInputs ←
        match ctorInputsFromSolcAbiE solcJson srcUnit contractName with
        | .ok xs => pure xs
        | .error e =>
            match base with
            | .obj kvs => return Lean.Json.obj (kvs.insert "foundryParityError" (Lean.Json.str e))
            | other => return other
      let files := HeytingLean.BountyHunter.Foundry.Parity.gen src contractName abiFns staticSlots creationHex ctorInputs mappingBases
      let base :=
        if wantEmit then
          match base with
          | .obj kvs => Lean.Json.obj (kvs.insert "foundryParity" (HeytingLean.BountyHunter.Foundry.Parity.filesToJson files))
          | other => other
        else
          base
      let base :=
        match base with
        | .obj kvs =>
            let kvs := kvs.insert "parityDecompiler" (Lean.Json.str parityDecompiler)
            let kvs :=
              match codegenStats? with
              | none => kvs
              | some j => kvs.insert "algebraIR2Codegen" j
            Lean.Json.obj kvs
        | other => other

      let resolveForgeCmd : IO String := do
        match (← IO.getEnv "FORGE") with
        | some cmd => pure cmd
        | none =>
            match (← IO.getEnv "HOME") with
            | none => pure "forge"
            | some h =>
                let p : System.FilePath := s!"{h}/.foundry/bin/forge"
                if (← p.pathExists) then pure p.toString else pure "forge"

      let (base, outDir?) ←
        match writeDir? with
        | none => pure (base, none)
        | some dirS =>
            let outDir : System.FilePath := dirS
            let srcPath := outDir / System.FilePath.mk files.srcPath
            let testPath := outDir / System.FilePath.mk files.testPath
            let tomlPath := outDir / "foundry.toml"
            let toml :=
              String.intercalate "\n"
                [ "[profile.default]"
                , "src = \"src\""
                , "test = \"test\""
                , "out = \"out\""
                , "libs = [\"lib\"]"
                , "via_ir = true"
                , "optimizer = true"
                , "optimizer_runs = 200"
                , "fs_permissions = [{ access = \"read-write\", path = \"./\" }]"
                , ""
                ]
            try
              IO.FS.createDirAll outDir
              IO.FS.createDirAll (srcPath.parent.getD outDir)
              IO.FS.createDirAll (testPath.parent.getD outDir)
              IO.FS.writeFile srcPath files.src
              IO.FS.writeFile testPath files.test
              if !(← tomlPath.pathExists) then
                IO.FS.writeFile tomlPath toml
              let writeJ :=
                Lean.Json.mkObj
                  [ ("dir", Lean.Json.str outDir.toString)
                  , ("src", Lean.Json.str srcPath.toString)
                  , ("test", Lean.Json.str testPath.toString)
                  , ("toml", Lean.Json.str tomlPath.toString)
                  ]
              match base with
              | .obj kvs => pure (Lean.Json.obj (kvs.insert "foundryParityWritten" writeJ), some outDir)
              | other => pure (other, some outDir)
            catch e =>
              match base with
              | .obj kvs => pure (Lean.Json.obj (kvs.insert "foundryParityError" (Lean.Json.str s!"failed to write foundry parity files: {e}")), some outDir)
              | other => pure (other, some outDir)

      if !runForge then
        return base

      match outDir? with
      | none =>
          match base with
          | .obj kvs => return Lean.Json.obj (kvs.insert "forgeParityError" (Lean.Json.str "internal: missing outDir for parity forge run"))
          | other => return other
      | some outDir =>
          let forgeCmd := (← resolveForgeCmd)
          let testOut ←
            try
              IO.Process.output { cmd := forgeCmd, args := #["test", "-q"], cwd := some outDir }
            catch e =>
              match base with
              | .obj kvs => return Lean.Json.obj (kvs.insert "forgeParityError" (Lean.Json.str s!"failed to run forge: {e}"))
              | other => return other
          let j0 :=
            Lean.Json.mkObj
              [ ("cmd", Lean.Json.str forgeCmd)
              , ("args", Lean.Json.arr #[Lean.Json.str "test", Lean.Json.str "-q"])
              , ("exitCode", Lean.Json.num testOut.exitCode.toNat)
              , ("ok", Lean.Json.bool (testOut.exitCode = 0))
              ]
          let oraclePath := outDir / files.oraclePath
          let j1 ←
            if (← oraclePath.pathExists) then
              match (← readFileE oraclePath) with
              | .ok s =>
                  match Lean.Json.parse s with
                  | .ok oj =>
                      match j0 with
                      | .obj kvs => pure (Lean.Json.obj (kvs.insert "oracle" oj))
                      | other => pure other
                  | .error err =>
                      match j0 with
                      | .obj kvs => pure (Lean.Json.obj (kvs.insert "oracleError" (Lean.Json.str s!"oracle JSON parse error: {err}")))
                      | other => pure other
              | .error e =>
                  match j0 with
                  | .obj kvs => pure (Lean.Json.obj (kvs.insert "oracleError" (Lean.Json.str e)))
                  | other => pure other
            else
              pure j0
          match base with
          | .obj kvs => return Lean.Json.obj (kvs.insert "forgeParityTest" j1)
          | other => return other

private def maybeAttachSolcAudit (args : List String) (sel : HeytingLean.BountyHunter.Solc.Selector) (ir : String)
    (desiredFunc selectedFunc : String) (slot : Nat) (base : Lean.Json) : IO Lean.Json := do
  if !hasFlag args "--emit-audit" then
    return base
  let slotExpr? : Option String :=
    match findArgVal args "--slot-expr" with
    | some s => some s
    | none =>
        if hasFlag args "--slot-auto" then
          match HeytingLean.BountyHunter.Solc.YulTextMini.parseFunctionBodyE ir selectedFunc with
          | .ok body =>
              let g := HeytingLean.BountyHunter.Solc.YulTextMini.toAlgebraIR body
              HeytingLean.BountyHunter.AlgebraIR.pickAutoSlotExpr? g
          | .error _ => none
        else
          none
  match HeytingLean.BountyHunter.Solc.Audit.mkFromIR sel ir desiredFunc selectedFunc slot slotExpr? with
  | .error e =>
      match base with
      | .obj kvs => return Lean.Json.obj (kvs.insert "auditError" (Lean.Json.str e))
      | other => return other
  | .ok a =>
      match base with
      | .obj kvs =>
          return Lean.Json.obj (kvs.insert "audit" (HeytingLean.BountyHunter.Solc.Audit.artifactToJson a))
      | other => return other

private def mkFuzzGraph (seed : Nat) : Graph :=
  let nNodes := (seed % 25) + 1
  let baseId := seed * 1000
  let ids : Array NodeId := (Array.range nNodes).map (fun i => baseId + i)
  let mkEffect (i : Nat) : Array Effect :=
    let slot := (seed + i) % 5
    let tag := (seed + i) % 7
    match tag with
    | 0 => #[Effect.storageRead slot]
    | 1 => #[Effect.storageWrite slot]
    | 2 => #[Effect.boundaryCall s!"t{(seed + i) % 3}"]
    | 3 => #[Effect.storageWrite slot, Effect.boundaryCall s!"t{(seed + i) % 3}"]
    | _ => #[]
  let mkSuccs (i : Nat) : Array NodeId :=
    let a := ids[(i + 1) % nNodes]!
    let b := ids[(i + 1 + (seed % 7)) % nNodes]!
    if (seed + i) % 4 = 0 then #[a, b] else #[a]
  let nodes : Array Node :=
    ids.mapIdx (fun i id =>
      { id := id
        op := { tag := s!"op_{seed}_{i}" }
        args := if i = 0 then #[] else #[ids[(i - 1) % nNodes]!]
        effects := mkEffect i
        succs := mkSuccs i })
  { entry := ids[0]!, exits := #[ids[nNodes - 1]!] , nodes := nodes }

/-! ## Solc/YulTextMini: small interprocedural inlining for CEI

For CEI/reentrancy-style checks we want storage writes performed by internal helper calls
(notably ReentrancyGuard enter/exit) to be visible in the caller's CFG nodes. This is
an intentionally bounded, conservative approximation:

- We summarize internal function bodies into a small set of *relevant* effects.
- When building the CFG for a function body, we append those summarized effects to
  direct internal calls at the expression level.
- We also drop `boundaryCall staticcall` for CEI purposes (static calls are not
  reentrancy interactions).
-/

private def isCEIInlineRelevantEffect (e : Effect) : Bool :=
  match e with
  | .storageWrite _ => true
  | .storageWriteDyn _ => true
  | .boundaryCall _ => true
  | _ => false

private def hasStorageWrite (effs : Array Effect) : Bool :=
  effs.any (fun e =>
    match e with
    | .storageWrite _ => true
    | .storageWriteDyn _ => true
    | _ => false)

private def isInterestingInlineFnName (fn : String) : Bool :=
  fn.startsWith "fun_" || fn.startsWith "modifier_"

private def isInlineRelevantBoundaryTarget (t : String) : Bool :=
  t = "call" || t = "delegatecall" || t = "callcode"

private def dedupInlineEffects (effs : Array Effect) : Array Effect :=
  Id.run do
    let mut seenSlots : Std.HashSet Nat := Std.HashSet.emptyWithCapacity 16
    let mut seenDyn : Std.HashSet String := Std.HashSet.emptyWithCapacity 16
    let mut seenBC : Std.HashSet String := Std.HashSet.emptyWithCapacity 8
    let mut out : Array Effect := #[]
    for e in effs do
      match e with
      | .storageWrite s =>
          if !seenSlots.contains s then
            seenSlots := seenSlots.insert s
            out := out.push e
      | .storageWriteDyn se =>
          if !seenDyn.contains se then
            seenDyn := seenDyn.insert se
            out := out.push e
      | .boundaryCall t =>
          if isInlineRelevantBoundaryTarget t && !seenBC.contains t then
            seenBC := seenBC.insert t
            out := out.push e
      | _ => continue
    return out

private partial def collectCalleesFromExpr (e : HeytingLean.BountyHunter.Solc.YulTextMini.Expr) (acc : Array String) : Array String :=
  match e with
  | .call fn args =>
      let acc := args.foldl (fun a x => collectCalleesFromExpr x a) acc
      if isInterestingInlineFnName fn then
        acc.push fn
      else
        acc
  | _ => acc

private partial def collectCalleesFromStmt (s : HeytingLean.BountyHunter.Solc.YulTextMini.Stmt) (acc : Array String) : Array String :=
  match s with
  | .let_ _ rhs => collectCalleesFromExpr rhs acc
  | .letMany _ rhs => collectCalleesFromExpr rhs acc
  | .assign _ rhs => collectCalleesFromExpr rhs acc
  | .assignMany _ _ => acc
  | .expr e => collectCalleesFromExpr e acc
  | .block ss => ss.foldl (fun a st => collectCalleesFromStmt st a) acc
  | .if_ cond thenStmts =>
      let acc := collectCalleesFromExpr cond acc
      thenStmts.foldl (fun a st => collectCalleesFromStmt st a) acc
  | .switch_ scrut cases def? =>
      let acc := collectCalleesFromExpr scrut acc
      let acc := cases.foldl (fun a c => c.2.foldl (fun a2 st => collectCalleesFromStmt st a2) a) acc
      def?.map (fun ds => ds.foldl (fun a2 st => collectCalleesFromStmt st a2) acc) |>.getD acc
  | .for_ init cond post body =>
      let acc := init.foldl (fun a st => collectCalleesFromStmt st a) acc
      let acc := collectCalleesFromExpr cond acc
      let acc := post.foldl (fun a st => collectCalleesFromStmt st a) acc
      body.foldl (fun a st => collectCalleesFromStmt st a) acc
  | _ => acc

private def collectCalleesFromBody (body : Array HeytingLean.BountyHunter.Solc.YulTextMini.Stmt) : Array String :=
  let xs := body.foldl (fun a st => collectCalleesFromStmt st a) #[]
  -- deterministic dedup
  Id.run do
    let ys := xs.qsort (fun a b => a < b)
    let mut out : Array String := #[]
    for x in ys do
      match out.back? with
      | none => out := out.push x
      | some y => if x = y then continue else out := out.push x
    return out

private structure CEIInlineContext where
  inlineMap : Std.HashMap String (Array Effect)
  calledByAny : Std.HashSet String
  deriving Inhabited

private def buildCEIInlineContext (ir : String) (fnsAll : Array String) : CEIInlineContext :=
  Id.run do
    let mut base : Std.HashMap String (Array Effect) := Std.HashMap.emptyWithCapacity (fnsAll.size + 1)
    let mut callees : Std.HashMap String (Array String) := Std.HashMap.emptyWithCapacity (fnsAll.size + 1)
    let mut calledByAny : Std.HashSet String := Std.HashSet.emptyWithCapacity (fnsAll.size + 1)

    for fn in fnsAll do
      if !isInterestingInlineFnName fn then
        continue
      match HeytingLean.BountyHunter.Solc.YulTextMini.parseFunctionBodyE ir fn with
      | .error _ => continue
      | .ok body =>
          let effs0 := HeytingLean.BountyHunter.Solc.YulTextMini.expectedEffectsFromStmts HeytingLean.BountyHunter.Solc.YulTextMini.envEmpty body
          -- Keep only storage writes + non-static boundary call kinds.
          let effs1 := dedupInlineEffects (effs0.filter isCEIInlineRelevantEffect)
          base := base.insert fn effs1
          let cs := collectCalleesFromBody body
          callees := callees.insert fn cs
          for c in cs do
            calledByAny := calledByAny.insert c

    -- Small transitive closure to propagate guard/boundary effects up wrapper chains.
    let mut cur := base
    for _iter in [:3] do
      let mut next := cur
      for (fn, effs0) in cur.toList do
        let cs := callees.getD fn #[]
        let mut combined := effs0
        for c in cs do
          combined := combined ++ (cur.getD c #[])
        next := next.insert fn (dedupInlineEffects combined)
      cur := next

    return { inlineMap := cur, calledByAny := calledByAny }

private def dropStaticcallBoundaryEffects (g : Graph) : Graph :=
  let nodes :=
    g.nodes.map (fun n =>
      let effs :=
        n.effects.filter (fun e =>
          match e with
          | .boundaryCall t => t ≠ "staticcall"
          | _ => true)
      { n with effects := effs })
  { g with nodes := nodes }

private def containsSubstr (hay needle : String) : Bool :=
  if needle.isEmpty then
    true
  else
    Id.run do
      let max := hay.length - needle.length
      let mut found := false
      for i in [:max.succ] do
        if (!found) && (hay.drop i).startsWith needle then
          found := true
      return found

private partial def stmtHasSubstr (needle : String) : HeytingLean.BountyHunter.Solc.YulTextMini.Stmt → Bool
  | .let_ _ rhs => containsSubstr (HeytingLean.BountyHunter.Solc.YulTextMini.exprRender rhs) needle
  | .letMany _ rhs => containsSubstr (HeytingLean.BountyHunter.Solc.YulTextMini.exprRender rhs) needle
  | .assign _ rhs => containsSubstr (HeytingLean.BountyHunter.Solc.YulTextMini.exprRender rhs) needle
  | .assignMany _ _rhs => false
  | .expr e => containsSubstr (HeytingLean.BountyHunter.Solc.YulTextMini.exprRender e) needle
  | .block ss => ss.any (stmtHasSubstr needle)
  | .if_ cond thenStmts =>
      containsSubstr (HeytingLean.BountyHunter.Solc.YulTextMini.exprRender cond) needle ||
        thenStmts.any (stmtHasSubstr needle)
  | .switch_ scrut cases def? =>
      containsSubstr (HeytingLean.BountyHunter.Solc.YulTextMini.exprRender scrut) needle ||
        cases.any (fun c => c.2.any (stmtHasSubstr needle)) ||
        (def?.map (fun ds => ds.any (stmtHasSubstr needle)) |>.getD false)
  | .for_ init cond post body =>
      init.any (stmtHasSubstr needle) ||
        containsSubstr (HeytingLean.BountyHunter.Solc.YulTextMini.exprRender cond) needle ||
        post.any (stmtHasSubstr needle) ||
        body.any (stmtHasSubstr needle)
  | _ => false

private def bodyLooksLikeEntrypoint (calledByAny : Std.HashSet String) (fn : String)
    (body : Array HeytingLean.BountyHunter.Solc.YulTextMini.Stmt) : Bool :=
  fn = "fallback" || fn = "receive" || fn.startsWith "external_fun_" ||
    body.any (stmtHasSubstr "calldataload") ||
    body.any (stmtHasSubstr "calldatasize") ||
    body.any (stmtHasSubstr "calldatacopy") ||
    (!calledByAny.contains fn)

private def selftestJsonRoundtrip : Except String Unit := do
  if !graphRoundtripPrintParseOk (etherStoreVuln 0) then
    throw "roundtrip failed: etherStoreVuln"
  if !graphRoundtripPrintParseOk (etherStoreFixed 0) then
    throw "roundtrip failed: etherStoreFixed"

  let minimal := "{\"entry\":0,\"nodes\":[{\"id\":0,\"op\":{\"tag\":\"x\"}}]}"
  let (canon, ok) ← graphRoundtripParsePrintParseE minimal
  if !ok then
    throw s!"roundtrip failed: minimal parse-print-parse mismatch (canon={canon})"

  let rec loop (i : Nat) : Except String Unit := do
    if h : i < 500 then
      let g := mkFuzzGraph i
      if !graphRoundtripPrintParseOk g then
        throw s!"roundtrip failed: fuzz seed {i}"
      loop (i + 1)
    else
      pure ()
  loop 0

  -- Phase 1 sanity: YulMini → AlgebraIR translation preserves the CEI classification.
  let yv := HeytingLean.BountyHunter.YulMini.etherStoreVuln
  let yf := HeytingLean.BountyHunter.YulMini.etherStoreFixed
  let gv ←
    match HeytingLean.BountyHunter.YulMini.translateProgram yv "withdraw" with
    | .ok g => pure g
    | .error e => throw s!"yulmini translate failed (vuln): {e}"
  let gf ←
    match HeytingLean.BountyHunter.YulMini.translateProgram yf "withdraw" with
    | .ok g => pure g
    | .error e => throw s!"yulmini translate failed (fixed): {e}"
  let (vv, _) := checkCEI gv 0
  let (vf, _) := checkCEI gf 0
  if vv ≠ Verdict.vulnerable then
    throw s!"yulmini CEI mismatch: expected VULNERABLE, got {reprStr vv}"
  if vf ≠ Verdict.safe then
    throw s!"yulmini CEI mismatch: expected SAFE, got {reprStr vf}"

  -- YulMini JSON roundtrip checks (examples + deterministic fuzz corpus).
  if !HeytingLean.BountyHunter.YulMini.programRoundtripPrintParseOk yv then
    throw "yulmini roundtrip failed: etherStoreVuln"
  if !HeytingLean.BountyHunter.YulMini.programRoundtripPrintParseOk yf then
    throw "yulmini roundtrip failed: etherStoreFixed"
  let mkFuzzProg (seed : Nat) : HeytingLean.BountyHunter.YulMini.Program :=
    let stmt (i : Nat) : HeytingLean.BountyHunter.YulMini.Stmt :=
      match (seed + i) % 7 with
      | 0 =>
          .expr (.builtin (.sload ((seed + i) % 5)) #[])
      | 1 =>
          .expr (.builtin (.sstore ((seed + i) % 5)) #[.nat 0])
      | 2 =>
          .expr (.builtin (.call s!"t{(seed + i) % 3}") #[.var "bal"])
      | 3 =>
          .if_ (.var "c") #[.revert] #[]
      | 4 =>
          .if_ (.var "c") #[] #[.revert]
      | 5 =>
          .let_ "x" (.nat (seed + i))
      | _ =>
          .expr (.var "x")
    let n := (seed % 25) + 1
    { funcs := #[{ name := "withdraw", body := (Array.range n).map stmt }] }
  let rec loopY (i : Nat) : Except String Unit := do
    if h : i < 200 then
      if !HeytingLean.BountyHunter.YulMini.programRoundtripPrintParseOk (mkFuzzProg i) then
        throw s!"yulmini roundtrip failed: fuzz seed {i}"
      loopY (i + 1)
    else
      pure ()
  loopY 0

  -- Evidence spine checks (determinism + JSON I/O + idempotence).
  let mkEvidence (g : Graph) (slot : Nat) : HeytingLean.BountyHunter.AlgebraIR.Evidence.Evidence :=
    let (v, w?) := checkCEI g slot
    let e0 :=
      HeytingLean.BountyHunter.AlgebraIR.Evidence.merge
        (HeytingLean.BountyHunter.AlgebraIR.Evidence.deltaOfGraph g)
        (HeytingLean.BountyHunter.AlgebraIR.Evidence.deltaOfCEIResult slot none v w?)
    HeytingLean.BountyHunter.AlgebraIR.Evidence.close e0
  let eV := mkEvidence (etherStoreVuln 0) 0
  let eF := mkEvidence (etherStoreFixed 0) 0
  if !HeytingLean.BountyHunter.AlgebraIR.Evidence.evidenceRoundtripPrintParseOk eV then
    throw "evidence roundtrip failed: etherStoreVuln"
  if !HeytingLean.BountyHunter.AlgebraIR.Evidence.evidenceRoundtripPrintParseOk eF then
    throw "evidence roundtrip failed: etherStoreFixed"
  if HeytingLean.BountyHunter.AlgebraIR.Evidence.close eV ≠ eV then
    throw "evidence idempotence failed: close(close(E)) != close(E) (vuln)"
  if HeytingLean.BountyHunter.AlgebraIR.Evidence.close eF ≠ eF then
    throw "evidence idempotence failed: close(close(E)) != close(E) (fixed)"
  let (dv1, _) := HeytingLean.BountyHunter.AlgebraIR.Evidence.deriveCEIFromClosedEvidence eV 0
  let (dv2, _) :=
    HeytingLean.BountyHunter.AlgebraIR.Evidence.deriveCEIFromClosedEvidence
      (HeytingLean.BountyHunter.AlgebraIR.Evidence.close (HeytingLean.BountyHunter.AlgebraIR.Evidence.merge eV { notes := #["extra"] }))
      0
  if dv1 ≠ dv2 then
    throw s!"evidence monotonicity sanity failed (vuln changed): {reprStr dv1} -> {reprStr dv2}"

  -- Phase 2a: replay trace artifact for a CEI witness.
  let (rv, rw?) := checkCEI (etherStoreVuln 0) 0
  match rv, rw? with
  | Verdict.vulnerable, some w =>
      let (t1, ok1) ←
        match HeytingLean.BountyHunter.AlgebraIR.Replay.replayCEIWitnessE (etherStoreVuln 0) w with
        | .ok r => pure r
        | .error e => throw s!"replayCEIWitnessE failed: {e}"
      let (t2, ok2) ←
        match HeytingLean.BountyHunter.AlgebraIR.Replay.replayCEIWitnessE (etherStoreVuln 0) w with
        | .ok r => pure r
        | .error e => throw s!"replayCEIWitnessE failed: {e}"
      if !ok1 || !ok2 then
        throw "replay trace did not validate as a witness"
      let c1 := HeytingLean.BountyHunter.AlgebraIR.Replay.traceCanonicalString t1
      let c2 := HeytingLean.BountyHunter.AlgebraIR.Replay.traceCanonicalString t2
      if c1 ≠ c2 then
        throw "replay trace canonicalization not deterministic"
  | _, _ =>
      throw "expected CEI witness for etherStoreVuln"

  -- Phase 2b: Foundry scaffold generation is deterministic.
  let f := HeytingLean.BountyHunter.Foundry.gen "pragma solidity ^0.8.20; contract C { function withdraw() external {} }" "C" "withdraw" 0
  let fc1 := HeytingLean.BountyHunter.Foundry.filesCanonicalString f
  let fc2 := HeytingLean.BountyHunter.Foundry.filesCanonicalString f
  if fc1 ≠ fc2 then
    throw "foundry scaffold canonicalization not deterministic"

  -- Phase 1b: Yul-text mini parser → AlgebraIR sanity (CEI classification).
  let yulTextVuln :=
    "function withdraw() {\n" ++
    "  let bal := sload(0)\n" ++
    "  if gt(bal, 0) {\n" ++
    "    let ok := call(0, 0, 0, 0, 0, 0, 0)\n" ++
    "    sstore(0, 0)\n" ++
    "  }\n" ++
    "}\n"
  let yulTextFixed :=
    "function withdraw() {\n" ++
    "  let bal := sload(0)\n" ++
    "  if gt(bal, 0) {\n" ++
    "    sstore(0, 0)\n" ++
    "    let ok := call(0, 0, 0, 0, 0, 0, 0)\n" ++
    "  }\n" ++
    "}\n"
  let bodyV ←
    match HeytingLean.BountyHunter.Solc.YulTextMini.parseFunctionBodyE yulTextVuln "withdraw" with
    | .ok b => pure b
    | .error e => throw s!"yultextmini parse failed (vuln): {e}"
  let bodyF ←
    match HeytingLean.BountyHunter.Solc.YulTextMini.parseFunctionBodyE yulTextFixed "withdraw" with
    | .ok b => pure b
    | .error e => throw s!"yultextmini parse failed (fixed): {e}"
  let gV := HeytingLean.BountyHunter.Solc.YulTextMini.toAlgebraIR bodyV
  let gF := HeytingLean.BountyHunter.Solc.YulTextMini.toAlgebraIR bodyF
  let (vv2, _) := checkCEI gV 0
  let (vf2, _) := checkCEI gF 0
  if vv2 ≠ Verdict.vulnerable then
    throw s!"yultextmini CEI mismatch: expected VULNERABLE, got {reprStr vv2}"
  if vf2 ≠ Verdict.safe then
    throw s!"yultextmini CEI mismatch: expected SAFE, got {reprStr vf2}"

  -- Phase 1b extension: ensure common solc IR constructs (switch/for) parse + translate.
  let yulTextSwitch :=
    "function withdraw() {\n" ++
    "  let bal := sload(0)\n" ++
    "  switch bal\n" ++
    "  case 0 { leave }\n" ++
    "  default {\n" ++
    "    let ok := call(0, 0, 0, 0, 0, 0, 0)\n" ++
    "    sstore(0, 0)\n" ++
    "  }\n" ++
    "}\n"
  let bodyS ←
    match HeytingLean.BountyHunter.Solc.YulTextMini.parseFunctionBodyE yulTextSwitch "withdraw" with
    | .ok b => pure b
    | .error e => throw s!"yultextmini parse failed (switch): {e}"
  let gS := HeytingLean.BountyHunter.Solc.YulTextMini.toAlgebraIR bodyS
  let (vs, _) := checkCEI gS 0
  if vs ≠ Verdict.vulnerable then
    throw s!"yultextmini switch CEI mismatch: expected VULNERABLE, got {reprStr vs}"

  let yulTextFor :=
    "function withdraw() {\n" ++
    "  for { let i := 0 } lt(i, 1) { i := add(i, 1) } {\n" ++
    "    let ok := call(0, 0, 0, 0, 0, 0, 0)\n" ++
    "    sstore(0, 0)\n" ++
    "  }\n" ++
    "}\n"
  let bodyL ←
    match HeytingLean.BountyHunter.Solc.YulTextMini.parseFunctionBodyE yulTextFor "withdraw" with
    | .ok b => pure b
    | .error e => throw s!"yultextmini parse failed (for): {e}"
  let gL := HeytingLean.BountyHunter.Solc.YulTextMini.toAlgebraIR bodyL
  let (vl, _) := checkCEI gL 0
  if vl ≠ Verdict.vulnerable then
    throw s!"yultextmini for-loop CEI mismatch: expected VULNERABLE, got {reprStr vl}"

  -- Phase 1b extension: solc-style storage helper calls should be recognized as storageRead/write effects.
  let yulTextHelperV :=
    "function withdraw() {\n" ++
    "  let bal := load_from_storage_offset_0_t_uint256()\n" ++
    "  if gt(bal, 0) {\n" ++
    "    let ok := call(0, 0, 0, 0, 0, 0, 0)\n" ++
    "    update_storage_value_offset_0_t_uint256_to_t_uint256(0)\n" ++
    "  }\n" ++
    "}\n"
  let bodyHV ←
    match HeytingLean.BountyHunter.Solc.YulTextMini.parseFunctionBodyE yulTextHelperV "withdraw" with
    | .ok b => pure b
    | .error e => throw s!"yultextmini parse failed (helper vuln): {e}"
  let gHV := HeytingLean.BountyHunter.Solc.YulTextMini.toAlgebraIR bodyHV
  let (vhv, _) := checkCEI gHV 0
  if vhv ≠ Verdict.vulnerable then
    throw s!"yultextmini helper-call CEI mismatch: expected VULNERABLE, got {reprStr vhv}"

  let yulTextHelperF :=
    "function withdraw() {\n" ++
    "  let bal := load_from_storage_offset_0_t_uint256()\n" ++
    "  if gt(bal, 0) {\n" ++
    "    update_storage_value_offset_0_t_uint256_to_t_uint256(0)\n" ++
    "    let ok := call(0, 0, 0, 0, 0, 0, 0)\n" ++
    "  }\n" ++
    "}\n"
  let bodyHF ←
    match HeytingLean.BountyHunter.Solc.YulTextMini.parseFunctionBodyE yulTextHelperF "withdraw" with
    | .ok b => pure b
    | .error e => throw s!"yultextmini parse failed (helper safe): {e}"
  let gHF := HeytingLean.BountyHunter.Solc.YulTextMini.toAlgebraIR bodyHF
  let (vhf, _) := checkCEI gHF 0
  if vhf ≠ Verdict.safe then
    throw s!"yultextmini helper-call CEI mismatch: expected SAFE, got {reprStr vhf}"

  -- Phase 1b extension: dynamic slot helpers should be reported as storageRead/Write *Dyn*.
  let yulTextDyn :=
    "function withdraw() {\n" ++
    "  let s := mapping_index_access_t_mapping$_t_address_$_t_uint256_$_of_t_address(0, caller())\n" ++
    "  let bal := read_from_storage_offset_0_t_uint256(s)\n" ++
    "  if gt(bal, 0) {\n" ++
    "    let ok := call(0, 0, 0, 0, 0, 0, 0)\n" ++
    "    update_storage_value_offset_0_t_uint256_to_t_uint256(s, 0)\n" ++
    "  }\n" ++
    "}\n"
  let bodyD ←
    match HeytingLean.BountyHunter.Solc.YulTextMini.parseFunctionBodyE yulTextDyn "withdraw" with
    | .ok b => pure b
    | .error e => throw s!"yultextmini parse failed (dyn slot): {e}"
  let gD := HeytingLean.BountyHunter.Solc.YulTextMini.toAlgebraIR bodyD
  if !gD.nodes.any (fun n => n.effects.any (fun e => match e with | .storageReadDyn _ => true | _ => false)) then
    throw "yultextmini expected storageReadDyn, but none found"
  if !gD.nodes.any (fun n => n.effects.any (fun e => match e with | .storageWriteDyn _ => true | _ => false)) then
    throw "yultextmini expected storageWriteDyn, but none found"
  let (vd, _) := checkCEI gD 0
  if vd ≠ Verdict.vulnerable then
    throw s!"yultextmini dyn-slot CEI mismatch: expected VULNERABLE, got {reprStr vd}"

  -- Phase 1b: extraction from solc standard-json output (minimal fixture).
  let jOut : Lean.Json :=
    Lean.Json.mkObj
      [ ("contracts",
          Lean.Json.mkObj
            [ ("X.sol",
                Lean.Json.mkObj
                  [ ("C",
                      Lean.Json.mkObj
                        [ ("ir", Lean.Json.str yulTextVuln) ]) ]) ]) ]
  let sel : HeytingLean.BountyHunter.Solc.Selector :=
    { sourceUnit := "X.sol", contractName := "C", field := "ir" }
  let extracted ←
    match HeytingLean.BountyHunter.Solc.extractFieldE jOut sel with
    | .ok s => pure s
    | .error e => throw s!"solc extractFieldE failed on minimal fixture: {e}"
  if extracted.isEmpty then
    throw "solc extractFieldE returned empty string on minimal fixture"

  -- Phase 1b: pinned solc IR fixture (for audit + translation sanity).
  let extracted2 ←
    match HeytingLean.BountyHunter.Solc.extractFieldE
        HeytingLean.BountyHunter.Solc.Fixtures.solcOutJson
        HeytingLean.BountyHunter.Solc.Fixtures.selector with
    | .ok s => pure s
    | .error e => throw s!"solc extractFieldE failed on pinned fixture: {e}"
  if extracted2 ≠ HeytingLean.BountyHunter.Solc.Fixtures.ir then
    throw "pinned solc fixture: extracted ir mismatch"
  let func ←
    match resolveSolcFuncNameE HeytingLean.BountyHunter.Solc.Fixtures.ir HeytingLean.BountyHunter.Solc.Fixtures.desiredFunc with
    | .ok f => pure f
    | .error e => throw s!"pinned solc fixture: func resolve failed: {e}"
  let bodyFix ←
    match HeytingLean.BountyHunter.Solc.YulTextMini.parseFunctionBodyE HeytingLean.BountyHunter.Solc.Fixtures.ir func with
    | .ok b => pure b
    | .error e => throw s!"pinned solc fixture: parseFunctionBodyE failed: {e}"
  let gFix := HeytingLean.BountyHunter.Solc.YulTextMini.toAlgebraIR bodyFix
  let (vFix, _) := checkCEI gFix HeytingLean.BountyHunter.Solc.Fixtures.slot
  if vFix ≠ Verdict.vulnerable then
    throw s!"pinned solc fixture: expected VULNERABLE, got {reprStr vFix}"
  let auditFix ←
    match HeytingLean.BountyHunter.Solc.Audit.mkFromIR
        HeytingLean.BountyHunter.Solc.Fixtures.selector
        HeytingLean.BountyHunter.Solc.Fixtures.ir
        HeytingLean.BountyHunter.Solc.Fixtures.desiredFunc
        func
        HeytingLean.BountyHunter.Solc.Fixtures.slot with
    | .ok a => pure a
    | .error e => throw s!"pinned solc fixture: audit mkFromIR failed: {e}"
  if !auditFix.translationChecks.ok then
    throw s!"pinned solc fixture: translationChecks failed (missing={auditFix.translationChecks.missingEffects.size})"
  let s1 := HeytingLean.BountyHunter.Solc.Audit.artifactCanonicalString auditFix
  let s2 := HeytingLean.BountyHunter.Solc.Audit.artifactCanonicalString auditFix
  if s1 ≠ s2 then
    throw "pinned solc fixture: audit canonical string not stable"

def main (argv : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs argv

  if hasFlag args "--help" || hasFlag args "-h" then
    IO.println usage
    return 0

  -- Treat "no args" as a help request. This keeps local QA runners (which may
  -- smoke-run executables without arguments) from reporting false failures.
  if args.isEmpty then
    IO.println usage
    return 0

  if hasFlag args "--solc-emit" then
    match (← loadSolcOutputJsonE args) with
    | .error m =>
        eprintlnErr m
        IO.println usage
        return 1
    | .ok (j, src, cName) =>
        let sel : HeytingLean.BountyHunter.Solc.Selector :=
          { sourceUnit := src, contractName := cName, field := solcField args }
        match HeytingLean.BountyHunter.Solc.extractFieldE j sel with
        | .ok s =>
            IO.println s
            return 0
        | .error e =>
            eprintlnErr e
            return 1

  if hasFlag args "--solc-coverage" then
    match (← loadSolcOutputJsonE args) with
    | .error m =>
        eprintlnErr m
        IO.println usage
        return 1
    | .ok (j, src, cName) =>
        let sel : HeytingLean.BountyHunter.Solc.Selector :=
          { sourceUnit := src, contractName := cName, field := solcField args }
        let ir ←
          match HeytingLean.BountyHunter.Solc.extractFieldE j sel with
          | .ok s => pure s
          | .error e =>
              eprintlnErr e
              return 1
        let rep := HeytingLean.BountyHunter.Solc.analyzeE ir
        let base : Lean.Json :=
          Lean.Json.mkObj
            [ ("version", Lean.Json.str "bh.solc_coverage_bundle.v0")
            , ("sourceUnit", Lean.Json.str src)
            , ("contractName", Lean.Json.str cName)
            , ("field", Lean.Json.str (solcField args))
            , ("coverage", HeytingLean.BountyHunter.Solc.coverageReportToJson rep)
            ]
        outputJson base
        if hasFlag args "--coverage-strict" then
          if !rep.yulObjectOk || !rep.failures.isEmpty then
            return 3
        return 0

  if hasFlag args "--solc-emit-algebrair2-yul" then
    match (← loadSolcOutputJsonE args) with
    | .error m =>
        eprintlnErr m
        IO.println usage
        return 1
    | .ok (j, src, cName) =>
        let sel : HeytingLean.BountyHunter.Solc.Selector :=
          { sourceUnit := src, contractName := cName, field := solcField args }
        let ir ←
          match HeytingLean.BountyHunter.Solc.extractFieldE j sel with
          | .ok s => pure s
          | .error e =>
              eprintlnErr e
              return 1
        match HeytingLean.BountyHunter.AlgebraIR2.canonicalizeYulObjectE ir with
        | .ok (yul, _stats) =>
            IO.println yul
            return 0
        | .error e =>
            eprintlnErr e
            return 1

  if hasFlag args "--solc-decompile-solidity" then
    match (← loadSolcOutputJsonE args) with
    | .error m =>
        eprintlnErr m
        IO.println usage
        return 1
    | .ok (j, src, cName) =>
        let sel : HeytingLean.BountyHunter.Solc.Selector :=
          { sourceUnit := src, contractName := cName, field := solcField args }
        let ir ←
          match HeytingLean.BountyHunter.Solc.extractFieldE j sel with
          | .ok s => pure s
          | .error e =>
              eprintlnErr e
              return 1
        let base : Lean.Json := Lean.Json.mkObj [("version", Lean.Json.str "bh.solc_decompile_solidity.v0")]
        let (out, _) ← maybeAttachSolcDecompileSolidity args src cName ir base
        outputJson out
        return 0

  if hasFlag args "--solc-scan-risks-all-contracts" then
    match (← loadSolcOutputJsonEAnyContract args) with
    | .error m =>
        let v : Verdict := .outOfScope m
        outputJson (verdictBundleToJson v none)
        return 3
    | .ok (j, src) =>
        let names ←
          match HeytingLean.BountyHunter.Solc.listContractNamesE j src with
          | .ok ns => pure ns
          | .error e =>
              let v : Verdict := .outOfScope s!"solc list contracts failed: {e}"
              outputJson (verdictBundleToJson v none)
              return 3
        let mut stats : RiskScanStats := { contractsTotal := names.size }
        let mut r : HeytingLean.BountyHunter.Solc.YulTextMini.RiskReport := {}
        for cn in names do
          let selC : HeytingLean.BountyHunter.Solc.Selector :=
            { sourceUnit := src, contractName := cn, field := solcField args }
          match HeytingLean.BountyHunter.Solc.extractFieldE j selC with
          | .error e =>
              stats := { stats with failures := stats.failures.push (cn, "<extract>", e) }
          | .ok irC =>
              match scanRisksAllFunctionsE irC with
              | .ok (riskC, statsC) =>
                  if statsC.functionsParsed > 0 then
                    stats := { stats with contractsWithAnyParsedFn := stats.contractsWithAnyParsedFn + 1 }
                  stats :=
                    { stats with
                      functionsTotal := stats.functionsTotal + statsC.functionsTotal
                      functionsParsed := stats.functionsParsed + statsC.functionsParsed
                      failures := stats.failures ++
                        (statsC.failures.map (fun (p : String × String × String) => (cn, p.2.1, p.2.2)))
                    }
                  r := mergeRisk r riskC
              | .error e =>
                  stats := { stats with failures := stats.failures.push (cn, "<scan>", e) }
        let rNorm := HeytingLean.BountyHunter.Solc.YulTextMini.normalize r
        let base : Lean.Json :=
          Lean.Json.mkObj
            [ ("version", Lean.Json.str "bh.solc_risk_scan.v1")
            , ("mode", Lean.Json.str "all_contracts")
            , ("sourceUnit", Lean.Json.str src)
            , ("field", Lean.Json.str (solcField args))
            , ("risk", HeytingLean.BountyHunter.Solc.YulTextMini.riskToJson rNorm)
            , ("riskScan", riskScanStatsToJson stats)
            ]
        outputJson base
        return 0

  if hasFlag args "--solc-emit-algebrair" || hasFlag args "--solc-check-cei" ||
     hasFlag args "--solc-scan-risks" || hasFlag args "--solc-scan-risks-all" ||
     hasFlag args "--solc-check-cei-all-auto" || hasFlag args "--solc-scan-inconsistencies" ||
     hasFlag args "--solc-scan-call-interface" || hasFlag args "--solc-summarize" ||
     hasFlag args "--solc-reachability" || hasFlag args "--solc-check-inconsistency-closure" ||
     hasFlag args "--solc-check-temporal" ||
     hasFlag args "--solc-mine-invariants" ||
     hasFlag args "--solc-check-cross-contract-assumptions" then
    match (← loadSolcOutputJsonE args) with
    | .error m =>
        eprintlnErr m
        IO.println usage
        return 1
    | .ok (j, src, cName) =>
        let sel : HeytingLean.BountyHunter.Solc.Selector :=
          { sourceUnit := src, contractName := cName, field := solcField args }
        let ir ←
          match HeytingLean.BountyHunter.Solc.extractFieldE j sel with
          | .ok s => pure s
          | .error e =>
              eprintlnErr e
              return 1
        if hasFlag args "--solc-scan-risks-all" then
            match scanRisksAllFunctionsE ir with
            | .error e =>
                let v : Verdict := .outOfScope s!"solc ir risk scan unsupported: {e}"
                outputJson (verdictBundleToJson v none)
                return 3
            | .ok (risk, stats) =>
                let base : Lean.Json :=
                  Lean.Json.mkObj
                    [ ("version", Lean.Json.str "bh.solc_risk_scan.v1")
                    , ("mode", Lean.Json.str "all_functions")
                    , ("sourceUnit", Lean.Json.str src)
                    , ("contractName", Lean.Json.str cName)
                    , ("field", Lean.Json.str (solcField args))
                    , ("risk", HeytingLean.BountyHunter.Solc.YulTextMini.riskToJson risk)
                    , ("riskScan", riskScanStatsToJson stats)
                    ]
                let out ← maybeAttachSolcAudit args sel ir "<all>" "<all>" 0 base
                outputJson out
                return 0
        else
          pure ()
        if hasFlag args "--solc-check-cei-all-auto" then
          let fnsAll ←
            match HeytingLean.BountyHunter.Solc.YulTextMini.listFunctionNamesE ir with
            | .ok ns => pure ns
            | .error e =>
                let v : Verdict := .outOfScope s!"solc ir list functions failed: {e}"
                outputJson (verdictBundleToJson v none)
                return 3
          let ctx := buildCEIInlineContext ir fnsAll
          -- Heuristic: skip "slot checks" that are really just ReentrancyGuard enter/exit bookkeeping.
          -- Many contracts do harmless prelude calls (e.g. WETH unwrap / ERC20 transferFrom) before
          -- entering a nonReentrant section. Treat those as noise for the CEI "dominance" lane, which
          -- is intended to catch missing invariant-restoring writes (balances/ownership) rather than
          -- lock placement.
          let reentrancySlots : Std.HashSet Nat :=
            Id.run do
              let mut out : Std.HashSet Nat := Std.HashSet.emptyWithCapacity 8
              for (nm, effs) in ctx.inlineMap.toList do
                let low := nm.toLower
                if containsSubstr low "nonreentrant" || containsSubstr low "reentrancyguard" then
                  for e in effs do
                    match e with
                    | .storageWrite s => out := out.insert s
                    | _ => pure ()
              return out
          let inlineFn : String → Array Effect := fun nm => ctx.inlineMap.getD nm #[]
          let fns := fnsAll.toList.filter isInterestingSolcFnName
          let mut stats : CEIAllAutoStats :=
            { functionsTotal := fnsAll.size
              functionsSelected := fns.length
            }
          let mut findings : Array Lean.Json := #[]
          for fn in fns do
            match HeytingLean.BountyHunter.Solc.YulTextMini.parseFunctionBodyE ir fn with
            | .error e =>
                stats := { stats with failures := stats.failures.push (fn, e) }
            | .ok body =>
                if !bodyLooksLikeEntrypoint ctx.calledByAny fn body then
                  continue
                stats := { stats with functionsParsed := stats.functionsParsed + 1 }
                let effectsFn : HeytingLean.BountyHunter.Solc.YulTextMini.EffectsFn :=
                  fun env e =>
                    HeytingLean.BountyHunter.Solc.YulTextMini.effectsOfExprWithInline inlineFn env e
                let g0 := HeytingLean.BountyHunter.Solc.YulTextMini.toAlgebraIRWithEffects body effectsFn
                let g := dropStaticcallBoundaryEffects g0
                let choices :=
                  collectSlotChoices g |>.filter (fun ch =>
                    match ch with
                    | .literal s => !reentrancySlots.contains s
                    | .dyn _ => true)
                if choices.isEmpty then
                  continue
                stats := { stats with functionsWithAnySlot := stats.functionsWithAnySlot + 1 }
                let mut found := false
                for ch in choices do
                  if found then
                    continue
                  stats := { stats with checksRun := stats.checksRun + 1 }
                  let slotNat :=
                    match ch with
                    | .literal s => s
                    | .dyn _ => 0
                  let (v, w?) :=
                    match ch with
                    | .literal s => checkCEI g s
                    | .dyn s => checkCEISlotExpr g s
                  if v = Verdict.vulnerable then
                    stats := { stats with vulnerableCount := stats.vulnerableCount + 1 }
                    found := true
                    let base0 := verdictBundleToJson v w?
                    let base1 :=
                      match ch, base0 with
                      | .literal s, .obj kvs =>
                          Lean.Json.obj
                            (kvs.insert "selectedFunc" (Lean.Json.str fn) |>.insert "slot" (Lean.Json.num s))
                      | .dyn s, .obj kvs =>
                          Lean.Json.obj
                            (kvs.insert "selectedFunc" (Lean.Json.str fn) |>.insert "slotExpr" (Lean.Json.str s))
                      | _, other => other
                    let slotExpr? : Option String :=
                      match ch with
                      | .literal _ => none
                      | .dyn s => some s
                    let base2 :=
                      if hasFlag args "--emit-evidence" then
                        let e0 :=
                          HeytingLean.BountyHunter.AlgebraIR.Evidence.merge
                            (HeytingLean.BountyHunter.AlgebraIR.Evidence.deltaOfGraph g)
                            (HeytingLean.BountyHunter.AlgebraIR.Evidence.deltaOfCEIResult slotNat slotExpr? v w?)
                        let e1 := HeytingLean.BountyHunter.AlgebraIR.Evidence.close e0
                        match base1 with
                        | .obj kvs =>
                            Lean.Json.obj
                              (kvs.insert "evidence"
                                (HeytingLean.BountyHunter.AlgebraIR.Evidence.evidenceToJson e1))
                        | other => other
                      else
                        base1
                    let base3 :=
                      if hasFlag args "--emit-replay" then
                        match v, w? with
                        | Verdict.vulnerable, some w =>
                            match HeytingLean.BountyHunter.AlgebraIR.Replay.traceFromCEIWitnessE g w with
                            | .error err =>
                                match base2 with
                                | .obj kvs => Lean.Json.obj (kvs.insert "replayError" (Lean.Json.str err))
                                | other => other
                            | .ok t =>
                                match base2 with
                                | .obj kvs =>
                                    Lean.Json.obj
                                      (kvs.insert "replay"
                                        (HeytingLean.BountyHunter.AlgebraIR.Replay.traceToJson t))
                                | other => other
                        | _, _ => base2
                      else
                        base2
                    findings := findings.push base3
          let base : Lean.Json :=
            Lean.Json.mkObj
              [ ("version", Lean.Json.str "bh.solc_cei_all_auto.v0")
              , ("sourceUnit", Lean.Json.str src)
              , ("contractName", Lean.Json.str cName)
              , ("field", Lean.Json.str (solcField args))
              , ("stats", ceiAllAutoStatsToJson stats)
              , ("findings", Lean.Json.arr findings)
              ]
          outputJson base
          if findings.isEmpty then
            if stats.checksRun > 0 then
              return 0
            else
              return 3
          else
            return 2
        else
          pure ()
        if hasFlag args "--solc-scan-inconsistencies" then
          let fnsAll ←
            match HeytingLean.BountyHunter.Solc.YulTextMini.listFunctionNamesE ir with
            | .ok ns => pure ns
            | .error e =>
                let v : Verdict := .outOfScope s!"solc ir list functions failed: {e}"
                outputJson (verdictBundleToJson v none)
                return 3
          -- For inconsistency scanning we want coverage on internal helpers too.
          -- Adapters/factories often do all state updates in non-external helper functions.
          let fns := fnsAll.toList
          let mut stats : InconsistencyScanStats :=
            { functionsTotal := fnsAll.size
              functionsSelected := fns.length
            }
          let mut findings : Array Lean.Json := #[]
          let mut updatesByFunc : Array Lean.Json := #[]
          for fn in fns do
            match HeytingLean.BountyHunter.Solc.YulTextMini.scanIRInconsistencies ir fn with
            | .error e =>
                stats := { stats with failures := stats.failures.push (fn, e) }
            | .ok (fs, ds) =>
                stats := { stats with functionsParsed := stats.functionsParsed + 1 }
                if ds.size > 0 then
                  stats := { stats with functionsWithAnyUpdate := stats.functionsWithAnyUpdate + 1 }
                  let sampleSize : Nat := 60
                  let sample :=
                    Lean.Json.arr <|
                      (ds.take sampleSize).map HeytingLean.BountyHunter.Solc.YulTextMini.SlotDelta.toJson
                  updatesByFunc :=
                    updatesByFunc.push <|
                      Lean.Json.mkObj
                        [ ("selectedFunc", Lean.Json.str fn)
                        , ("updatesCount", Lean.Json.num ds.size)
                        , ("updatesSample", sample)
                        , ("updatesTruncated", Lean.Json.bool (ds.size > sampleSize))
                        ]
                if fs.size > 0 then
                  stats := { stats with findingsCount := stats.findingsCount + fs.size }
                  for f in fs do
                    let f0 := jsonInsertObjField f.toJson "selectedFunc" (Lean.Json.str fn)
                    let id ← HeytingLean.Util.sha256HexOfStringIO (HeytingLean.Util.JCS.canonicalString f0)
                    let f1 := jsonInsertObjField f0 "id" (Lean.Json.str id)
                    findings := findings.push f1
          let base : Lean.Json :=
            Lean.Json.mkObj
              [ ("version", Lean.Json.str "bh.solc_inconsistency_scan.v0")
              , ("sourceUnit", Lean.Json.str src)
              , ("contractName", Lean.Json.str cName)
              , ("field", Lean.Json.str (solcField args))
              , ("stats", inconsistencyScanStatsToJson stats)
              , ("findings", Lean.Json.arr findings)
              , ("updatesByFunc", Lean.Json.arr updatesByFunc)
              ]
          outputJson base
          if findings.isEmpty then
            if stats.functionsWithAnyUpdate > 0 then
              return 0
            else
              return 3
          else
            return 2
        if hasFlag args "--solc-scan-call-interface" then
          let fnsAll ←
            match HeytingLean.BountyHunter.Solc.YulTextMini.listFunctionNamesE ir with
            | .ok ns => pure ns
            | .error e =>
                let v : Verdict := .outOfScope s!"solc ir list functions failed: {e}"
                outputJson (verdictBundleToJson v none)
                return 3
          -- Privilege-aware scoring: many protocols have privileged configuration setters
          -- (initializer/onlyRole/onlyOwner). We compute a best-effort set of slot refs
          -- writable by *non-privileged* external entrypoints, and downgrade certain flags
          -- when a storage-derived call target appears to be privileged/immutable configuration.
          let ctx := HeytingLean.BountyHunter.Solc.YulTextMini.buildSummaryContext ir fnsAll 6
          let externalFns := fnsAll.filter (fun fn => fn.startsWith "external_fun_")
          let mut unprivWritableSlots : Std.HashSet Nat := {}
          let mut unprivWritableSlotRefs : Std.HashSet String := {}
          for ext in externalFns do
            let s := ctx.summaries.getD ext {}
            if HeytingLean.BountyHunter.Solc.YulTextMini.isPrivilegedEntrypointSummaryHeuristic s then
              continue
            for w in s.writes.toList do
              match w.toNat? with
              | none => pure ()
              | some n => unprivWritableSlots := unprivWritableSlots.insert n
              unprivWritableSlotRefs := unprivWritableSlotRefs.insert w
          let fns := fnsAll.toList.filter isInterestingSolcFnName
          let threshold : Nat := 7
          let mut functionsWithAnyCall : Nat := 0
          let mut functionsWithWriteAfterRiskyCall : Nat := 0
          let mut failures : Array Lean.Json := #[]
          let mut riskByFunc : Array Lean.Json := #[]
          let mut leads : Array Lean.Json := #[]
          let mut composedLeads : Array Lean.Json := #[]
          let tagSlotNat? (t : String) : Option Nat :=
            if t.startsWith "target_slot=" then
              (t.drop "target_slot=".length).toNat?
            else
              none
          let tagSlotRef? (t : String) : Option String :=
            if t.startsWith "target_slotref=" then
              some (t.drop "target_slotref=".length)
            else
              none
          let isValueBearingCall (c : HeytingLean.BountyHunter.Solc.YulTextMini.BoundaryCall) : Bool :=
            (c.kind = "call" || c.kind = "callcode") &&
              (c.tags.any (fun t => t = "value=callvalue" || t = "value=nonzero_const" || t = "value=nonzero_maybe"))
          for fn in fns do
            match HeytingLean.BountyHunter.Solc.YulTextMini.scanIRCallInterfaceScoredWithWrites ir fn with
            | .error e =>
                failures := failures.push (Lean.Json.mkObj [("fn", Lean.Json.str fn), ("error", Lean.Json.str e)])
            | .ok (calls, _topSites, score0, flags0, writesAny, writesAfter, writesAfterEv) =>
                let mut score := score0
                let mut flags := flags0
                -- Downgrade: storage-derived, value-bearing call to a target slot with no non-privileged writers.
                if flags.any (fun f => f.name = "value_bearing_call_to_nonconst_target") then
                  let mut downgraded : Bool := false
                  for c in calls do
                    if downgraded then
                      continue
                    if !(isValueBearingCall c) then
                      continue
                    if !(c.tags.any (· = "target=storage_derived")) then
                      continue
                    let slotNat? := c.tags.findSome? tagSlotNat?
                    let slotRef? := c.tags.findSome? tagSlotRef?
                    let hasNonPrivWriter :=
                      match slotNat?, slotRef? with
                      | some n, _ => unprivWritableSlots.contains n
                      | none, some sr => unprivWritableSlotRefs.contains sr
                      | none, none => false
                    if !hasNonPrivWriter then
                      score := (score - 10) + 4
                      flags := flags.filter (fun f => f.name ≠ "value_bearing_call_to_nonconst_target")
                      let ev :=
                        match slotNat?, slotRef? with
                        | some n, some sr =>
                            s!"storage-derived value-bearing call target slot={n} slotRef={sr} has no non-privileged external writers (heuristic); downgraded"
                        | some n, none =>
                            s!"storage-derived value-bearing call target slot={n} has no non-privileged external writers (heuristic); downgraded"
                        | none, some sr =>
                            s!"storage-derived value-bearing call target slotRef={sr} has no non-privileged external writers (heuristic); downgraded"
                        | none, none =>
                            "storage-derived value-bearing call target has no non-privileged external writers (heuristic); downgraded"
                      flags := flags.push { name := "value_bearing_call_to_privileged_or_immutable_target", weight := 4, evidence := ev }
                      downgraded := true
                if calls.size > 0 then
                  functionsWithAnyCall := functionsWithAnyCall + 1
                  if writesAfter > 0 then
                    functionsWithWriteAfterRiskyCall := functionsWithWriteAfterRiskyCall + 1
                  let sampleSize : Nat := 40
                  let sample :=
                    Lean.Json.arr <|
                      (calls.take sampleSize).map HeytingLean.BountyHunter.Solc.YulTextMini.BoundaryCall.toJson
                  let flagsJ :=
                    Lean.Json.arr <|
                      flags.map HeytingLean.BountyHunter.Solc.YulTextMini.CallRiskFlag.toJson
                  let writesAfterEvJ :=
                    Lean.Json.arr <|
                      writesAfterEv.map Lean.Json.str
                  let entry : Lean.Json :=
                      Lean.Json.mkObj
                        [ ("selectedFunc", Lean.Json.str fn)
                        , ("callsCount", Lean.Json.num calls.size)
                        , ("callsSample", sample)
                        , ("callsTruncated", Lean.Json.bool (calls.size > sampleSize))
                        , ("riskScore", Lean.Json.num score)
                        , ("riskFlags", flagsJ)
                        , ("writeStmtsAnyCount", Lean.Json.num writesAny)
                        , ("writeStmtsAfterRiskyCallCount", Lean.Json.num writesAfter)
                        , ("writeAfterRiskyCallEvidence", writesAfterEvJ)
                        ]
                  riskByFunc := riskByFunc.push entry
                  if score ≥ threshold then
                    leads := leads.push entry
                    if writesAfter > 0 then
                      composedLeads := composedLeads.push entry
          let base : Lean.Json :=
            Lean.Json.mkObj
              [ ("version", Lean.Json.str "bh.solc_call_interface.v1")
              , ("sourceUnit", Lean.Json.str src)
              , ("contractName", Lean.Json.str cName)
              , ("field", Lean.Json.str (solcField args))
              , ("threshold", Lean.Json.num threshold)
              , ("functionsTotal", Lean.Json.num fnsAll.size)
              , ("functionsSelected", Lean.Json.num fns.length)
              , ("functionsWithAnyCall", Lean.Json.num functionsWithAnyCall)
              , ("functionsWithWriteAfterRiskyCall", Lean.Json.num functionsWithWriteAfterRiskyCall)
              , ("failures", Lean.Json.arr failures)
              , ("riskByFunc", Lean.Json.arr riskByFunc)
              , ("leads", Lean.Json.arr leads)
              , ("composedLeads", Lean.Json.arr composedLeads)
              ]
          outputJson base
          if riskByFunc.isEmpty then
            return 3
          else
            return 0
        if hasFlag args "--solc-reachability" then
          let k : Nat :=
            match findArgVal args "--k" with
            | none => 2
            | some s => s.toNat?.getD 2
          if k < 1 || k > 3 then
            let v : Verdict := .outOfScope s!"only --k 1..3 is supported for --solc-reachability (got k={k})"
            outputJson (verdictBundleToJson v none)
            return 3
          let fnsAll ←
            match HeytingLean.BountyHunter.Solc.YulTextMini.listFunctionNamesE ir with
            | .ok ns => pure ns
            | .error e =>
                let v : Verdict := .outOfScope s!"solc ir list functions failed: {e}"
                outputJson (verdictBundleToJson v none)
                return 3
          let (stats, facts, fs) := HeytingLean.BountyHunter.Solc.YulTextMini.scanIRReachability ir fnsAll 6 k
          let mut findings : Array Lean.Json := #[]
          for f in fs do
            let f0 := f.toJson
            let id ← HeytingLean.Util.sha256HexOfStringIO (HeytingLean.Util.JCS.canonicalString f0)
            let f1 := jsonInsertObjField f0 "id" (Lean.Json.str id)
            findings := findings.push f1
          let base : Lean.Json :=
            Lean.Json.mkObj
              [ ("version", Lean.Json.str "bh.solc_reachability.v0")
              , ("sourceUnit", Lean.Json.str src)
              , ("contractName", Lean.Json.str cName)
              , ("field", Lean.Json.str (solcField args))
              , ("k", Lean.Json.num k)
              , ("stats", HeytingLean.BountyHunter.Solc.YulTextMini.ReachabilityScanStats.toJson stats)
              , ("facts", HeytingLean.BountyHunter.Solc.YulTextMini.Facts.toJson facts)
              , ("findings", Lean.Json.arr findings)
              ]
          outputJson base
          if findings.isEmpty then
            return 0
          else
            return 2
        if hasFlag args "--solc-check-inconsistency-closure" then
          let k : Nat :=
            match findArgVal args "--k" with
            | none => 2
            | some s => s.toNat?.getD 2
          if k < 1 || k > 3 then
            let v : Verdict := .outOfScope s!"only --k 1..3 is supported for --solc-check-inconsistency-closure (got k={k})"
            outputJson (verdictBundleToJson v none)
            return 3
          let fnsAll ←
            match HeytingLean.BountyHunter.Solc.YulTextMini.listFunctionNamesE ir with
            | .ok ns => pure ns
            | .error e =>
                let v : Verdict := .outOfScope s!"solc ir list functions failed: {e}"
                outputJson (verdictBundleToJson v none)
                return 3
          let (stats, facts, fs) := HeytingLean.BountyHunter.Solc.YulTextMini.scanIRReachability ir fnsAll 6 k
          let invs := HeytingLean.BountyHunter.Solc.YulTextMini.mineClosureInvariants fs
          let invsJson := Lean.Json.arr (invs.map HeytingLean.BountyHunter.Solc.YulTextMini.ClosureInvariant.toJson)
          let mut findings : Array Lean.Json := #[]
          for f in fs do
            let f0 := f.toJson
            let id ← HeytingLean.Util.sha256HexOfStringIO (HeytingLean.Util.JCS.canonicalString f0)
            let f1 := jsonInsertObjField f0 "id" (Lean.Json.str id)
            findings := findings.push f1
          let base : Lean.Json :=
            Lean.Json.mkObj
              [ ("version", Lean.Json.str "bh.solc_inconsistency_closure.v0")
              , ("sourceUnit", Lean.Json.str src)
              , ("contractName", Lean.Json.str cName)
              , ("field", Lean.Json.str (solcField args))
              , ("k", Lean.Json.num k)
              , ("stats", HeytingLean.BountyHunter.Solc.YulTextMini.ReachabilityScanStats.toJson stats)
              , ("facts", HeytingLean.BountyHunter.Solc.YulTextMini.Facts.toJson facts)
              , ("findings", Lean.Json.arr findings)
              , ("invariants", invsJson)
              ]
          outputJson base
          if invs.any (·.violated) then
            return 2
          else
            return 0
        if hasFlag args "--solc-check-temporal" then
          let qStr ←
            match findArgVal args "--query" with
            | none =>
                eprintlnErr "missing --query \"<dsl>\" for --solc-check-temporal"
                IO.println usage
                return 1
            | some s => pure s
          let q ←
            match HeytingLean.BountyHunter.Solc.YulTextMini.parseTemporalQuery? qStr with
            | .ok q => pure q
            | .error e =>
                let v : Verdict := .outOfScope s!"temporal query parse failed: {e}"
                outputJson (verdictBundleToJson v none)
                return 3
          let k : Nat :=
            match findArgVal args "--k" with
            | none => q.steps.size
            | some s => s.toNat?.getD q.steps.size
          if k ≠ q.steps.size then
            let v : Verdict := .outOfScope s!"--k must match number of steps in query (k={k}, steps={q.steps.size})"
            outputJson (verdictBundleToJson v none)
            return 3
          let fnsAll ←
            match HeytingLean.BountyHunter.Solc.YulTextMini.listFunctionNamesE ir with
            | .ok ns => pure ns
            | .error e =>
                let v : Verdict := .outOfScope s!"solc ir list functions failed: {e}"
                outputJson (verdictBundleToJson v none)
                return 3
          let (stats, ms) := HeytingLean.BountyHunter.Solc.YulTextMini.scanIRTemporalQuery ir fnsAll q 6 24
          let base : Lean.Json :=
            Lean.Json.mkObj
              [ ("version", Lean.Json.str "bh.solc_temporal_query.v0")
              , ("sourceUnit", Lean.Json.str src)
              , ("contractName", Lean.Json.str cName)
              , ("field", Lean.Json.str (solcField args))
              , ("query", Lean.Json.str qStr)
              , ("k", Lean.Json.num k)
              , ("stats", HeytingLean.BountyHunter.Solc.YulTextMini.TemporalScanStats.toJson stats)
              , ("matches", Lean.Json.arr (ms.map HeytingLean.BountyHunter.Solc.YulTextMini.TemporalMatch.toJson))
              ]
          outputJson base
          if ms.isEmpty then
            return 0
          else
            return 2
        if hasFlag args "--solc-mine-invariants" then
          let k : Nat :=
            match findArgVal args "--k" with
            | none => 3
            | some s => s.toNat?.getD 3
          if k < 1 || k > 3 then
            let v : Verdict := .outOfScope s!"only --k 1..3 is supported for --solc-mine-invariants (got k={k})"
            outputJson (verdictBundleToJson v none)
            return 3
          let fnsAll ←
            match HeytingLean.BountyHunter.Solc.YulTextMini.listFunctionNamesE ir with
            | .ok ns => pure ns
            | .error e =>
                let v : Verdict := .outOfScope s!"solc ir list functions failed: {e}"
                outputJson (verdictBundleToJson v none)
                return 3

          -- 1) Closure / reachability-derived invariants (WP5-lite).
          let (_statsR, _factsR, fs) := HeytingLean.BountyHunter.Solc.YulTextMini.scanIRReachability ir fnsAll 6 k
          let closureInvs := HeytingLean.BountyHunter.Solc.YulTextMini.mineClosureInvariants fs
          let mut invs : Array HeytingLean.BountyHunter.Solc.YulTextMini.MinedInvariant :=
            closureInvs.map HeytingLean.BountyHunter.Solc.YulTextMini.MinedInvariant.ofClosure

          -- 2) Risk scan primitives.
          match scanRisksAllFunctionsE ir with
          | .error _ => pure ()
          | .ok (risk, _stats) =>
              invs := invs ++ HeytingLean.BountyHunter.Solc.YulTextMini.minedOfRisk risk

          -- 3) Call-interface risk flags aggregated across functions (deterministic sample).
          -- Privilege-aware downgrade (best-effort):
          -- If a value-bearing call target is derived from a storage slot ref that has no
          -- non-privileged external writers, we treat it as privileged/immutable configuration.
          let ctxCI := HeytingLean.BountyHunter.Solc.YulTextMini.buildSummaryContext ir fnsAll 6
          let externalFnsCI := fnsAll.filter (fun fn => fn.startsWith "external_fun_")
          let mut unprivWritableSlotsCI : Std.HashSet Nat := {}
          let mut unprivWritableSlotRefsCI : Std.HashSet String := {}
          for ext in externalFnsCI do
            let s := ctxCI.summaries.getD ext {}
            if HeytingLean.BountyHunter.Solc.YulTextMini.isPrivilegedEntrypointSummaryHeuristic s then
              continue
            for w in s.writes.toList do
              match w.toNat? with
              | none => pure ()
              | some n => unprivWritableSlotsCI := unprivWritableSlotsCI.insert n
              unprivWritableSlotRefsCI := unprivWritableSlotRefsCI.insert w
          let tagSlotNat? (t : String) : Option Nat :=
            if t.startsWith "target_slot=" then
              (t.drop "target_slot=".length).toNat?
            else
              none
          let tagSlotRef? (t : String) : Option String :=
            if t.startsWith "target_slotref=" then
              some (t.drop "target_slotref=".length)
            else
              none
          let isValueBearingCall (c : HeytingLean.BountyHunter.Solc.YulTextMini.BoundaryCall) : Bool :=
            (c.kind = "call" || c.kind = "callcode") &&
              (c.tags.any (fun t => t = "value=callvalue" || t = "value=nonzero_const" || t = "value=nonzero_maybe"))
          let fns := fnsAll.toList.filter isInterestingSolcFnName
          let mut flagCounts : Std.HashMap String Nat := {}
          let mut flagSample : Std.HashMap String Lean.Json := {}
          for fn in fns do
            match HeytingLean.BountyHunter.Solc.YulTextMini.scanIRCallInterfaceScoredWithWrites ir fn with
            | .error _ => pure ()
            | .ok (calls, _topSites, _score, flags0, _writesAny, _writesAfter, _writesAfterEv) =>
                let mut flags := flags0
                if flags.any (fun f => f.name = "value_bearing_call_to_nonconst_target") then
                  let mut downgraded : Bool := false
                  for c in calls do
                    if downgraded then
                      continue
                    if !(isValueBearingCall c) then
                      continue
                    if !(c.tags.any (· = "target=storage_derived")) then
                      continue
                    let slotNat? := c.tags.findSome? tagSlotNat?
                    let slotRef? := c.tags.findSome? tagSlotRef?
                    let hasNonPrivWriter :=
                      match slotNat?, slotRef? with
                      | some n, _ => unprivWritableSlotsCI.contains n
                      | none, some sr => unprivWritableSlotRefsCI.contains sr
                      | none, none => false
                    if !hasNonPrivWriter then
                      flags := flags.filter (fun f => f.name ≠ "value_bearing_call_to_nonconst_target")
                      let ev :=
                        match slotNat?, slotRef? with
                        | some n, some sr =>
                            s!"storage-derived value-bearing call target slot={n} slotRef={sr} has no non-privileged external writers (heuristic); downgraded"
                        | some n, none =>
                            s!"storage-derived value-bearing call target slot={n} has no non-privileged external writers (heuristic); downgraded"
                        | none, some sr =>
                            s!"storage-derived value-bearing call target slotRef={sr} has no non-privileged external writers (heuristic); downgraded"
                        | none, none =>
                            "storage-derived value-bearing call target has no non-privileged external writers (heuristic); downgraded"
                      flags := flags.push { name := "value_bearing_call_to_privileged_or_immutable_target", weight := 4, evidence := ev }
                      downgraded := true
                for fl in flags do
                  -- Exclude very-low-signal flags from invariant mining. These are still
                  -- useful for ranking/composition in `--solc-scan-call-interface`, but as
                  -- global “invariants” they dominate adapter-heavy contracts with benign
                  -- ETH-transfer patterns.
                  if fl.weight < 6 then
                    continue
                  let cur := flagCounts.getD fl.name 0
                  flagCounts := flagCounts.insert fl.name (cur + 1)
                  if (flagSample.get? fl.name).isNone then
                    flagSample :=
                      flagSample.insert fl.name <|
                        Lean.Json.mkObj
                          [ ("selectedFunc", Lean.Json.str fn)
                          , ("flag", HeytingLean.BountyHunter.Solc.YulTextMini.CallRiskFlag.toJson fl)
                          ]
          for (nm, cnt) in flagCounts.toList do
            let ev := flagSample.getD nm Lean.Json.null
            invs :=
              invs.push
                { id := s!"call_interface:{nm}"
                  kind := "call_interface"
                  violated := cnt > 0
                  reason := s!"call-interface: flag '{nm}' observed (count={cnt})"
                  evidence := ev
                }

          -- 4) Delta inconsistency presence (very coarse).
          let mut deltaFindings : Nat := 0
          for fn in fnsAll.toList do
            match HeytingLean.BountyHunter.Solc.YulTextMini.scanIRInconsistencies ir fn with
            | .error _ => pure ()
            | .ok (fs, _ds) =>
                if fs.size > 0 then
                  deltaFindings := deltaFindings + fs.size
          invs :=
            invs.push
              { id := "no_delta_inconsistency"
                kind := "delta"
                violated := deltaFindings > 0
                reason := s!"delta scan: mapping-like groups with net delta ≠ 0 (findings={deltaFindings})"
                evidence := Lean.Json.mkObj [("findingsCount", Lean.Json.num deltaFindings)]
              }

          let base : Lean.Json :=
            Lean.Json.mkObj
              [ ("version", Lean.Json.str "bh.solc_mine_invariants.v0")
              , ("sourceUnit", Lean.Json.str src)
              , ("contractName", Lean.Json.str cName)
              , ("field", Lean.Json.str (solcField args))
              , ("k", Lean.Json.num k)
              , ("invariants", Lean.Json.arr (invs.map HeytingLean.BountyHunter.Solc.YulTextMini.MinedInvariant.toJson))
              ]
          outputJson base
          if invs.any (·.violated) then
            return 2
          else
            return 0
        if hasFlag args "--solc-check-cross-contract-assumptions" then
          let calleeName ←
            match findArgVal args "--solc-callee-contract" with
            | none =>
                eprintlnErr "missing --solc-callee-contract <name> for --solc-check-cross-contract-assumptions"
                IO.println usage
                return 1
            | some s => pure s
          let selCallee : HeytingLean.BountyHunter.Solc.Selector :=
            { sourceUnit := src, contractName := calleeName, field := solcField args }
          let irCallee ←
            match HeytingLean.BountyHunter.Solc.extractFieldE j selCallee with
            | .ok s => pure s
            | .error e =>
                let v : Verdict := .outOfScope s!"solc ir extract callee failed: {e}"
                outputJson (verdictBundleToJson v none)
                return 3

          let fnsCallerAll :=
            match HeytingLean.BountyHunter.Solc.YulTextMini.listFunctionNamesE ir with
            | .ok ns => ns
            | .error _ => #[]
          let fnsCalleeAll :=
            match HeytingLean.BountyHunter.Solc.YulTextMini.listFunctionNamesE irCallee with
            | .ok ns => ns
            | .error _ => #[]

          let fnsCaller := fnsCallerAll.toList.filter isInterestingSolcFnName
          let fnsCallee := fnsCalleeAll.toList.filter isInterestingSolcFnName

          -- Callee evidence: does it ever call back into `msg.sender`?
          let mut calleeCallbackEvidence : Array Lean.Json := #[]
          let mut calleeFailures : Array Lean.Json := #[]
          for fn in fnsCallee do
            match HeytingLean.BountyHunter.Solc.YulTextMini.scanIRBoundaryCalls irCallee fn with
            | .error e =>
                calleeFailures := calleeFailures.push (Lean.Json.mkObj [("fn", Lean.Json.str fn), ("error", Lean.Json.str e)])
            | .ok calls =>
                for c in calls do
                  let isCallback :=
                    (c.kind = "call" || c.kind = "callcode") &&
                      (c.tags.any (· = "target=cx.caller()") || c.tags.any (· = "target=cx.caller") || c.tags.any (· = "target=cx.caller_derived"))
                  if isCallback && calleeCallbackEvidence.size < 12 then
                    calleeCallbackEvidence :=
                      calleeCallbackEvidence.push <|
                        Lean.Json.mkObj
                          [ ("selectedFunc", Lean.Json.str fn)
                          , ("call", HeytingLean.BountyHunter.Solc.YulTextMini.BoundaryCall.toJson c)
                          ]

          -- Caller evidence: writes after any effectful boundary call.
          let mut callerLeads : Array Lean.Json := #[]
          let mut callerFailures : Array Lean.Json := #[]
          for fn in fnsCaller do
            match HeytingLean.BountyHunter.Solc.YulTextMini.scanIRWritesAfterAnyEffectfulCall ir fn with
            | .error e =>
                callerFailures := callerFailures.push (Lean.Json.mkObj [("fn", Lean.Json.str fn), ("error", Lean.Json.str e)])
            | .ok (writesAfter, evs) =>
                if writesAfter > 0 then
                  callerLeads :=
                    callerLeads.push <|
                      Lean.Json.mkObj
                        [ ("selectedFunc", Lean.Json.str fn)
                        , ("writeStmtsAfterAnyCallCount", Lean.Json.num writesAfter)
                        , ("writeAfterAnyCallEvidence", Lean.Json.arr (evs.map Lean.Json.str))
                        ]

          let calleeCallbackCapable := !calleeCallbackEvidence.isEmpty
          let mut findings : Array Lean.Json := #[]
          if calleeCallbackCapable && !callerLeads.isEmpty then
            for lead in callerLeads do
              let f0 :=
                Lean.Json.mkObj
                  [ ("property", Lean.Json.str "caller_writes_after_call_into_callback_capable_callee")
                  , ("callerContract", Lean.Json.str cName)
                  , ("calleeContract", Lean.Json.str calleeName)
                  , ("callerLead", lead)
                  , ("calleeCallbackEvidence", Lean.Json.arr calleeCallbackEvidence)
                  ]
              let id ← HeytingLean.Util.sha256HexOfStringIO (HeytingLean.Util.JCS.canonicalString f0)
              let f1 := jsonInsertObjField f0 "id" (Lean.Json.str id)
              findings := findings.push f1

          let base : Lean.Json :=
            Lean.Json.mkObj
              [ ("version", Lean.Json.str "bh.solc_cross_contract_assumptions.v0")
              , ("sourceUnit", Lean.Json.str src)
              , ("callerContract", Lean.Json.str cName)
              , ("calleeContract", Lean.Json.str calleeName)
              , ("field", Lean.Json.str (solcField args))
              , ("calleeCallbackEvidence", Lean.Json.arr calleeCallbackEvidence)
              , ("callerLeads", Lean.Json.arr callerLeads)
              , ("failures", Lean.Json.arr (calleeFailures ++ callerFailures))
              , ("findings", Lean.Json.arr findings)
              ]
          outputJson base
          if findings.isEmpty then
            return 0
          else
            return 2
        else
          pure ()
        if hasFlag args "--solc-summarize" then
          let fnsAll ←
            match HeytingLean.BountyHunter.Solc.YulTextMini.listFunctionNamesE ir with
            | .ok ns => pure ns
            | .error e =>
                let v : Verdict := .outOfScope s!"solc ir list functions failed: {e}"
                outputJson (verdictBundleToJson v none)
                return 3
          let ctx := HeytingLean.BountyHunter.Solc.YulTextMini.buildSummaryContext ir fnsAll 6
          let base : Lean.Json :=
            Lean.Json.mkObj
              [ ("version", Lean.Json.str "bh.solc_summarize.v0")
              , ("sourceUnit", Lean.Json.str src)
              , ("contractName", Lean.Json.str cName)
              , ("field", Lean.Json.str (solcField args))
              , ("summary", HeytingLean.BountyHunter.Solc.YulTextMini.SummaryContext.toJson ctx)
              ]
          outputJson base
          return 0
        let desired := solcFuncName args
        let func ←
          match resolveSolcFuncNameE ir desired with
          | .ok f => pure f
          | .error e =>
              let v : Verdict := .outOfScope s!"solc ir func resolve failed: {e}"
              outputJson (verdictBundleToJson v none)
              return 3
        match HeytingLean.BountyHunter.Solc.YulTextMini.parseFunctionBodyE ir func with
        | .error e =>
            let v : Verdict := .outOfScope s!"solc ir parse unsupported: {e}"
            outputJson (verdictBundleToJson v none)
            return 3
        | .ok body =>
            if hasFlag args "--solc-scan-risks" then
              let risk :=
                HeytingLean.BountyHunter.Solc.YulTextMini.normalize
                  (HeytingLean.BountyHunter.Solc.YulTextMini.scanStmts body)
              let base : Lean.Json :=
                Lean.Json.mkObj
                  [ ("version", Lean.Json.str "bh.solc_risk_scan.v1")
                  , ("mode", Lean.Json.str "single_function")
                  , ("sourceUnit", Lean.Json.str src)
                  , ("contractName", Lean.Json.str cName)
                  , ("field", Lean.Json.str (solcField args))
                  , ("desiredFunc", Lean.Json.str desired)
                  , ("selectedFunc", Lean.Json.str func)
                  , ("risk", HeytingLean.BountyHunter.Solc.YulTextMini.riskToJson risk)
                  ]
              let out ← maybeAttachSolcAudit args sel ir desired func 0 base
              outputJson out
              return 0
            let fnsAll :=
              match HeytingLean.BountyHunter.Solc.YulTextMini.listFunctionNamesE ir with
              | .ok ns => ns
              | .error _ => #[]
            let ctx := buildCEIInlineContext ir fnsAll
            let inlineFn : String → Array Effect := fun nm => ctx.inlineMap.getD nm #[]
            let effectsFn : HeytingLean.BountyHunter.Solc.YulTextMini.EffectsFn :=
              fun env e => HeytingLean.BountyHunter.Solc.YulTextMini.effectsOfExprWithInline inlineFn env e
            let g0 := HeytingLean.BountyHunter.Solc.YulTextMini.toAlgebraIRWithEffects body effectsFn
            let g := dropStaticcallBoundaryEffects g0
            if hasFlag args "--solc-emit-algebrair" then
              IO.println (graphToCanonicalString g)
              return 0
            -- Otherwise expect CEI check.
            match resolveSlotChoiceE args g with
            | .error e =>
                eprintlnErr e
                IO.println usage
                return 1
              | .ok choice =>
                  let slotNat :=
                    match choice with
                    | .literal s => s
                    | .dyn _ => 0
                  let (v, w?) :=
                    match choice with
                    | .literal s => checkCEI g s
                    | .dyn s => checkCEISlotExpr g s
                  let base0 := verdictBundleToJson v w?
                  let base :=
                    match choice, base0 with
                    | .dyn s, .obj kvs => Lean.Json.obj (kvs.insert "slotExpr" (Lean.Json.str s))
                    | _, _ => base0
                  let out :=
                    maybeAttachReplay args g slotNat v w? (maybeAttachEvidence args g slotNat v w? base)
                  let out ← maybeAttachSolcAudit args sel ir desired func slotNat out
                  let out ← maybeAttachFoundry args j src ir g slotNat cName desired v w? out
                  let (out, _) ← maybeAttachSolcDecompileSolidity args src cName ir out
                  let out ← maybeAttachFoundryParity args j src ir cName out
                  outputJson out
                  match v with
                  | Verdict.safe => return 0
                  | Verdict.vulnerable => return 2
                  | Verdict.outOfScope _ => return 3
  else
    pure ()

  if hasFlag args "--selftest" then
    match selftestJsonRoundtrip with
    | .ok () =>
        IO.println "OK"
        return 0
    | .error e =>
        eprintlnErr e
        return 1

  if hasFlag args "--dump-example" then
    match findArgVal args "--dump-example" with
    | none =>
        eprintlnErr "missing example name after --dump-example"
        IO.println usage
        return 1
    | some ex =>
        match parseExample ex with
        | .error m =>
            eprintlnErr m
            return 1
        | .ok g =>
            outputJson (graphToJson g)
            return 0

  if hasFlag args "--dump-yulmini-example" then
    match findArgVal args "--dump-yulmini-example" with
    | none =>
        eprintlnErr "missing example name after --dump-yulmini-example"
        IO.println usage
        return 1
    | some ex =>
        match parseYulMiniExample ex with
        | .error m =>
            eprintlnErr m
            return 1
        | .ok p =>
            IO.println (HeytingLean.BountyHunter.YulMini.programToCanonicalString p)
            return 0

  if hasFlag args "--yulmini-roundtrip" then
    let pE : IO (Except String HeytingLean.BountyHunter.YulMini.Program) := do
      match findArgVal args "--yulmini-example" with
      | some ex => pure (parseYulMiniExample ex)
      | none =>
          match findArgVal args "--yulmini-input" with
          | none => pure (.error "missing --yulmini-input <file.json> (or --yulmini-example <name>) for --yulmini-roundtrip")
          | some path =>
              match (← readFileE path) with
              | .error m => pure (.error m)
              | .ok raw => pure (HeytingLean.BountyHunter.YulMini.parseProgramStringE raw)
    let p ←
      match (← pE) with
      | .ok p => pure p
      | .error m =>
          eprintlnErr m
          IO.println usage
          return 1
    let canon := HeytingLean.BountyHunter.YulMini.programToCanonicalString p
    match HeytingLean.BountyHunter.YulMini.parseProgramStringE canon with
    | .error e =>
        eprintlnErr s!"yulmini roundtrip parse error: {e}"
        return 1
    | .ok p2 =>
        if HeytingLean.BountyHunter.YulMini.programToJson p2 ==
            HeytingLean.BountyHunter.YulMini.programToJson p then
          IO.println canon
          return 0
        else
          eprintlnErr "yulmini roundtrip mismatch (parse(print(parse(x))) != parse(x))"
          return 1

  if hasFlag args "--roundtrip" then
    let gE : IO (Except String Graph) := do
      match findArgVal args "--example" with
      | some ex => pure (parseExample ex)
      | none =>
          match findArgVal args "--input" with
          | none => pure (.error "missing --input <file.json> (or --example <name>) for --roundtrip")
          | some path =>
              match (← readFileE path) with
              | .error m => pure (.error m)
              | .ok raw => pure (parseGraphStringE raw)
    let g ←
      match (← gE) with
      | .ok g => pure g
      | .error m =>
          eprintlnErr m
          IO.println usage
          return 1
    let canon := graphToCanonicalString g
    match parseGraphStringE canon with
    | .error e =>
        eprintlnErr s!"roundtrip parse error: {e}"
        return 1
    | .ok g2 =>
        if g2 = g then
          IO.println canon
          return 0
        else
          eprintlnErr "roundtrip mismatch (parse(print(parse(x))) != parse(x))"
          return 1

  -- Phase 1: YulMini → AlgebraIR pipeline.
  if hasFlag args "--yulmini-input" || hasFlag args "--yulmini-example" then
    let funcName := findFuncName args
    let pE : IO (Except String HeytingLean.BountyHunter.YulMini.Program) := do
      match findArgVal args "--yulmini-example" with
      | some ex => pure (parseYulMiniExample ex)
      | none =>
          match findArgVal args "--yulmini-input" with
          | none => pure (.error "missing --yulmini-input <file.json> (or --yulmini-example <name>)")
          | some path =>
              match (← readFileE path) with
              | .error m => pure (.error m)
              | .ok raw => pure (HeytingLean.BountyHunter.YulMini.parseProgramStringE raw)
    let p ←
      match (← pE) with
      | .ok p => pure p
      | .error m =>
          eprintlnErr m
          IO.println usage
          return 1
    let g ←
      match HeytingLean.BountyHunter.YulMini.translateProgram p funcName with
      | .ok g => pure g
      | .error e =>
          eprintlnErr e
          return 1
    if hasFlag args "--emit-algebrair" then
      IO.println (graphToCanonicalString g)
      return 0
    -- Otherwise expect CEI check.
    if !hasFlag args "--check-cei" then
      eprintlnErr "missing --emit-algebrair or --check-cei"
      IO.println usage
      return 1
    match resolveSlotChoiceE args g with
    | .error e =>
        eprintlnErr e
        IO.println usage
        return 1
    | .ok choice =>
        let slotNat :=
          match choice with
          | .literal s => s
          | .dyn _ => 0
        let (v, w?) :=
          match choice with
          | .literal s => checkCEI g s
          | .dyn s => checkCEISlotExpr g s
        let base0 := verdictBundleToJson v w?
        let base :=
          match choice, base0 with
          | .dyn s, .obj kvs => Lean.Json.obj (kvs.insert "slotExpr" (Lean.Json.str s))
          | _, _ => base0
        let out := maybeAttachReplay args g slotNat v w? (maybeAttachEvidence args g slotNat v w? base)
        outputJson out
        match v with
        | Verdict.safe => return 0
        | Verdict.vulnerable => return 2
        | Verdict.outOfScope _ => return 3

  let graphE : IO (Except String Graph) := do
    match findArgVal args "--example" with
    | some ex => pure (parseExample ex)
    | none =>
        match findArgVal args "--input" with
        | none => pure (.error "missing --input <file.json> (or --example <name>)")
        | some path =>
            match (← readFileE path) with
            | .error m => pure (.error m)
            | .ok raw => pure (parseGraphStringE raw)

  let g ←
    match (← graphE) with
    | .ok g => pure g
    | .error m =>
        eprintlnErr m
        IO.println usage
        return 1

  if !hasFlag args "--check-cei" then
    eprintlnErr "missing --check-cei"
    IO.println usage
    return 1

  match resolveSlotChoiceE args g with
  | .error e =>
      eprintlnErr e
      IO.println usage
      return 1
  | .ok choice =>
      let slotNat :=
        match choice with
        | .literal s => s
        | .dyn _ => 0
      let (v, w?) :=
        match choice with
        | .literal s => checkCEI g s
        | .dyn s => checkCEISlotExpr g s
      let base0 := verdictBundleToJson v w?
      let base :=
        match choice, base0 with
        | .dyn s, .obj kvs => Lean.Json.obj (kvs.insert "slotExpr" (Lean.Json.str s))
        | _, _ => base0
      let out := maybeAttachReplay args g slotNat v w? (maybeAttachEvidence args g slotNat v w? base)
      outputJson out
      match v with
      | Verdict.safe => return 0
      | Verdict.vulnerable => return 2
      | Verdict.outOfScope _ => return 3
