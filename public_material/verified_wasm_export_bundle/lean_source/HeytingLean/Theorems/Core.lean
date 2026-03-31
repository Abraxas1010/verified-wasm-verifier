import Lean

namespace HeytingLean
namespace Theorems

open Lean
open Std
open System

/-- Stable identifier for a theorem or definition. -/
structure ThmId where
  name : Name
  deriving Repr, Inhabited, BEq

/-- Classification of theorem/proof entries (stringly-typed for easy interop). -/
abbrev ThmKind := String

/-- Canonical kind labels. -/
def kindComputational : ThmKind := "computational"
def kindProperty : ThmKind := "property"
def kindMeta : ThmKind := "meta"

/-- Render a kind as a string for manifests/JSON. -/
def kindToString (k : ThmKind) : String := k

/-- Allowed namespace prefixes to include in the manifest. -/
def allowedPrefixes : List Name :=
  [ `HeytingLean, `Mathlib, `quantumInfo ]

private def hasAllowedPrefix (n : Name) : Bool :=
  allowedPrefixes.any (fun p => p.isPrefixOf n)

/-- Optional tagging hints for theorem blocks. -/
structure ThmTag where
  namespaceHint : List String := []
  lensHint : List String := []
  notes : Option String := none
  deriving Repr, Inhabited

/-- Core record capturing a tagged theorem/definition. -/
structure ThmBlock where
  id : ThmId
  typeStr : String
  declName : Name
  tags : ThmTag
  category : String
  kind : ThmKind
  deriving Inhabited, Repr

/-- Simple marker attribute for theorem blocks (currently used for discoverability only). -/
initialize apmtThmAttr : TagAttribute ←
  registerTagAttribute `apmt_thm
    "Mark a theorem/def as a theorem block with optional tags"

/-- Inference: map a declaration name to a coarse category based on namespace prefixes. -/
def inferCategory (n : Name) : String :=
  let segs := n.components.map Name.toString
  let pref := List.isPrefixOf
  match segs with
  | [] => "uncategorized"
  | h :: _ =>
      if pref ["HeytingLean", "LoF"] segs then "lof"
      else if pref ["HeytingLean", "LambdaIR"] segs then "lambda-ir"
      else if pref ["HeytingLean", "MiniC"] segs then "minic"
      else if pref ["HeytingLean", "LeanCore"] segs
        ∨ pref ["HeytingLean", "LeanCoreV2"] segs then "lean-core"
      else if pref ["HeytingLean", "Exec"] segs then "exec"
      else if pref ["HeytingLean", "PCC"] segs then "pcc"
      else if pref ["HeytingLean", "Policy"] segs
        ∨ pref ["HeytingLean", "Payments"] segs
        ∨ pref ["HeytingLean", "Contracts"] segs
        ∨ pref ["HeytingLean", "Blockchain"] segs
        ∨ pref ["HeytingLean", "Chain"] segs
        ∨ pref ["HeytingLean", "Gateway"] segs then "policy"
      else if pref ["HeytingLean", "TCB"] segs
        ∨ pref ["HeytingLean", "Meta"] segs then "meta"
      else if pref ["HeytingLean", "Crypto"] segs then "crypto"
      else if pref ["HeytingLean", "Topos"] segs then "topos"
      else if pref ["HeytingLean", "Logic"] segs
        ∨ pref ["HeytingLean", "Ontology"] segs
        ∨ pref ["HeytingLean", "Epistemic"] segs then "logic"
      else if pref ["HeytingLean", "Physics"] segs then "physics"
      else if pref ["HeytingLean", "Numbers"] segs then "numbers"
      else if pref ["HeytingLean", "Automation"] segs then "automation"
      else if pref ["HeytingLean", "Runtime"] segs
        ∨ pref ["HeytingLean", "Computation"] segs
        ∨ pref ["HeytingLean", "Computing"] segs then "runtime"
      else if h = "Mathlib" then "vendor/mathlib"
      else if h = "quantumInfo" then "vendor/quantumInfo"
      else "uncategorized"

/-- Helper to build a theorem block with inferred category and optional overrides. -/
def mkBlock (declName : Name) (typeStr : String)
    (kind : ThmKind := kindProperty) (tags : ThmTag := {}) : ThmBlock :=
  { id := { name := declName }
    typeStr := typeStr
    declName := declName
    tags := tags
    category := inferCategory declName
    kind := kind }

/-- Stable manifest version for theorem metadata. -/
def manifestVersion : String := "1"

/-- Format tag advertised by the theorems manifest JSON. -/
def manifestFormat : String := "apmt_theorems_v1"

/-- Relative path (from the repo root) for theorems_manifest.json. -/
def manifestPath : String := "artifacts/theorems_manifest.json"

/-- Build blocks from an environment by prefix filter. Default kind is property. -/
def blocksFromEnv (env : Environment) : Array ThmBlock :=
  env.constants.fold (init := #[]) fun acc n ci =>
    if hasAllowedPrefix n then
      acc.push <| mkBlock n (toString ci.type) kindProperty
    else acc

/-- Load an environment rooted at `HeytingLean` plus vendor deps. Falls back to smaller sets if needed. -/
def loadProjectEnv : IO Environment := do
  let base := System.FilePath.mk "."
  let sysroot ← Lean.findSysroot
  let candidates : List System.FilePath :=
    [ base / ".lake" / "build" / "lib" / "lean"
    , base / ".lake" / "packages" / "mathlib" / ".lake" / "build" / "lib" / "lean"
    , base / ".lake" / "packages" / "quantumInfo" / ".lake" / "build" / "lib" / "lean"
    , sysroot / "lib" / "lean"
    ]
  let existing0 ← Lean.searchPathRef.get
  let extras ← candidates.filterM (fun p => do
    let ok ← p.pathExists
    pure (ok && !existing0.contains p))
  if !extras.isEmpty || existing0.isEmpty then
    -- Preserve any existing paths and append missing candidates.
    Lean.searchPathRef.set (existing0 ++ extras)
  let attempts : List (Array Lean.Import) :=
    [ #[{ module := `HeytingLean }, { module := `Mathlib }, { module := `quantumInfo }]
    , #[{ module := `HeytingLean }, { module := `Mathlib }]
    , #[{ module := `HeytingLean }]
    ]
  let rec tryImports : List (Array Lean.Import) → IO Environment
    | [] => throw <| IO.userError "importModules failed for all import sets"
    | imports :: rest => do
        let res ← (Lean.importModules imports {} 0).toBaseIO
        match res with
        | .ok env => pure env
        | .error _ => tryImports rest
  tryImports attempts

/-- Discover theorem blocks from the project and vendor namespaces. -/
def discoverBlocksIO : IO (Array ThmBlock) := do
  let env ← loadProjectEnv
  let constCount := env.constants.fold (init := 0) (fun acc _ _ => acc + 1)
  let filtered := blocksFromEnv env
  IO.println s!"[discoverBlocks] env.consts={constCount} filtered={filtered.size}"
  pure filtered

/-- Merge seed blocks with discovered blocks, preferring seed info on conflicts. -/
def mergeBlocks (preferred discovered : Array ThmBlock) : Array ThmBlock :=
  Id.run do
    let mut seen : Std.HashMap Name ThmBlock := {}
    for b in preferred do
      seen := seen.insert b.id.name b
    for b in discovered do
      if !seen.contains b.id.name then
        seen := seen.insert b.id.name b
    return seen.fold (init := #[]) (fun acc _ v => acc.push v)
private def seedBlocks : Array ThmBlock :=
  #[
    mkBlock `HeytingLean.LambdaIR.Add1EndToEnd.add1_end_to_end
      "EndToEndNatSpec for add1" kindComputational,
    mkBlock `HeytingLean.LambdaIR.DoubleEndToEnd.double_end_to_end
      "EndToEndNatSpec for double" kindComputational,
    mkBlock `HeytingLean.LambdaIR.ClampEndToEnd.clamp01_end_to_end
      "EndToEndNatSpec for clamp01" kindComputational,
    mkBlock `HeytingLean.LambdaIR.SuccTwiceEndToEnd.succTwice_end_to_end
      "EndToEndNatSpec for succ_twice" kindComputational,
    mkBlock `HeytingLean.LambdaIR.Max01EndToEnd.max01_end_to_end
      "EndToEndNatSpec for max01" kindComputational,
    mkBlock `HeytingLean.LambdaIR.Add2EndToEnd.add2_end_to_end
      "EndToEndNat2Spec for add2" kindComputational,
    mkBlock `HeytingLean.LambdaIR.Max2EndToEnd.max2_end_to_end
      "EndToEndNat2Spec for max2" kindComputational,
    mkBlock `HeytingLean.LambdaIR.Min2EndToEnd.min2_end_to_end
      "EndToEndNat2Spec for min2" kindComputational,
    mkBlock `HeytingLean.LambdaIR.RealFunEndToEnd.xorSum_end_to_end
      "EndToEndNat2Spec for xorSum" kindComputational,
    mkBlock `HeytingLean.LoF.NatFunProps.add1_compiled_spec
      "LoF property: add1 compiled spec" kindProperty,
    mkBlock `HeytingLean.LoF.NatFunProps.add2_compiled_spec
      "LoF property: add2 compiled spec" kindProperty,
    mkBlock `HeytingLean.LoF.NatFunProps.clamp01_compiled_boolish
      "LoF property: clamp01 boolish" kindProperty,
    mkBlock `HeytingLean.LoF.NatFunProps.double_compiled_spec
      "LoF property: double compiled spec" kindProperty,
    mkBlock `HeytingLean.LoF.NatFunProps.max01_compiled_spec
      "LoF property: max01 compiled spec" kindProperty,
    mkBlock `HeytingLean.LoF.NatFunProps.max2_compiled_select
      "LoF property: max2 select" kindProperty,
    mkBlock `HeytingLean.LoF.NatFunProps.min2_compiled_select
      "LoF property: min2 select" kindProperty,
    mkBlock `HeytingLean.LoF.NatFunProps.succTwice_compiled_spec
      "LoF property: succTwice compiled spec" kindProperty,
    mkBlock `HeytingLean.LoF.NatFunProps.xorSum_compiled_spec
      "LoF property: xorSum compiled spec" kindProperty
  ]

/-- Seed theorem blocks (always available even if discovery fails). -/
def seedThmBlocks : Array ThmBlock := seedBlocks

/-- All registered theorem blocks (seed view; prefer IO for full discovery). -/
def allThmBlocks : Array ThmBlock := seedBlocks

/-- IO wrapper that merges seeds with discovered blocks. -/
def allThmBlocksIO : IO (Array ThmBlock) := do
  let discovered ← discoverBlocksIO
  pure (mergeBlocks seedBlocks discovered)

/-- Find a theorem block by declaration name. -/
def findThmByName (n : Name) : Option ThmBlock :=
  allThmBlocks.find? (·.id.name == n)

end Theorems
end HeytingLean
