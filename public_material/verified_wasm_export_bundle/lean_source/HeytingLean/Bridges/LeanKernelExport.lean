import Lean
import Lean.Data.Json
import Std
import HeytingLean.Util.ModuleOwner

namespace HeytingLean.Bridges.LeanKernelExport

open Lean

/-!
Kernel-faithful Lean exporter (minimal v0):

- Imports one or more modules into a fresh environment (like `proof2vec_extract`).
- Exports selected declarations’ kernel `Expr` (type/value) as JSON, including universe levels.

This is intended as the Lean-side counterpart to the MetaRocq-based Coq kernel export.
-/

structure CliArgs where
  outPath : System.FilePath := "lean_kernel_export.json"
  modules : Array Name := #[]
  moduleFile : Option System.FilePath := none
  modulePrefixes : Array String := #[]
  namePrefixes : Array String := #[]
  maxDecls : Option Nat := none
  includeDefs : Bool := false
  includeDecls : Array Name := #[]
  closure : String := "transitive" -- "none" | "transitive"
  closureFuel : Nat := 20000
  deriving Inhabited

private def parseNat? (s : String) : Option Nat :=
  s.toNat?

private def parseModuleName (s : String) : Name :=
  (s.splitOn ".").foldl (fun acc part => acc.mkStr part) Name.anonymous

private def parseArgs (argv : List String) : Except String CliArgs := do
  let rec go (args : CliArgs) : List String → Except String CliArgs
    | [] => return args
    | "--" :: rest =>
      go args rest
    | "--out" :: p :: rest =>
      go { args with outPath := p } rest
    | "--module" :: m :: rest =>
      go { args with modules := args.modules.push (parseModuleName m) } rest
    | "--module-file" :: p :: rest =>
      go { args with moduleFile := some p } rest
    | "--module-prefix" :: p :: rest =>
      go { args with modulePrefixes := args.modulePrefixes.push p } rest
    | "--name-prefix" :: p :: rest =>
      go { args with namePrefixes := args.namePrefixes.push p } rest
    | "--max-decls" :: n :: rest =>
      match parseNat? n with
      | none => throw s!"invalid Nat for --max-decls: {n}"
      | some 0 => go { args with maxDecls := none } rest
      | some v => go { args with maxDecls := some v } rest
    | "--include-defs" :: rest =>
      go { args with includeDefs := true } rest
    | "--include" :: ns :: rest =>
      let parts := ns.splitOn ","
      let inc :=
        parts.foldl
          (fun acc p =>
            let s := p.trim
            if s.isEmpty then acc else acc.push (parseModuleName s))
          args.includeDecls
      go { args with includeDecls := inc } rest
    | "--closure" :: m :: rest => do
      if m != "none" && m != "transitive" then
        throw s!"invalid --closure mode: {m}"
      go { args with closure := m } rest
    | "--closure-fuel" :: n :: rest =>
      match parseNat? n with
      | none => throw s!"invalid Nat for --closure-fuel: {n}"
      | some v => go { args with closureFuel := v } rest
    | "--help" :: _ =>
      throw "help"
    | bad :: _ =>
      throw s!"unknown arg: {bad}"
  go {} argv

private def usage : String :=
  String.intercalate "\n"
    [ "lean_kernel_export --out <path> [--module <Module.Name> ...] [--module-file <path>]"
    , "                 [--module-prefix <prefix> ...] [--name-prefix <prefix> ...]"
    , "                 [--max-decls N] [--include-defs]"
    , "                 [--include <Decl.Name>[,<Decl.Name>...]] [--closure none|transitive] [--closure-fuel N]"
    , ""
    , "Notes:"
    , "- If neither --module nor --module-file is provided, export is a no-op and exits nonzero."
    , "- Prefer using --name-prefix when you want a small slice; exporting all of Init/Std can be huge."
    ]

partial def exprConstDeps : Expr → Std.HashSet Name
  | .const n _ => ((Std.HashSet.emptyWithCapacity 8).insert n)
  | .app f a =>
      let fds := exprConstDeps f
      let ads := exprConstDeps a
      Id.run do
        let mut out := fds
        for x in ads do
          out := out.insert x
        out
  | .lam _ ty body _ =>
      let tds := exprConstDeps ty
      let bds := exprConstDeps body
      Id.run do
        let mut out := tds
        for x in bds do
          out := out.insert x
        out
  | .forallE _ ty body _ =>
      let tds := exprConstDeps ty
      let bds := exprConstDeps body
      Id.run do
        let mut out := tds
        for x in bds do
          out := out.insert x
        out
  | .letE _ ty val body _ =>
      let tds := exprConstDeps ty
      let vds := exprConstDeps val
      let bds := exprConstDeps body
      Id.run do
        let mut out := tds
        for x in vds do
          out := out.insert x
        for x in bds do
          out := out.insert x
        out
  | .mdata _ e => exprConstDeps e
  | .proj _ _ e => exprConstDeps e
  | .bvar _ => Std.HashSet.emptyWithCapacity 0
  | .fvar _ => Std.HashSet.emptyWithCapacity 0
  | .mvar _ => Std.HashSet.emptyWithCapacity 0
  | .sort _ => Std.HashSet.emptyWithCapacity 0
  | .lit _ => Std.HashSet.emptyWithCapacity 0

private def constInfoDeps (ci : ConstantInfo) (includeDefs : Bool) : Std.HashSet Name :=
  Id.run do
    let mut deps := exprConstDeps ci.type
    match ci with
    | .thmInfo v =>
        for x in exprConstDeps v.value do
          deps := deps.insert x
    | .defnInfo v =>
        if includeDefs then
          for x in exprConstDeps v.value do
            deps := deps.insert x
    | .inductInfo v =>
        -- Ensure inductive closure includes constructors.
        for c in v.ctors do
          deps := deps.insert c
    | .ctorInfo v =>
        deps := deps.insert v.induct
    | .recInfo v =>
        deps := deps.insert v.getMajorInduct
    | _ => ()
    deps

private def computeClosure (env : Environment) (roots : Array Name) (includeDefs : Bool) (mode : String) (fuel : Nat) :
    Array Name := Id.run do
  if mode == "none" then
    return roots
  let mut seen : Std.HashSet Name := Std.HashSet.emptyWithCapacity (roots.size + 8)
  let mut todo : List Name := roots.toList
  let mut out : Array Name := #[]
  let mut remaining := fuel
  while remaining > 0 do
    remaining := remaining - 1
    match todo with
    | [] => break
    | n :: rest =>
        todo := rest
        if seen.contains n then
          continue
        seen := seen.insert n
        out := out.push n
        if let some ci := env.find? n then
          let deps := constInfoDeps ci includeDefs
          for d in deps do
            if !seen.contains d then
              todo := d :: todo
  out

private def setupSearchPath : IO Unit := do
  let sys ← Lean.findSysroot
  Lean.initSearchPath sys
  -- Mirror `HeytingLean.Embedding.CLI` so `lake exe` works from repo root.
  let cwd ← IO.currentDir
  let localLib : System.FilePath := cwd / ".." / "lean" / ".lake" / "build" / "lib" / "lean"
  let cur : Lean.SearchPath := (← Lean.searchPathRef.get)
  let mut sp := cur ++ [localLib]
  let basePkgs := #["mathlib","batteries","proofwidgets","Qq","aesop","importGraph","LeanSearchClient","plausible","Cli"]
  for nm in basePkgs do
    let lib := cwd / ".." / "lean" / ".lake" / "packages" / nm / ".lake" / "build" / "lib" / "lean"
    if ← lib.pathExists then
      sp := sp ++ [lib]
  let pkgsRoot := cwd / ".." / "lean" / ".lake" / "packages"
  if ← pkgsRoot.pathExists then
    for entry in (← pkgsRoot.readDir) do
      let lib := entry.path / ".lake" / "build" / "lib" / "lean"
      if ← lib.pathExists then
        sp := sp ++ [lib]
  Lean.searchPathRef.set sp

private def moduleFor (env : Environment) (n : Name) : Name :=
  HeytingLean.Util.moduleOwnerOf env n

private def matchesAnyPrefix (s : String) (prefixes : Array String) : Bool :=
  prefixes.isEmpty || prefixes.any (fun p => s.startsWith p)

private def keepConst (env : Environment) (n : Name) (opts : CliArgs) : Bool :=
  let nameStr := n.toString
  if !matchesAnyPrefix nameStr opts.namePrefixes then
    false
  else
    let modStr := (moduleFor env n).toString
    matchesAnyPrefix modStr opts.modulePrefixes

private def levelToJson : Level → Json
  | .zero => Json.mkObj [("tag", Json.str "zero")]
  | .succ u => Json.mkObj [("tag", Json.str "succ"), ("u", levelToJson u)]
  | .max u v => Json.mkObj [("tag", Json.str "max"), ("u", levelToJson u), ("v", levelToJson v)]
  | .imax u v => Json.mkObj [("tag", Json.str "imax"), ("u", levelToJson u), ("v", levelToJson v)]
  | .param n => Json.mkObj [("tag", Json.str "param"), ("name", Json.str n.toString)]
  | .mvar n => Json.mkObj [("tag", Json.str "mvar"), ("name", Json.str n.name.toString)]

private def binderInfoToString : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

private def literalToJson : Literal → Json
  | .natVal n => Json.mkObj [("tag", Json.str "nat"), ("value", Json.num n)]
  | .strVal s => Json.mkObj [("tag", Json.str "str"), ("value", Json.str s)]

partial def exprToJson : Expr → Json
  | .bvar i =>
      Json.mkObj [("tag", Json.str "bvar"), ("idx", Json.num i)]
  | .fvar id =>
      Json.mkObj [("tag", Json.str "fvar"), ("id", Json.str id.name.toString)]
  | .mvar id =>
      Json.mkObj [("tag", Json.str "mvar"), ("id", Json.str id.name.toString)]
  | .sort u =>
      Json.mkObj [("tag", Json.str "sort"), ("level", levelToJson u)]
  | .const n us =>
      Json.mkObj
        [ ("tag", Json.str "const")
        , ("name", Json.str n.toString)
        , ("levels", Json.arr (us.toArray.map levelToJson))
        ]
  | .app f a =>
      Json.mkObj [("tag", Json.str "app"), ("fn", exprToJson f), ("arg", exprToJson a)]
  | .lam n ty body bi =>
      Json.mkObj
        [ ("tag", Json.str "lam")
        , ("binder", Json.str n.toString)
        , ("binder_info", Json.str (binderInfoToString bi))
        , ("type", exprToJson ty)
        , ("body", exprToJson body)
        ]
  | .forallE n ty body bi =>
      Json.mkObj
        [ ("tag", Json.str "forallE")
        , ("binder", Json.str n.toString)
        , ("binder_info", Json.str (binderInfoToString bi))
        , ("type", exprToJson ty)
        , ("body", exprToJson body)
        ]
  | .letE n ty val body _ =>
      Json.mkObj
        [ ("tag", Json.str "letE")
        , ("binder", Json.str n.toString)
        , ("type", exprToJson ty)
        , ("value", exprToJson val)
        , ("body", exprToJson body)
        ]
  | .lit l =>
      Json.mkObj [("tag", Json.str "lit"), ("lit", literalToJson l)]
  | .mdata _ e =>
      Json.mkObj [("tag", Json.str "mdata"), ("expr", exprToJson e)]
  | .proj s i e =>
      Json.mkObj [("tag", Json.str "proj"), ("struct", Json.str s.toString), ("idx", Json.num i), ("expr", exprToJson e)]

private def constInfoToJson (env : Environment) (n : Name) (ci : ConstantInfo) (opts : CliArgs) (forceKeep : Bool := false) : IO (Option Json) := do
  if !forceKeep && !keepConst env n opts then
    return none
  let mod := moduleFor env n
  let (kind, declClass, type, value?, extra) : (String × String × Expr × Option Expr × Array (String × Json)) :=
    match ci with
    | .thmInfo thm => ("thm", "thm", thm.type, some thm.value, #[])
    | .defnInfo defn =>
        if opts.includeDefs then
          ("def", "def", defn.type, some defn.value, #[])
        else
          ("skip", "skip", defn.type, none, #[])
    | .opaqueInfo opaq =>
        if opts.includeDefs then
          ("opaque", "opaque", opaq.type, none, #[])
        else
          ("skip", "skip", opaq.type, none, #[])
    | .inductInfo ind =>
        let ctors := Json.arr ((ind.ctors.map (fun nm => Json.str nm.toString)).toArray)
        let extra : Array (String × Json) := #[
          ("inductive_val",
            Json.mkObj
              [ ("numParams", Json.num ind.numParams)
              , ("numIndices", Json.num ind.numIndices)
              , ("ctors", ctors)
              , ("isRec", Json.bool ind.isRec)
              , ("isUnsafe", Json.bool ind.isUnsafe)
              , ("numNested", Json.num ind.numNested)
              ])
        ]
        ("inductive", "inductive", ind.type, none, extra)
    | .ctorInfo ctor =>
        let extra : Array (String × Json) := #[
          ("constructor_val",
            Json.mkObj
              [ ("inductive", Json.str ctor.induct.toString)
              , ("cidx", Json.num ctor.cidx)
              , ("numParams", Json.num ctor.numParams)
              , ("numFields", Json.num ctor.numFields)
              ])
        ]
        ("constructor", "constructor", ctor.type, none, extra)
    | .recInfo r =>
        let extra : Array (String × Json) := #[
          ("recursor_val",
            Json.mkObj
              [ ("inductive", Json.str r.getMajorInduct.toString)
              , ("all", Json.arr ((r.all.map (fun nm => Json.str nm.toString)).toArray))
              , ("numParams", Json.num r.numParams)
              , ("numIndices", Json.num r.numIndices)
              , ("numMotives", Json.num r.numMotives)
              , ("numMinors", Json.num r.numMinors)
              , ("majorIdx", Json.num r.getMajorIdx)
              , ("firstMinorIdx", Json.num r.getFirstMinorIdx)
              , ("firstIndexIdx", Json.num r.getFirstIndexIdx)
              ])
        ]
        ("recursor", "recursor", r.type, none, extra)
    | _ => ("skip", "skip", (mkConst n), none, #[])
  if kind == "skip" then
    return none
  let base : Array (String × Json) := #[
    ("name", Json.str n.toString),
    ("module", Json.str mod.toString),
    ("decl_kind", Json.str kind),
    ("decl_class", Json.str declClass),
    ("type_expr", exprToJson type)
  ]
  let base := match value? with
    | none => base
    | some v => base.push ("value_expr", exprToJson v)
  let base := base ++ extra
  return some (Json.mkObj base.toList)

def main (argv : List String) : IO UInt32 := do
  let args ←
    match parseArgs argv with
    | .ok a => pure a
    | .error "help" =>
      IO.eprintln usage
      return 0
    | .error e =>
      IO.eprintln e
      IO.eprintln usage
      return 2
  setupSearchPath
  let mut modules := args.modules
  if let some mf := args.moduleFile then
    let lines ← IO.FS.lines mf
    for ln in lines do
      let s := ln.trim
      if s.isEmpty then
        continue
      if s.startsWith "#" then
        continue
      modules := modules.push (parseModuleName s)
  if modules.isEmpty then
    IO.eprintln "no --module or --module-file provided; nothing to import/export"
    IO.eprintln usage
    return 0

  let modsSorted := modules.qsort (fun a b => a.toString < b.toString)

  let _ ← IO.FS.withFile args.outPath .write fun h => do
    h.putStr "["
    let mut first := true
    let mut remaining : Option Nat := args.maxDecls

    if !args.includeDecls.isEmpty then
      -- Targeted export: compute closure from `--include` roots and emit only those decls.
      let env ← Lean.importModules (modsSorted.map (fun m => { module := m })) {}
      let roots := args.includeDecls
      let names := computeClosure env roots args.includeDefs args.closure args.closureFuel
      for n in names do
        if let some r := remaining then
          if r == 0 then
            break
        if let some ci := env.find? n then
          if let some j ← constInfoToJson env n ci args (forceKeep := true) then
            if first then
              pure ()
            else
              h.putStr ","
            h.putStr "\n"
            h.putStr (toString j)
            first := false
            remaining := remaining.map (fun r => r - 1)
    else
      -- Scan export: iterate over all environment constants, filtering by prefix/module.
      -- Like `proof2vec_extract`: avoid global collisions by importing each module in a fresh environment.
      for m in modsSorted do
        if let some r := remaining then
          if r == 0 then
            break
        let env ← Lean.importModules #[{ module := m }] {}
        let st0 : Bool × Option Nat × Nat := (first, remaining, 0)
        let st ←
          forIn env.constants st0 fun (n, ci) (stFirst, stRem, stCount) => do
            if let some r := stRem then
              if r == 0 then
                return ForInStep.done (stFirst, stRem, stCount)
            if let some j ← constInfoToJson env n ci args then
              if stFirst then
                pure ()
              else
                h.putStr ","
              h.putStr "\n"
              h.putStr (toString j)
              let stRem' := stRem.map (fun r => r - 1)
              return ForInStep.yield (false, stRem', stCount + 1)
            return ForInStep.yield (stFirst, stRem, stCount)
        first := st.1
        remaining := st.2.1

    if !first then
      h.putStr "\n"
    h.putStr "]\n"
  IO.println s!"Exported kernel expr JSON to {args.outPath}"
  return 0

end HeytingLean.Bridges.LeanKernelExport

def main (argv : List String) : IO UInt32 :=
  HeytingLean.Bridges.LeanKernelExport.main argv
