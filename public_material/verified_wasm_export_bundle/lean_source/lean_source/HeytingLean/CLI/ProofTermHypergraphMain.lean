import Lean
import Lean.Data.Json
import HeytingLean.CLI.Args

open Lean
open System

namespace HeytingLean
namespace CLI

namespace ProofTermHypergraph

structure Args where
  constName : Option String := none
  exprKind : String := "value" -- "value" | "type"
  extraModules : List String := []
  fuel : Nat := 4096
  outDir : FilePath := FilePath.mk ".tmp" / "proof_term_hypergraph"
  runViz : Bool := false
  runWitness : Bool := false
deriving Inhabited

private def parseArg (xs : List String) (flag : String) : Option String :=
  match xs with
  | [] => none
  | x :: y :: rest => if x == flag then some y else parseArg (y :: rest) flag
  | _ => none

private def parseArgsMany (args : List String) (flag : String) : List String :=
  match args with
  | [] => []
  | x :: y :: rest =>
      if x = flag then
        y :: parseArgsMany rest flag
      else
        parseArgsMany (y :: rest) flag
  | _ => []

private def parseArgs (argv : List String) : Args :=
  let constName := parseArg argv "--const"
  let exprKind := (parseArg argv "--expr").getD "value"
  let extraModules := parseArgsMany argv "--module"
  let fuel := (parseArg argv "--fuel").bind (·.toNat?) |>.getD 4096
  let outDir := (parseArg argv "--out").map FilePath.mk |>.getD (FilePath.mk ".tmp" / "proof_term_hypergraph")
  let runViz := argv.any (· == "--viz")
  let runWitness := argv.any (· == "--witness")
  { constName, exprKind, extraModules, fuel, outDir, runViz, runWitness }

private def usage : String :=
  String.intercalate "\n"
    [ "proof_term_hypergraph"
    , ""
    , "Export a Lean proof term (or type) as a Wolfram-Physics-style hypergraph:"
    , "  each hyperedge is (premises → conclusion) = (children ++ [parent])."
    , ""
    , "Usage:"
    , "  lake exe proof_term_hypergraph -- --const HeytingLean.LoF.Foundation.Soundness.soundness --expr value"
    , ""
    , "Options:"
    , "  --const <Name>     constant to inspect (required)"
    , "  --module <M>       extra module(s) to import (repeatable)"
    , "  --expr value|type  export the constant's proof term (value) or its type (default: value)"
    , "  --fuel <n>         recursion fuel (default: 4096)"
    , "  --out <dir>        output base directory (default: .tmp/proof_term_hypergraph; relative to repo root)"
    , "  --viz              run wolframscript to export Wolfram-style plots"
    , "  --witness          run wolframscript to generate a structural witness and verify it in Lean"
    ]

private def slug (s : String) : String :=
  s.foldl (fun acc c => if c.isAlphanum then acc.push c else acc.push '_') ""

private def nameOfDotted (s : String) : Name :=
  s.splitOn "." |>.foldl (fun n part => Name.str n part) Name.anonymous

private def importProject (extraModules : List String := []) : IO Environment := do
  let sys ← Lean.findSysroot
  Lean.initSearchPath sys
  let extras : Array Import := extraModules.toArray.map (fun s => { module := nameOfDotted s })
  importModules (#[{ module := `Init }, { module := `HeytingLean }] ++ extras) {}

private def findConst (env : Environment) (full : String) : Option Name :=
  env.constants.toList.findSome? (fun (n, _ci) => if n.toString = full then some n else none)

private def constantValueExpr? : ConstantInfo → Option Expr
  | ConstantInfo.thmInfo thm     => some thm.value
  | ConstantInfo.opaqueInfo info => some info.value
  | ConstantInfo.defnInfo info   => some info.value
  | _                            => none

structure Node where
  id : Nat
  kind : String
  depth : Nat
  label : String
deriving Inhabited, Repr

structure Edge where
  src : Nat
  dst : Nat
  label : String := ""
deriving Inhabited, Repr

structure GraphState where
  next : Nat := 0
  nodes : Array Node := #[]
  edges : Array Edge := #[]
deriving Inhabited

abbrev GM := StateM GraphState

private def nodeKind (e : Expr) : String :=
  match e with
  | .forallE .. => "forall"
  | .lam ..     => "lam"
  | .app ..     => "app"
  | .const ..   => "const"
  | .sort ..    => "sort"
  | .letE ..    => "let"
  | .mdata ..   => "mdata"
  | .proj ..    => "proj"
  | .lit _      => "lit"
  | .bvar _     => "bvar"
  | .fvar _     => "fvar"
  | .mvar _     => "mvar"

private def nodeLabel (e : Expr) : String :=
  match e with
  | .const n _ => n.toString
  | .sort u => s!"Sort {u}"
  | .forallE n _ _ _ => s!"∀ {n}"
  | .lam n _ _ _ => s!"λ {n}"
  | .proj n i _ => s!"proj {n}:{i}"
  | .lit (.natVal v) => s!"nat {v}"
  | .lit (.strVal v) => s!"str \"{v}\""
  | _ => ""

private def walkFuel (fuel : Nat) (e : Expr) (depth : Nat) : GM Nat := do
  match fuel with
  | 0 =>
      let id := (← get).next
      modify fun s =>
        { s with
          next := s.next + 1
          nodes := s.nodes.push { id, kind := "term", depth, label := "… (fuel exhausted)" } }
      return id
  | fuel + 1 =>
      let id := (← get).next
      modify fun s =>
        { s with
          next := s.next + 1
          nodes := s.nodes.push { id, kind := nodeKind e, depth, label := nodeLabel e } }
      let attach (child : Expr) (lbl : String := "") : GM Unit := do
        let cid ← walkFuel fuel child (depth + 1)
        modify fun s => { s with edges := s.edges.push { src := id, dst := cid, label := lbl } }
      match e with
      | .forallE _ ty b _ => do attach ty "ty"; attach b "body"
      | .lam _ ty b _     => do attach ty "ty"; attach b "body"
      | .app f a          => do attach f "f"; attach a "a"
      | .letE _ ty v b _  => do attach ty "ty"; attach v "val"; attach b "body"
      | .mdata _ b        => do attach b "m"
      | .proj _ _ b       => do attach b "struct"
      | _                 => pure ()
      return id

private def walk (e : Expr) (fuel : Nat) : GraphState :=
  let (_, st) := (walkFuel fuel e 0).run {}
  st

private def jNat (n : Nat) : Json :=
  Json.num (JsonNumber.fromNat n)

private def jsonOfNodes (nodes : Array Node) : Json :=
  Json.arr <| nodes.map (fun n =>
    Json.mkObj
      [ ("id", jNat n.id)
      , ("kind", Json.str n.kind)
      , ("depth", jNat n.depth)
      , ("label", Json.str n.label)
      ])

private def jsonOfEdges (edges : Array Edge) : Json :=
  Json.arr <| edges.map (fun e =>
    Json.mkObj
      [ ("src", jNat e.src)
      , ("dst", jNat e.dst)
      , ("label", Json.str e.label)
      ])

private def jsonOfHyperedges (hyper : Array (Array Nat)) : Json :=
  Json.arr <| hyper.map (fun e =>
    Json.arr (e.map (fun v => jNat v)))

private def u64BytesLE (u : UInt64) : Array UInt8 :=
  let rec go (k : Nat) (n : Nat) (acc : Array UInt8) : Array UInt8 :=
    match k with
    | 0 => acc
    | k + 1 =>
        let b : UInt8 := UInt8.ofNat (n % 256)
        go k (n / 256) (acc.push b)
  go 8 u.toNat #[]

private def encodeU64LEList (xs : List UInt64) : ByteArray :=
  let out : Array UInt8 := Id.run do
    let mut acc : Array UInt8 := #[]
    for x in xs do
      for b in u64BytesLE x do
        acc := acc.push b
    return acc
  ByteArray.mk out

private def flattenHyperedges (edges : Array (Array Nat)) : List Nat :=
  edges.foldl (fun acc e => acc ++ e.toList) []

private def hyperedgeLengths (edges : Array (Array Nat)) : List Nat :=
  edges.toList.map (fun e => e.size)

private def writeHypergraphBin (dataPath lengthsPath : FilePath) (edges : Array (Array Nat)) : IO Unit := do
  let lens := hyperedgeLengths edges |>.map (UInt64.ofNat ·)
  let flat := flattenHyperedges edges |>.map (UInt64.ofNat ·)
  IO.FS.writeBinFile lengthsPath (encodeU64LEList lens)
  IO.FS.writeBinFile dataPath (encodeU64LEList flat)

private def getD {α β} [BEq α] [Hashable α] (m : Std.HashMap α β) (k : α) (default : β) : β :=
  match m.get? k with
  | some v => v
  | none => default

private def groupChildren (edges : Array Edge) : Std.HashMap Nat (Array Nat × Array String) :=
  edges.foldl
    (fun acc e =>
      let (kids, labels) := getD acc e.src (#[], #[])
      acc.insert e.src (kids.push e.dst, labels.push e.label))
    {}

private def buildTermHyperedges (st : GraphState) : Array (Array Nat) × Array (Array String) :=
  Id.run do
    let childMap := groupChildren st.edges
    let keys : Array Nat :=
      (childMap.toList.map (fun (k, _) => k)).toArray |>.qsort (· < ·)
    let mut hyper : Array (Array Nat) := #[]
    let mut slotLabels : Array (Array String) := #[]
    for k in keys do
      let some (kids, labels) := childMap.get? k
        | continue
      if kids.isEmpty then
        continue
      hyper := hyper.push (kids.push k)
      slotLabels := slotLabels.push labels
    return (hyper, slotLabels)

private def dedupStrings (xs : Array String) : Array String :=
  let step := fun (st : Std.HashSet String × Array String) (s : String) =>
    let seen := st.fst; let out := st.snd
    if seen.contains s then st else (seen.insert s, out.push s)
  (xs.foldl step ((Std.HashSet.emptyWithCapacity : Std.HashSet String), (#[] : Array String))).snd

private def buildConstDependencyGraph (nodes : Array Node) (target : String) :
    (Array (Array Nat)) × (Array String) := Id.run do
  let mut raw : Array String := #[]
  for n in nodes do
    if n.kind == "const" && n.label != "" then
      raw := raw.push n.label
  let consts : Array String := (dedupStrings raw).qsort (· < ·)
  let mut names : Array String := #[target]
  for c in consts do
    if c != target then
      names := names.push c
  let mut idOf : Std.HashMap String Nat := Std.HashMap.emptyWithCapacity (max 8 (names.size * 2))
  for i in [0:names.size] do
    idOf := idOf.insert names[i]! i
  let tgtId := getD idOf target 0
  let mut edges : Array (Array Nat) := #[]
  for c in consts do
    let did := getD idOf c 0
    edges := edges.push #[did, tgtId]
  return (edges, names)

private partial def findRepoRoot (start : FilePath) (fuel : Nat := 6) : IO (Option FilePath) := do
  if fuel == 0 then
    return none
  let lakefile := start / "lakefile.lean"
  if (← lakefile.pathExists) then
    if start.fileName == some "lean" then
      match start.parent with
      | some p =>
          let parentLakefile := p / "lakefile.lean"
          if (← parentLakefile.pathExists) then
            return some p
          else
            return some start
      | none => return some start
    else
      return some start
  match start.parent with
  | none => return none
  | some p => findRepoRoot p (fuel - 1)

private def runWolframscript (args : Array String) (cwd : Option FilePath := none) :
    IO (Except String IO.Process.Output) := do
  try
    let out ← IO.Process.output { cmd := "wolframscript", args := args, cwd := cwd }
    return .ok out
  catch e =>
    return .error s!"failed to run wolframscript: {e}"

private def requireOk (label : String) (out : IO.Process.Output) : Except String Unit :=
  if out.exitCode == 0 then
    .ok ()
  else
    .error s!"{label} failed rc={out.exitCode} stderr={out.stderr.trim}"

private def parseJsonStdout (out : IO.Process.Output) : Except String Json :=
  let line := out.stdout.trim.splitOn "\n" |>.getLastD ""
  match Json.parse line with
  | .ok j => .ok j
  | .error e => .error s!"failed to parse wolframscript JSON: {e}\nstdout={line}"

private def jsonNumberToNat? (n : JsonNumber) : Option Nat :=
  n.toString.toNat?

private def jsonGetNat? (j : Json) (k : String) : Option Nat :=
  match j.getObjVal? k with
  | .ok (Json.num n) => jsonNumberToNat? n
  | _ => none

private def jsonGetBool? (j : Json) (k : String) : Option Bool :=
  match j.getObjVal? k with
  | .ok (.bool b) => some b
  | _ => none

private def jsonAsNat? (j : Json) : Option Nat :=
  match j with
  | Json.num n => jsonNumberToNat? n
  | _ => none

private def jsonAsNatList? (j : Json) : Option (List Nat) :=
  match j with
  | Json.arr a =>
      let xs := a.toList.map jsonAsNat?
      if xs.all Option.isSome then
        some (xs.map Option.get!)
      else
        none
  | _ => none

private def edgeKey (e : Array Nat) : String :=
  String.intercalate "," (e.toList.map toString)

private def verifyWitness (rootId : Nat) (hyper : Array (Array Nat)) (w : Json) : Except String Unit := do
  let ok := (jsonGetBool? w "ok").getD false
  if !ok then
    throw "witness json has ok=false"
  let wRoot := (jsonGetNat? w "derivedRoot").getD 0
  if wRoot != rootId then
    throw s!"witness derivedRoot mismatch (expected {rootId}, got {wRoot})"
  -- Structural check: ensure each step's premises precede its parent according to the emitted order.
  let order? :=
    match w.getObjVal? "order" with
    | .ok (.arr a) =>
        let ns := a.toList.map (fun j =>
          match j with
          | Json.num n => jsonNumberToNat? n
          | _ => none)
        if ns.all Option.isSome then
          some (ns.map Option.get!)
        else
          none
    | _ => none
  let order := order?.getD []
  if order.isEmpty then
    throw "witness json missing 'order' array"
  let pos : Std.HashMap Nat Nat :=
    Id.run do
      let mut m : Std.HashMap Nat Nat := {}
      for i in [0:order.length] do
        m := m.insert order[i]! i
      return m
  for e in hyper do
    if e.size < 2 then
      continue
    let parent := e.back!
    let premises := e.pop
    let some pPos := pos.get? parent
      | throw s!"witness order missing parent {parent}"
    for c in premises do
      let some cPos := pos.get? c
        | throw s!"witness order missing premise {c}"
      if cPos >= pPos then
        throw s!"witness order violates edge (premise {c} not before parent {parent})"

  -- Stronger check: validate the explicit step-by-step derivation.
  let edgeSet : Std.HashSet String :=
    hyper.foldl (init := (Std.HashSet.emptyWithCapacity : Std.HashSet String)) (fun acc e => acc.insert (edgeKey e))

  let stepsJson ←
    match w.getObjVal? "steps" with
    | .ok (Json.arr a) => pure a
    | _ => throw "witness json missing 'steps' array"

  let parents : Std.HashSet Nat :=
    hyper.foldl (init := (Std.HashSet.emptyWithCapacity : Std.HashSet Nat)) (fun acc e =>
      if 0 < e.size then acc.insert e.back! else acc)

  -- Compute leaves from the witness order: vertices not appearing as a parent.
  let mut known : Std.HashSet Nat := (Std.HashSet.emptyWithCapacity : Std.HashSet Nat)
  for v in order do
    if !parents.contains v then
      known := known.insert v
  for stepJ in stepsJson do
    let obj ←
      match stepJ.getObj? with
      | .ok o => pure o
      | .error _ => throw "witness step is not an object"
    let parent ←
      match obj.get? "parent" with
      | some j =>
          match jsonAsNat? j with
          | some n => pure n
          | none => throw "witness step parent is not Nat"
      | none => throw "witness step missing 'parent'"
    let premises :=
      match obj.get? "premises" with
      | some j => (jsonAsNatList? j).getD []
      | none => []
    let edge :=
      match obj.get? "edge" with
      | some j => (jsonAsNatList? j).getD []
      | none => premises ++ [parent]
    if edge != premises ++ [parent] then
      throw "witness step edge != premises ++ [parent]"
    if !edgeSet.contains (edgeKey edge.toArray) then
      throw "witness step edge not present in exported hypergraph"
    for p in premises do
      if !known.contains p then
        throw s!"witness step applied before premise known: {p}"
    known := known.insert parent

  if !known.contains rootId then
    throw "witness steps did not derive root"

  return ()

def main (args : List String) : IO UInt32 := do
  let argv := HeytingLean.CLI.stripLakeArgs args
  if argv.isEmpty || argv.any (· == "--help") then
    IO.println usage
    return 0

  let cfg := parseArgs argv
  let some full := cfg.constName
    | IO.eprintln "E: missing --const <Name>"
      return 2

  let cwd ← IO.currentDir
  let root ← (findRepoRoot cwd).map (·.getD cwd)
  let outBase := if cfg.outDir.isAbsolute then cfg.outDir else root / cfg.outDir

  let env ← importProject cfg.extraModules
  let some nm := findConst env full
    | IO.eprintln s!"E: constant not found in environment: {full}"
      return 2
  let some ci := env.constants.find? nm
    | IO.eprintln s!"E: constant info not found: {full}"
      return 2

  let expr? : Except String Expr :=
    match cfg.exprKind with
    | "type" => .ok ci.type
    | "value" =>
        match constantValueExpr? ci with
        | some v => .ok v
        | none => .error s!"constant has no value/proof term: {full}"
    | other => .error s!"invalid --expr {other} (expected value|type)"

  let expr ←
    match expr? with
    | .ok e => pure e
    | .error e =>
        IO.eprintln s!"E: {e}"
        return 2

  let st := walk expr cfg.fuel
  let rootId : Nat := match st.nodes[0]? with | some n => n.id | none => 0

  let slugName := slug full
  let outDir := outBase / slugName
  IO.FS.createDirAll outDir

  let (hyper, slotLabels) := buildTermHyperedges st
  let flatLen := flattenHyperedges hyper |>.length

  let termData := outDir / s!"{slugName}_{cfg.exprKind}_hypergraph.bin"
  let termLens := outDir / s!"{slugName}_{cfg.exprKind}_lengths.bin"
  let termMeta := outDir / s!"{slugName}_{cfg.exprKind}_metadata.json"
  let termGraphJson := outDir / s!"{slugName}_{cfg.exprKind}_graph.json"

  writeHypergraphBin termData termLens hyper

  let termMetaJ :=
    Json.mkObj
      [ ("schema", Json.str "HeytingLean/ProofTermHypergraph/v1")
      , ("model", Json.str s!"proof_{slugName}_{cfg.exprKind}")
      , ("constant", Json.str full)
      , ("exprKind", Json.str cfg.exprKind)
      , ("fuel", jNat cfg.fuel)
      , ("root", jNat rootId)
      , ("nodeCount", jNat st.nodes.size)
      , ("finalStateSize", jNat hyper.size)
      , ("vertexCount", jNat st.nodes.size)
      , ("totalDataLength", jNat flatLen)
      , ("nodes", jsonOfNodes st.nodes)
      , ("hyperedgeSlots", Json.arr (slotLabels.map (fun xs => Json.arr (xs.map Json.str))))
      ]
  IO.FS.writeFile termMeta (Json.pretty termMetaJ)

  let graphJson :=
    Json.mkObj
      [ ("root", jNat rootId)
      , ("nodes", jsonOfNodes st.nodes)
      , ("edges", jsonOfEdges st.edges)
      , ("hyperedges", jsonOfHyperedges hyper)
      ]
  IO.FS.writeFile termGraphJson (Json.pretty graphJson)

  -- Export a collapsed constant-dependency graph (2-edges) as a second artifact.
  let (depEdges, depLabelArr) := buildConstDependencyGraph st.nodes full
  let depData := outDir / s!"{slugName}_constdeps_hypergraph.bin"
  let depLens := outDir / s!"{slugName}_constdeps_lengths.bin"
  let depMeta := outDir / s!"{slugName}_constdeps_metadata.json"
  writeHypergraphBin depData depLens depEdges
  let depLabels := Json.arr (depLabelArr.map Json.str)
  let depMetaJ :=
    Json.mkObj
      [ ("schema", Json.str "HeytingLean/ProofConstDeps/v1")
      , ("model", Json.str s!"constdeps_{slugName}")
      , ("constant", Json.str full)
      , ("finalStateSize", jNat depEdges.size)
      , ("vertexCount", jNat depLabelArr.size)
      , ("labels", depLabels)
      ]
  IO.FS.writeFile depMeta (Json.pretty depMetaJ)

  if cfg.runViz then
    let vizWls := root / "ffi" / "heyting_wolfram_bridge" / "proof_hypergraph_visualize.wls"
    if !(← vizWls.pathExists) then
      IO.eprintln s!"[viz] missing script: {vizWls}"
      return 2
    match (← runWolframscript #["-file", vizWls.toString, termData.toString, termLens.toString, termMeta.toString, outDir.toString] (cwd := some root)) with
    | .error e =>
        IO.eprintln s!"[viz] {e}"
        return 2
    | .ok out =>
        match requireOk "proof_hypergraph_visualize.wls" out with
        | .error e =>
            IO.eprintln s!"[viz] {e}"
            return 2
        | .ok _ =>
            IO.println s!"[viz] exported plots under: {outDir}"

  if cfg.runWitness then
    let wls := root / "ffi" / "heyting_wolfram_bridge" / "proof_hypergraph_witness.wls"
    if !(← wls.pathExists) then
      IO.eprintln s!"[witness] missing script: {wls}"
      return 2
    match (← runWolframscript #["-file", wls.toString, termData.toString, termLens.toString, toString rootId] (cwd := some root)) with
    | .error e =>
        IO.eprintln s!"[witness] {e}"
        return 2
    | .ok out =>
        match requireOk "proof_hypergraph_witness.wls" out with
        | .error e =>
            IO.eprintln s!"[witness] {e}"
            return 2
        | .ok _ =>
            match parseJsonStdout out with
            | .error e =>
                IO.eprintln s!"[witness] {e}"
                return 2
            | .ok j =>
                match verifyWitness rootId hyper j with
                | .error e =>
                    IO.eprintln s!"[witness] FAIL: {e}"
                    return 1
                | .ok _ =>
                    IO.println "[witness] OK (Wolfram witness verified by Lean)"

  IO.println s!"Wrote:"
  IO.println s!"  {termMeta}"
  IO.println s!"  {termData}"
  IO.println s!"  {termLens}"
  IO.println s!"  {depMeta}"
  IO.println s!"  {depData}"
  IO.println s!"  {depLens}"
  return 0

end ProofTermHypergraph

end CLI
end HeytingLean

def main (argv : List String) : IO UInt32 :=
  HeytingLean.CLI.ProofTermHypergraph.main argv
