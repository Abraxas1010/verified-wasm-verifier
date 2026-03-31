import Lean
import Lean.Data.Json
import Std
import HeytingLean.CLI.Args

open Lean Std System

/-
# TheoremDiagramExport CLI

A small CLI that emits a JSON description of a canonical per-constant diagram,
backed by the compiled `HeytingLean` library.  This is intended as the first
step of the Phase 4.5 backend: it is a standalone, testable binary that can be
called by dashboards or other tools without depending on any in-process
interpreter state.

For now, the diagram is intentionally simple:

* a single node labelled by the constant name;
* the (pretty-printed) Lean type of the constant;
* mode tags that indicate which visual calculus family is being requested.

Future extensions refine the `nodes`/`edges` field to reflect more of the
type and proof structure; we already provide a basic Π/arrow‑shaped view so
that input/output structure is visible to visual frontends.
-/

namespace HeytingLean.CLI.TheoremDiagramExport

/-- A minimal node descriptor for JSON export. -/
structure Node where
  id   : Nat
  name : String

/-- A minimal edge descriptor for JSON export. -/
structure Edge where
  id    : Nat
  kind  : String
  src   : Nat
  tgt   : Nat
  label : String

def nodeToJson (n : Node) : Json :=
  Json.mkObj
    [ ("id",   Json.num n.id)
    , ("name", Json.str n.name)
    ]

def edgeToJson (e : Edge) : Json :=
  Json.mkObj
    [ ("id",    Json.num e.id)
    , ("kind",  Json.str e.kind)
    , ("src",   Json.num e.src)
    , ("tgt",   Json.num e.tgt)
    , ("label", Json.str e.label)
    ]

/-- Parse a dotted constant string like `"HeytingLean.Foo.bar"` into a Lean
`Name`. -/
private def nameOfString (s : String) : Name :=
  s.splitOn "." |>.foldl (fun n part => Name.str n part) Name.anonymous

/-- Initialise a Lean environment with the `HeytingLean` module imported. -/
private def initEnv : IO Environment := do
  let sys ← Lean.findSysroot
  Lean.initSearchPath sys
  let cwd ← IO.currentDir
  -- Prefer the local project build tree if present.
  let localLib : System.FilePath :=
    cwd / ".." / "lean" / ".lake" / "build" / "lib" / "lean"
  let cur : Lean.SearchPath := (← Lean.searchPathRef.get)
  let mut sp := cur
  if ← localLib.pathExists then
    sp := sp ++ [localLib]
  -- Add common package libs if available (mirrors `LeanFacts`).
  let basePkgs :=
    #["mathlib","batteries","proofwidgets","Qq","aesop","importGraph","LeanSearchClient","plausible","Cli"]
  for nm in basePkgs do
    let lib :=
      cwd / ".." / "lean" / ".lake" / "packages" / nm / ".lake" / "build" / "lib" / "lean"
    if ← lib.pathExists then
      sp := sp ++ [lib]
  Lean.searchPathRef.set sp
  importModules #[{module := `Init}, {module := `HeytingLean}] {}

/-- Collect a (possibly dependent) Π‑tower `∀ x₁ : A₁, …, ∀ xₙ : Aₙ, B` as a
list of binders together with the residual codomain. Fuel protects against
pathological terms while keeping the function total. -/
private partial def collectBinders (e : Expr) (fuel : Nat := 128) :
    List (Name × Expr) × Expr :=
  if fuel = 0 then
    ([], e)
  else
    match e with
    | Expr.forallE n ty b _ =>
        let (bs, res) := collectBinders b (fuel - 1)
        ((n, ty) :: bs, res)
    | _ =>
        ([], e)

/-- Render a type expression to a compact string.  We deliberately use the
`toString` instance here to avoid pulling in the full pretty‑printing
machinery; frontends remain free to re‑label nodes as needed. -/
private def typeToString (ty : Expr) : String :=
  toString ty

/-- A lightweight Heyting-style region formula derived from the Π/arrow
structure of a type: we read a Π-tower `∀ x₁ : A₁, …, ∀ xₙ : Aₙ, B` as a
formula of the shape `(A₁ ∧ … ∧ Aₙ) ⇒ B`, where each `Aᵢ` is rendered
syntactically from its binder type.  This is not tied to a specific Ω_R
instance but provides a mathematically meaningful approximation that external
visual tools can interpret as a region diagram in a generic Heyting algebra.
-/
private def regionFormulaOfType (ty : Expr) : String :=
  let (binders, resTy) := collectBinders ty
  let atoms :=
    (binders.zip (List.range binders.length)).map fun
      | ((nm, aTy), idx) =>
        let base :=
          if nm == Name.anonymous then s!"x{idx}" else nm.toString
        s!"{base} : {typeToString aTy}"
  let lhs :=
    match atoms with
    | [] => "⊤"
    | a :: [] => a
    | a :: rest =>
        "(" ++ String.intercalate " ∧ " (a :: rest) ++ ")"
  s!"{lhs} ⇒ {typeToString resTy}"

/-- A minimal, language-agnostic AST for a Heyting-style region expression,
derived from the Π/arrow structure of a type.  This is intended solely for
export as JSON to visual tools; it does not depend on a particular Ω_R
instance. -/
inductive RegionAst where
  | top : RegionAst
  | atom (name typeStr : String) : RegionAst
  | inf (x y : RegionAst) : RegionAst
  | himp (x y : RegionAst) : RegionAst
  deriving Repr

private def regionAstToJson : RegionAst → Json
  | RegionAst.top =>
      Json.mkObj [("kind", Json.str "top")]
  | RegionAst.atom name ty =>
      Json.mkObj
        [ ("kind", Json.str "atom")
        , ("name", Json.str name)
        , ("type", Json.str ty)
        ]
  | RegionAst.inf x y =>
      Json.mkObj
        [ ("kind", Json.str "inf")
        , ("lhs", regionAstToJson x)
        , ("rhs", regionAstToJson y)
        ]
  | RegionAst.himp x y =>
      Json.mkObj
        [ ("kind", Json.str "himp")
        , ("lhs", regionAstToJson x)
        , ("rhs", regionAstToJson y)
        ]

/-- Build a RegionAst from the Π/arrow structure of a type: treat binders as
atoms in a left-associated meet, with the codomain as the Heyting implication
target. -/
private def regionAstOfType (ty : Expr) : RegionAst :=
  let (binders, resTy) := collectBinders ty
  let atoms :=
    (binders.zip (List.range binders.length)).map fun
      | ((nm, aTy), idx) =>
        let base :=
          if nm == Name.anonymous then s!"x{idx}" else nm.toString
        RegionAst.atom base (typeToString aTy)
  let lhs :=
    match atoms with
    | [] => RegionAst.top
    | a :: [] => a
    | a :: rest =>
        rest.foldl (fun acc b => RegionAst.inf acc b) a
  RegionAst.himp lhs (RegionAst.atom "_" (typeToString resTy))

/-- Given the constant name and its type, build a simple Π/arrow‑style diagram:

* node 0: the constant itself;
* node 1: the result type;
* nodes 2..: one node per binder `x : A` with label `"x : A"`;
* edges from each input node to the result node, labelled by the binder name.

This is generic over the theorem/def’s type and independent of any UI. -/
private def buildPiDiagram (constName : String) (ty : Expr) :
    Array Node × Array Edge :=
  let (binders, resTy) := collectBinders ty
  let resLabel := typeToString resTy
  let baseNodes : Array Node := #[⟨0, constName⟩, ⟨1, resLabel⟩]
  let baseEdges : Array Edge := #[⟨0, "omega-type-of", 0, 1, "type"⟩]
  let step
      (acc : Array Node × Array Edge × Nat)
      (b : Name × Expr) :
      Array Node × Array Edge × Nat :=
    let (nodes, edges, nextId) := acc
    let nm := b.fst
    let aTy := b.snd
    let id := nextId
    let nmStr :=
      if nm == Name.anonymous then s!"arg{nextId - 2}" else nm.toString
    let label := s!"{nmStr} : {typeToString aTy}"
    let nodes' := nodes.push ⟨id, label⟩
    let edges' := edges.push
      { id := edges.size
      , kind := "omega-input"
      , src := id
      , tgt := 1
      , label := nmStr
      }
    (nodes', edges', nextId + 1)
  let (nodes, edges, _) :=
    binders.foldl step (baseNodes, baseEdges, 2)
  (nodes, edges)

/-- Region view: treat binders as "assumptions" feeding a single conclusion
node representing the result type. -/
private def buildRegionDiagram (constName : String) (ty : Expr) :
    Array Node × Array Edge :=
  let (binders, resTy) := collectBinders ty
  let resLabel := typeToString resTy
  let baseNodes : Array Node := #[⟨0, constName⟩, ⟨1, resLabel⟩]
  let baseEdges : Array Edge := #[⟨0, "region-type-of", 0, 1, "type"⟩]
  let step
      (acc : Array Node × Array Edge × Nat)
      (b : Name × Expr) :
      Array Node × Array Edge × Nat :=
    let (nodes, edges, nextId) := acc
    let nm := b.fst
    let aTy := b.snd
    let id := nextId
    let nmStr :=
      if nm == Name.anonymous then s!"assumption{nextId - 2}" else nm.toString
    let label := s!"{nmStr} : {typeToString aTy}"
    let nodes' := nodes.push ⟨id, label⟩
    let edges' := edges.push
      { id := edges.size
      , kind := "region-assumption"
      , src := id
      , tgt := 1
      , label := nmStr
      }
    (nodes', edges', nextId + 1)
  let (nodes, edges, _) :=
    binders.foldl step (baseNodes, baseEdges, 2)
  (nodes, edges)

/-- Graph view: arrange binders in a simple flow from the constant through
the inputs to the result type. -/
private def buildGraphDiagram (constName : String) (ty : Expr) :
    Array Node × Array Edge :=
  let (binders, resTy) := collectBinders ty
  let resLabel := typeToString resTy
  let baseNodes : Array Node := #[⟨0, constName⟩, ⟨1, resLabel⟩]
  let baseEdges : Array Edge := #[⟨0, "graph-type-of", 0, 1, "type"⟩]
  let step
      (acc : Array Node × Array Edge × Nat × Option Nat)
      (b : Name × Expr) :
      Array Node × Array Edge × Nat × Option Nat :=
    let (nodes, edges, nextId, prevOpt) := acc
    let nm := b.fst
    let aTy := b.snd
    let id := nextId
    let nmStr :=
      if nm == Name.anonymous then s!"stage{nextId - 2}" else nm.toString
    let label := s!"{nmStr} : {typeToString aTy}"
    let nodes' := nodes.push ⟨id, label⟩
    let mkEdge (src tgt : Nat) (k lbl : String) : Edge :=
      { id := edges.size, kind := k, src, tgt, label := lbl }
    let edges' :=
      match prevOpt with
      | none =>
          edges.push (mkEdge 0 id "graph-flow" "start")
      | some p =>
          edges.push (mkEdge p id "graph-flow" "step")
    (nodes', edges', nextId + 1, some id)
  let (nodes, edges, _, lastOpt) :=
    binders.foldl step (baseNodes, baseEdges, 2, none)
  let mkEdge (src tgt : Nat) (k lbl : String) : Edge :=
    { id := edges.size, kind := k, src, tgt, label := lbl }
  let edges' :=
    match lastOpt with
    | none => edges.push (mkEdge 0 1 "graph-flow" "flow")
    | some last => edges.push (mkEdge last 1 "graph-flow" "result")
  (nodes, edges')

/-- Clifford view: treat binders as a sequence of "stages" acting on a
state, represented as a path from the constant through each stage to the
result type. -/
private def buildCliffordDiagram (constName : String) (ty : Expr) :
    Array Node × Array Edge :=
  let (binders, resTy) := collectBinders ty
  let resLabel := typeToString resTy
  let baseNodes : Array Node := #[⟨0, constName⟩, ⟨1, resLabel⟩]
  let baseEdges : Array Edge := #[⟨0, "clifford-type-of", 0, 1, "type"⟩]
  let step
      (acc : Array Node × Array Edge × Nat × Option Nat)
      (b : Name × Expr) :
      Array Node × Array Edge × Nat × Option Nat :=
    let (nodes, edges, nextId, prevOpt) := acc
    let nm := b.fst
    let aTy := b.snd
    let id := nextId
    let nmStr :=
      if nm == Name.anonymous then s!"stage{nextId - 2}" else nm.toString
    let label := s!"{nmStr} : {typeToString aTy}"
    let nodes' := nodes.push ⟨id, label⟩
    let mkEdge (src tgt : Nat) (k lbl : String) : Edge :=
      { id := edges.size, kind := k, src, tgt, label := lbl }
    let edges' :=
      match prevOpt with
      | none =>
          edges.push (mkEdge 0 id "clifford-stage" "project")
      | some p =>
          edges.push (mkEdge p id "clifford-stage" "stage")
    (nodes', edges', nextId + 1, some id)
  let (nodes, edges, _, lastOpt) :=
    binders.foldl step (baseNodes, baseEdges, 2, none)
  let mkEdge (src tgt : Nat) (k lbl : String) : Edge :=
    { id := edges.size, kind := k, src, tgt, label := lbl }
  let edges' :=
    match lastOpt with
    | none => edges.push (mkEdge 0 1 "clifford-flow" "flow")
    | some last => edges.push (mkEdge last 1 "clifford-stage" "result")
  (nodes, edges')

/-- Build a simple per-constant diagram JSON object for a given constant name
and visual calculus mode.  If the constant cannot be found, the JSON records
`"status": "not-found"` and emits empty node/edge arrays.
-/
def theoremDiagramJson (constName mode : String) : IO Json := do
  let env ← initEnv
  let n := nameOfString constName
  match env.constants.find? n with
  | none =>
      pure <|
        Json.mkObj
          [ ("kind",   Json.str "theorem-diagram")
          , ("const",  Json.str constName)
          , ("mode",   Json.str mode)
          , ("status", Json.str "not-found")
          , ("nodes",  Json.arr #[])
          , ("edges",  Json.arr #[])
          ]
  | some ci =>
      let regionFormula := regionFormulaOfType ci.type
      let (binders, _) := collectBinders ci.type
      let binderCount := binders.length
      let pathIds : List Nat :=
        let binderIds := (List.range binderCount).map fun i => (i + 2)
        0 :: (binderIds ++ [1])
      let graphFlowJson : Json :=
        Json.arr <| (pathIds.map (fun i => Json.num (Int.ofNat i))).toArray
      let stageNames :=
        (binders.zip (List.range binderCount)).map fun
          | ((nm, _), idx) =>
            if nm == Name.anonymous then s!"stage{idx}" else nm.toString
      let cliffordStagesJson : Json :=
        Json.arr <| (stageNames.map Json.str).toArray
      let (nodes, edges) :=
        match mode with
        | "region" => buildRegionDiagram constName ci.type
        | "graph" => buildGraphDiagram constName ci.type
        | "clifford" => buildCliffordDiagram constName ci.type
        | _ => buildPiDiagram constName ci.type
      let explain :=
        match mode with
        | "region" =>
            s!"Region view: treat binders as assumptions and show {regionFormula} as a Heyting-style implication."
        | "graph" =>
            s!"Graph view: show binders as stages in a flow from {constName} to the result type."
        | "clifford" =>
            s!"Clifford view: interpret binders as a stage pipeline (project/stage/result) over the theorem state."
        | "omega" =>
            s!"Ω/string view: show the Π-tower of arguments for {constName} as inputs to its result type."
        | _ =>
            s!"View {mode}: structural diagram derived from the Π-tower of {constName}."
      pure <|
        Json.mkObj
          [ ("kind",          Json.str "theorem-diagram")
          , ("const",         Json.str constName)
          , ("mode",          Json.str mode)
          , ("status",        Json.str "ok")
          , ("type",          Json.str (typeToString ci.type))
          , ("explain",       Json.str explain)
          , ("regionFormula", Json.str regionFormula)
          , ("regionAst",     regionAstToJson (regionAstOfType ci.type))
          , ("graphFlow",     graphFlowJson)
          , ("cliffordStages", cliffordStagesJson)
          , ("nodes",         Json.arr <| nodes.map nodeToJson)
          , ("edges",         Json.arr <| edges.map edgeToJson)
          ]

private def usage : String :=
  "theorem_diagram_export --const NAME [--mode MODE]\n" ++
  "  NAME : fully qualified constant name (e.g. HeytingLean.Numbers.Surreal.zero)\n" ++
  "  MODE : optional calculus tag (default: omega)"

/-- Parse CLI arguments into `(constName, mode)` if possible. -/
private def parseArgs : List String → Option (String × String)
  | "--const" :: name :: rest =>
      let rec findMode
        | [] => "omega"
        | "--mode" :: m :: _ => m
        | _ :: xs => findMode xs
      some (name, findMode rest)
  | _ => none

/-- Entrypoint: emit a simple per-constant diagram as JSON, backed by the
compiled `HeytingLean` environment. -/
def main (argv : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs argv
  match parseArgs args with
  | some (constName, mode) =>
      let j ← theoremDiagramJson constName mode
      IO.println (toString j)
      pure 0
  | none =>
      IO.eprintln usage
      pure 1

end HeytingLean.CLI.TheoremDiagramExport
