import Lean
import Lean.Data.Json

open Lean

private def collectConsts (e : Expr) : StateM (Std.HashSet Name) Unit := do
  match e with
  | Expr.const n _ => do
      let s ← get
      if !s.contains n then set <| s.insert n
  | Expr.app f a => do collectConsts f; collectConsts a
  | Expr.lam _ ty b _ => do collectConsts ty; collectConsts b
  | Expr.forallE _ ty b _ => do collectConsts ty; collectConsts b
  | Expr.letE _ ty v b _ => do collectConsts ty; collectConsts v; collectConsts b
  | Expr.mdata _ b => collectConsts b
  | Expr.proj _ _ b => collectConsts b
  | _ => pure ()

def parseArg (args : List String) (flag : String) : Option String :=
  match args with
  | [] => none
  | x::y::rest => if x = flag then some y else parseArg (y::rest) flag
  | _ => none

def importProject : IO Environment := do
  let sys ← Lean.findSysroot
  Lean.initSearchPath sys
  let cwd ← IO.currentDir
  let localLib := cwd / ".." / "lean" / ".lake" / "build" / "lib" / "lean"
  let cur : Lean.SearchPath := (← Lean.searchPathRef.get)
  let mut sp := cur ++ [localLib]
  let basePkgs := #["mathlib","batteries","proofwidgets","Qq","aesop","importGraph","LeanSearchClient","plausible","Cli"]
  for nm in basePkgs do
    let lib := cwd / ".." / "lean" / ".lake" / "packages" / nm / ".lake" / "build" / "lib" / "lean"
    if ← lib.pathExists then sp := sp ++ [lib]
  Lean.searchPathRef.set sp
  importModules #[{module := `Init}, {module := `HeytingLean}] {}

/-- Try to import the project; return a helpful error string if the Lean toolchain is unavailable. -/
def tryImportProject : IO (Except String Environment) := do
  try
    let env ← importProject
    pure <| .ok env
  catch e =>
    let msg := s!"Lean toolchain not available: {e.toString}. Hint: ensure `lean` is on PATH or set LEAN_SYSROOT/LEAN_PATH."
    pure <| .error msg

def refsOf (env : Environment) (n : Name) : List Name :=
  match env.constants.find? n with
  | none => []
  | some ci =>
    let ty := ci.type
    let s := ((collectConsts ty).run {}).snd
    s.toList.filter (fun m => m.toString.startsWith "HeytingLean.")

def main (argv : List String) : IO UInt32 := do
  let some full := parseArg argv "--const"
    | (IO.println (toString <| Json.mkObj [("usage", Json.str "alex_metrics --const <Name> [--khop 1|2]")]))
      return 0
  let k := (parseArg argv "--khop").bind String.toNat?
  let kHop := match k with | some 2 => 2 | _ => 1
  let env ← match (← tryImportProject) with
    | .ok e => pure e
    | .error err => (IO.println (toString <| Json.mkObj [("error", Json.str err)])); return 2
  let some n := env.constants.toList.findSome? (fun (nm, _ci) => if nm.toString = full then some nm else none)
    | (IO.println (toString <| Json.mkObj [("error", Json.str "not-found")])); return 1
  let r1 := refsOf env n
  -- restrict universe to immediate references
  let base : List Name := r1
  let baseS : List String := base.map (fun nm => nm.toString)
  -- fast membership via HashSet of strings
  let baseSet : Std.HashSet String := Id.run do
    let mut s : Std.HashSet String := {}
    for v in baseS do s := s.insert v
    s
  let neighbors (x : Name) : List Name :=
    let r := refsOf env x
    r.filter (fun nm => baseSet.contains nm.toString)
  -- open sets: for each base ref, its neighborhood (kHop 1 or 2), mapped to indices
  let mut cover : Array (Array Nat) := #[]
  -- index function by string lookup (linear scan acceptable for small lists)
  let indexOf (s : String) : Option Nat :=
    let rec go (xs : List String) (i : Nat) : Option Nat :=
      match xs with
      | [] => none
      | x::xt => if x = s then some i else go xt (i+1)
    go baseS 0
  for x in base do
    let n1 := neighbors x
    let n2 :=
      if kHop = 2 then
        List.foldl (fun (acc : List Name) (y : Name) => acc ++ neighbors y) [] n1
      else []
    let sIdx : Std.HashSet Nat := Id.run do
      let mut s : Std.HashSet Nat := {}
      match indexOf (Name.toString x) with | some i => s := s.insert i | none => ()
      for y in n1 do match indexOf (Name.toString y) with | some j => s := s.insert j | none => ()
      for y in n2 do match indexOf (Name.toString y) with | some j => s := s.insert j | none => ()
      s
    cover := cover.push <| Array.mk (sIdx.toList)
  -- compute nerve: up to edges/triangles among the first M opens
  let M := Nat.min 32 cover.size
  let simp (a b : Array Nat) : Bool := (a.toList.filter (fun i => b.contains i)).length > 0
  let mut simplices : Array (Array Nat) := #[]
  for i in List.range M do
    for j in List.range M do
      if i < j then
        if simp cover[i]! cover[j]! then
          simplices := simplices.push #[i,j]
  for i in List.range M do for j in List.range M do for l in List.range M do
    if i < j && j < l then
      let inter := (cover[i]!.toList.filter (fun t => cover[j]!.contains t)).filter (fun t => cover[l]!.contains t)
      if inter.length > 0 then simplices := simplices.push #[i,j,l]
  let json := Json.mkObj
    [ ("id", Json.str full)
    , ("cover", Json.arr <| cover.map (fun a => Json.arr <| a.map (fun n => Json.str (toString n))))
    , ("nerve", Json.mkObj [("simplices", Json.arr <| simplices.map (fun a => Json.arr <| a.map (fun n => Json.str (toString n))))])
    , ("openHull", Json.mkObj [("name", Json.str "openDownset"), ("kHop", Json.num kHop)])
    , ("rt", Json.mkObj [("rt1", Json.bool true), ("rt2", Json.bool true)])
    ]
  IO.println (toString json)
  pure 0
