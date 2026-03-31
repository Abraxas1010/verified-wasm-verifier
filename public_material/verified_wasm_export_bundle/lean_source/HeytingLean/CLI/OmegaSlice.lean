import Lean
import Lean.Data.Json

open Lean

def parseArg (args : List String) (flag : String) : Option String :=
  match args with
  | [] => none
  | x::y::rest => if x = flag then some y else parseArg (y::rest) flag
  | _ => none

def countForalls (e : Expr) : Nat :=
  match e with
  | .forallE _ _ b _ => Nat.succ (countForalls b)
  | .lam _ _ b _     => countForalls b
  | .app f a         => countForalls f + countForalls a
  | .letE _ _ v b _  => countForalls v + countForalls b
  | .mdata _ b       => countForalls b
  | .proj _ _ b      => countForalls b
  | _                => 0

def importProject : IO Environment := do
  let sys ← Lean.findSysroot; Lean.initSearchPath sys
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

def readNames (p : System.FilePath) : IO (List String) := do
  let s ← IO.FS.readFile p
  match Json.parse s with
  | Except.ok (Json.arr a) =>
      let xs := a.foldl (fun acc x => match x with | Json.str t => t :: acc | _ => acc) []
      return xs.reverse
  | _ =>
      pure <| (s.split (fun c => c = '\n')).map (fun t => t) |>.filter (fun t => t ≠ "")

def main (argv : List String) : IO Unit := do
  let some fp := parseArg argv "--consts"
    | IO.println (toString <| Json.mkObj [("error", Json.str "missing --consts")]); return
  let names ← readNames fp
  let env ← importProject
  let ids := names.take 200
  let births ← ids.mapM (fun s => do
    let some n := env.constants.toList.findSome? (fun (nm, _ci) => if nm.toString = s then some nm else none)
      | pure 0
    match env.constants.find? n with
    | some ci => pure (countForalls ci.type % 4)
    | none    => pure 0
  )
  -- simple edges: connect each node i to i+1 if birth(i) ≤ birth(i+1)
  let rec edgesFrom : List Nat → Nat → Array (Nat × Nat) → Array (Nat × Nat)
  | (a::b::rest), i, acc =>
      let acc' := if a ≤ b then acc.push (i, i+1) else acc
      edgesFrom (b::rest) (i+1) acc'
  | _, _, acc => acc
  let edgesArr := edgesFrom births 0 (#[])
  let edgesJ := Json.arr <| edgesArr.map (fun p => Json.arr #[Json.num p.fst, Json.num p.snd])
  let nodesJ := Json.arr <| (List.zip ids births |>.map (fun (s,b) => Json.mkObj [("id", Json.str s), ("birth", Json.num b)])).toArray
  let json := Json.mkObj
    [ ("ids", Json.arr <| (ids.map Json.str).toArray)
    , ("nodes", nodesJ)
    , ("edges", edgesJ)
    , ("occam", Json.mkObj [("buckets", Json.arr #[Json.num 0, Json.num 1, Json.num 2, Json.num 3])])
    ]
  IO.println (toString json)
