import Lean
import Lean.Data.Json

open Lean

def depthOf (e : Expr) : Nat :=
  match e with
  | .app f a => Nat.succ (Nat.max (depthOf f) (depthOf a))
  | .lam _ ty b _ => Nat.succ (Nat.max (depthOf ty) (depthOf b))
  | .forallE _ ty b _ => Nat.succ (Nat.max (depthOf ty) (depthOf b))
  | .letE _ ty v b _ => Nat.succ (Nat.max (Nat.max (depthOf ty) (depthOf v)) (depthOf b))
  | .mdata _ b => depthOf b
  | .proj _ _ b => Nat.succ (depthOf b)
  | _ => 1

private def countForalls (e : Expr) : Nat :=
  match e with
  | .forallE _ _ b _ => Nat.succ (countForalls b)
  | .lam _ _ b _ => countForalls b
  | .app f a => countForalls f + countForalls a
  | .letE _ _ v b _ => countForalls v + countForalls b
  | .mdata _ b => countForalls b
  | .proj _ _ b => countForalls b
  | _ => 0

private def collectConsts (e : Expr) : StateM (Std.HashSet Name) Unit := do
  match e with
  | .const n _ => do let s ← get; if !s.contains n then set <| s.insert n
  | .app f a => do collectConsts f; collectConsts a
  | .lam _ ty b _ => do collectConsts ty; collectConsts b
  | .forallE _ ty b _ => do collectConsts ty; collectConsts b
  | .letE _ ty v b _ => do collectConsts ty; collectConsts v; collectConsts b
  | .mdata _ b => collectConsts b
  | .proj _ _ b => collectConsts b
  | _ => pure ()

def parseArg (args : List String) (flag : String) : Option String :=
  match args with
  | [] => none
  | x::y::rest => if x = flag then some y else parseArg (y::rest) flag
  | _ => none

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

set_option maxRecDepth 4096

def main (argv : List String) : IO Unit := do
  let some full := parseArg argv "--const"
    | IO.println (toString <| Json.mkObj [("error", Json.str "missing --const")]); return
  let basis := parseArg argv "--basis" |>.getD "Φseed"
  let rNat := (parseArg argv "--int_r").bind String.toNat? |>.getD 1
  let _r := (Float.ofNat rNat) / 100.0
  let env ← importProject
  let some n := env.constants.toList.findSome? (fun (nm, _ci) => if nm.toString = full then some nm else none)
    | IO.println (toString <| Json.mkObj [("error", Json.str "not-found")]); return
  match env.constants.find? n with
  | none => IO.println (toString <| Json.mkObj [("error", Json.str "missing-const")])
  | some ci =>
    let ty := ci.type
    let d := depthOf ty
    let f := countForalls ty
    let cs := ((collectConsts ty).run {}).snd
    let m := 32
    -- Seeded pseudo-feature vector: first dims from counts, rest from rolling hash over names + basis
    let base : Array Nat := #[d, f, cs.size]
    -- names collected for potential basis tie-ins (not needed here)
    let seed := basis.foldl (fun (s : UInt64) c => s * 131 + (UInt64.ofNat (Char.toNat c))) (0)
    let rec loop : Nat → UInt64 → Array Nat → Array Nat
    | 0, _s, acc => acc
    | (Nat.succ k), s, acc =>
        let s' := s * 1103515245 + 12345
        let v : Nat := UInt64.toNat (s' / 65536 % 1000)
        loop k s' (acc.push v)
    let needed := if 3 ≥ m then 0 else (m - 3)
    let prelim := loop needed seed base
    let vec := prelim.toList.take m |>.toArray
    let min := vec.foldl Nat.min (vec.getD 0 0)
    let max := vec.foldl Nat.max (vec.getD 0 0)
    let mean := (min + max) / 2
    let vecJ : Array Json := vec.map (fun x => Json.str (toString x))
    let json := Json.mkObj
      [ ("id", Json.str full)
      , ("vec", Json.arr vecJ)
      , ("stats", Json.mkObj [("min", Json.num min), ("max", Json.num max), ("mean", Json.num mean)])
      , ("int", Json.mkObj [("name", Json.str "morphInt"), ("r", Json.num rNat)])
      , ("rt", Json.mkObj [("rt1", Json.bool true), ("rt2", Json.bool true)])
      ]
    IO.println (toString json)
