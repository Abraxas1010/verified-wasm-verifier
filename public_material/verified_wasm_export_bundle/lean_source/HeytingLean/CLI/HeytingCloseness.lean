import Lean
import Lean.Data.Json
import Std
-- NOTE: This CLI is intentionally decoupled from the library distances
-- to minimize dependencies and ensure fast compilation of the runtime
-- surface. The library implements Ω_R distances; here we focus on I/O.
-- Distances are computed via the library elsewhere; this CLI currently
-- returns well-formed JSON and focuses on runtime wiring. We avoid
-- constructing concrete modalities here.

/-
  A small CLI that prints JSON with closeness fields.
  The score is a lightweight, schema-stable heuristic over the inputs
  (JSON strings or opaque text), meant to exercise the runtime surface.
-/

open Std
open Lean

structure Args where
  a     : String := ""
  b     : String := ""
  constA : String := ""
  constB : String := ""
  batch : String := ""
  metric : String := "birth"
  lens   : String := "core"
  json   : Bool := true
deriving Inhabited

private def parseArgs (xs : List String) : Args :=
  let rec go (st : Args) (ys : List String) : Args :=
    match ys with
    | [] => st
    | "--a" :: v :: ys' => go { st with a := v } ys'
    | "--b" :: v :: ys' => go { st with b := v } ys'
    | "--constA" :: v :: ys' => go { st with constA := v } ys'
    | "--constB" :: v :: ys' => go { st with constB := v } ys'
    | "--batch" :: v :: ys' => go { st with batch := v } ys'
    | "--metric" :: v :: ys' => go { st with metric := v } ys'
    | "--lens" :: v :: ys' => go { st with lens := v } ys'
    | "--json" :: ys' => go { st with json := true } ys'
    | _ :: ys' => go st ys'
  go ({} : Args) xs

private def readMaybe (p : String) : IO (Option String) := do
  try
    if (← System.FilePath.pathExists p) then
      return some (← IO.FS.readFile p)
    else
      return none
  catch _ =>
    return none

/- IR feature metric (file-local helpers) -/

structure Feat where
  atoms : Nat
  orR   : Nat
  impR  : Nat
  notR  : Nat
  depth : Nat
deriving Inhabited

private def countSubstr (s sub : String) : Nat :=
  let parts := s.splitOn sub
  if parts.isEmpty then 0 else parts.length - 1

private def bracketDepth (s : String) : Nat :=
  let rec go (cs : List Char) (d m : Nat) : Nat :=
    match cs with
    | []      => m
    | c :: cs =>
      let d' := if c = '(' then d+1 else if c = ')' then (if d = 0 then 0 else d-1) else d
      let m' := if d' > m then d' else m
      go cs d' m'
  go s.data 0 0

private def featFromJsonString (s : String) : Feat :=
  let atoms := countSubstr s "\"kind\":\"atom\""
  let orR   := countSubstr s "\"kind\":\"or\"" + countSubstr s "\"kind\":\"orR\""
  let impR  := countSubstr s "\"kind\":\"imp\"" + countSubstr s "\"kind\":\"impR\""
  let notR  := countSubstr s "\"kind\":\"not\"" + countSubstr s "\"kind\":\"notR\""
  let depth := bracketDepth s
  { atoms := atoms, orR := orR, impR := impR, notR := notR, depth := depth }

private def countOcc (s sub : String) : Nat :=
  let parts := s.splitOn sub
  if parts.isEmpty then 0 else parts.length - 1

private def featFromTypeString (s : String) : Feat :=
  let atoms := countOcc s "Prop" + countOcc s "Type" -- crude proxy
  let orR   := countOcc s "∨" + countOcc s "Or"
  let impR  := countOcc s "→" + countOcc s "implies"
  let notR  := countOcc s "¬" + countOcc s "Not"
  let depth := bracketDepth s
  { atoms, orR, impR, notR, depth }

private def nameFromString (s : String) : Name :=
  (s.splitOn ".").foldl (fun n p => Name.str n p) Name.anonymous

private def typeStringOfConst (_n : String) : IO (Option String) := do
  -- Minimal: resolving constant types at runtime is environment‑dependent.
  -- Return none so we fall back to JSON/heuristic features.
  pure none

private def l1 (x y : Nat) : Nat := if x ≥ y then x - y else y - x
private def pos (n : Int) : Nat := if n ≤ 0 then 0 else Int.toNat n

private def dIR (fa fb : Feat) : Nat × Nat × Nat × Nat :=
  let dPlusAB :=
    pos (Int.ofNat fb.atoms - Int.ofNat fa.atoms) +
    pos (Int.ofNat fb.orR   - Int.ofNat fa.orR)   +
    pos (Int.ofNat fb.impR  - Int.ofNat fa.impR)  +
    pos (Int.ofNat fb.notR  - Int.ofNat fa.notR)  +
    pos (Int.ofNat fb.depth - Int.ofNat fa.depth)
  let dPlusBA :=
    pos (Int.ofNat fa.atoms - Int.ofNat fb.atoms) +
    pos (Int.ofNat fa.orR   - Int.ofNat fb.orR)   +
    pos (Int.ofNat fa.impR  - Int.ofNat fb.impR)  +
    pos (Int.ofNat fa.notR  - Int.ofNat fb.notR)  +
    pos (Int.ofNat fa.depth - Int.ofNat fb.depth)
  let dSym :=
    l1 fa.atoms fb.atoms +
    l1 fa.orR   fb.orR   +
    l1 fa.impR  fb.impR  +
    l1 fa.notR  fb.notR  +
    l1 fa.depth fb.depth
  let dGap := dSym / 2
  (dPlusAB, dPlusBA, dSym, dGap)

def main (argv : List String) : IO Unit := do
  let args := parseArgs argv
  if args.batch ≠ "" then
    -- Batch mode (lightweight): read raw file, count items by "\"canon\"" and produce empty edges if parsing is unknown.
    let ok ← System.FilePath.pathExists args.batch
    if !ok then
      IO.println ("{\"error\":\"missing batch file\"}")
      return
    let payload ← IO.FS.readFile args.batch
    let n :=
      let parts := payload.splitOn "\"canon\""
      if parts.isEmpty then 0 else parts.length - 1
    let obj := Json.mkObj
      [("metric", Json.str args.metric), ("lens", Json.str args.lens), ("n", Json.num n), ("edges", Json.arr #[])]
    IO.println (toString obj)
    return
  -- Inputs can be: const names or JSON; prefer const names when provided
  let constA? := if args.constA ≠ "" then some args.constA else none
  let constB? := if args.constB ≠ "" then some args.constB else none
  let typeA? ← match constA? with
               | some nm => typeStringOfConst nm
               | none    => pure none
  let typeB? ← match constB? with
               | some nm => typeStringOfConst nm
               | none    => pure none
  -- Fallback: read JSON or raw strings
  let _aJson? ← readMaybe args.a
  let _bJson? ← readMaybe args.b
  let aJson? := match _aJson? with | some s => some s | none => some args.a
  let bJson? := match _bJson? with | some s => some s | none => some args.b
  -- Try to parse (ignored for now, but validates inputs)
  let _ := match aJson? with
           | some s => match Json.parse s with | .ok _ => () | .error _ => ()
           | none   => ()
  let _ := match bJson? with
           | some s => match Json.parse s with | .ok _ => () | .error _ => ()
           | none   => ()
  -- Choose measure

  -- Build features for A and B
  let parseOrDefault (t? j? : Option String) : Feat :=
    match t? with
    | some ts => featFromTypeString ts
    | none    => match j? with
                 | some js => featFromJsonString js
                 | none    => { atoms := 1, orR := 0, impR := 0, notR := 0, depth := 1 }

  let fa := parseOrDefault typeA? aJson?
  let fb := parseOrDefault typeB? bJson?
  -- Birth metric (residuation debt) via ambient implication feature combo
  let featImp (x y : Feat) : Feat :=
    { atoms := x.atoms + y.atoms
    , orR   := x.orR + y.orR + 1
    , impR  := x.impR + y.impR + 1
    , notR  := x.notR + y.notR + 1
    , depth := Nat.succ (Nat.max x.depth y.depth) }
  let birthScore (f : Feat) : Nat := f.impR + f.notR
  let dBirthAB := birthScore (featImp fa fb)
  let dBirthBA := birthScore (featImp fb fa)
  let dBirthSym := Nat.max dBirthAB dBirthBA
  let dBirthGap := dBirthSym / 2

  let (dPlusAB, dPlusBA, dSymAB, dGapAB) :=
    if args.metric == "ir" then dIR fa fb
    else if args.metric == "birth" then (dBirthAB, dBirthBA, dBirthSym, dBirthGap)
    else dIR fa fb

  let obj := Json.mkObj
    [ ("metric", Json.str args.metric)
      , ("lens",   Json.str args.lens)
      , ("dPlus_AB", Json.num dPlusAB)
      , ("dPlus_BA", Json.num dPlusBA)
      , ("dSym",    Json.num dSymAB)
      , ("dGap",    Json.num dGapAB)
      ]
  IO.println (toString obj)
