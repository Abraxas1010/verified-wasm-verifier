import Lean
import HeytingLean.WPP.Causal
import HeytingLean.WPP.Examples.StringRules

open Lean
open HeytingLean.WPP
open HeytingLean.WPP.Examples

structure Args where
  rule      : String := "fib"
  start     : String := "A"
  maxDepth  : Nat := 4
  maxBreadth : Nat := 64
deriving Inhabited

private def parseArg (xs : List String) (flag : String) : Option String :=
  match xs with
  | [] => none
  | x::y::rest => if x = flag then some y else parseArg (y::rest) flag
  | _ => none

private def hasFlag (xs : List String) (flag : String) : Bool :=
  match xs with
  | [] => false
  | x::rest => if x = flag then true else hasFlag rest flag

private def parseArgs (argv : List String) : Args :=
  let start := (parseArg argv "--start").getD "A"
  let rule  := (parseArg argv "--rule").getD "fib"
  let maxDepth := (parseArg argv "--maxDepth").bind (·.toNat?) |>.getD 4
  let maxBreadth := (parseArg argv "--maxBreadth").bind (·.toNat?) |>.getD 64
  {rule, start, maxDepth, maxBreadth}

private def pickRule (name : String) : StrSystem :=
  let n := name.trim.toLower
  if n = "fib" then StrRule.fibSys
  else if n = "dup" then StrRule.dupSys
  else StrRule.simpleSys

def main (argv : List String) : IO Unit := do
  let args := parseArgs argv
  let noBranchial := hasFlag argv "--no-branchial"
  let noEvents := hasFlag argv "--no-events"
  let wantInv := hasFlag argv "--checkInvariance"
  let joinDepth := (parseArg argv "--maxJoinDepth").bind (·.toNat?) |>.getD 2
  let wantInvAll := hasFlag argv "--invarianceAll"
  let sys := pickRule args.rule
  let res := HeytingLean.WPP.Build.buildMultiway sys args.start args.maxDepth args.maxBreadth (!noBranchial) (!noEvents)
  let nodesJson := Json.arr (res.nodes.map Json.str)
  let edgesJson := Json.arr (res.edges.map (fun e => Json.mkObj [("src", Json.num e.src), ("dst", Json.num e.dst)]))
  let eventsJson := Json.arr (res.events.map (fun e => Json.mkObj [("src", Json.num e.src), ("dst", Json.num e.dst), ("label", Json.str e.label)]))
  let eventEdgesJson := Json.arr (res.eventEdges.map (fun e => Json.mkObj [("src", Json.num e.src), ("dst", Json.num e.dst)]))
  let levelsJson :=
    let arrs : Array (Array Json) := res.levels.map (fun lvl => (lvl.map (fun (i : Nat) => Json.num i)))
    Json.arr (arrs.map Json.arr)
  let baseFields : List (String × Json) :=
    [ ("rule", Json.str args.rule)
    , ("start", Json.str args.start)
    , ("maxDepth", Json.num args.maxDepth)
    , ("maxBreadth", Json.num args.maxBreadth)
    , ("nodes", nodesJson)
    , ("edges", edgesJson)
    , ("levels", levelsJson)
    , ("events", eventsJson)
    , ("eventEdges", eventEdgesJson) ]
  let payload := Id.run do
    let mut fields := baseFields
    let bj := Json.arr (res.branchial.map (fun e => Json.mkObj [("i", Json.num e.src), ("j", Json.num e.dst)]))
    fields := fields ++ [("branchial", bj)]
    if wantInv then
      let holds := if wantInvAll then
        HeytingLean.WPP.Build.checkInvarianceAllLevels sys res joinDepth
      else HeytingLean.WPP.Build.checkInvarianceDepth1 sys args.start joinDepth
      let invObj :=
        if holds then Json.mkObj
          [ ("checked", Json.bool true)
          , ("diamondDepth", Json.num joinDepth)
          , ("holds", Json.bool true)
          , ("scope", Json.str (if wantInvAll then "all-levels" else "root")) ]
        else
          match HeytingLean.WPP.Build.firstNonInvariantWitness sys args.start joinDepth with
          | some (s, t1, t2) => Json.mkObj
              [ ("checked", Json.bool true)
              , ("diamondDepth", Json.num joinDepth)
              , ("holds", Json.bool false)
              , ("scope", Json.str (if wantInvAll then "all-levels" else "root"))
              , ("witness", Json.mkObj [("s", Json.str s), ("t1", Json.str t1), ("t2", Json.str t2)]) ]
          | none => Json.mkObj [ ("checked", Json.bool true), ("diamondDepth", Json.num joinDepth), ("holds", Json.bool false), ("scope", Json.str (if wantInvAll then "all-levels" else "root")) ]
      fields := fields ++ [("invariance", invObj)]
    Json.mkObj fields
  IO.println payload.pretty
