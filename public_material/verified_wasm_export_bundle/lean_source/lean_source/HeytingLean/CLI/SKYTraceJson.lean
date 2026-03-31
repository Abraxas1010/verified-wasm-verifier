import Lean.Data.Json
import HeytingLean.LoF.Combinators.SKYMachineBounded

namespace HeytingLean.CLI.SKYTraceJson

open Lean
open HeytingLean.LoF.Combinators

partial def collectReachableIds
    (s : SKYMachineBounded.State α) (todo seen : List Nat) : List Nat :=
  match todo with
  | [] => seen
  | id :: rest =>
      if id ∈ seen then
        collectReachableIds s rest seen
      else
        match s.node? id with
        | some (.app f a) => collectReachableIds s (f :: a :: rest) (id :: seen)
        | some _ => collectReachableIds s rest (id :: seen)
        | none => collectReachableIds s rest seen

def reachableIds (s : SKYMachineBounded.State α) : List Nat :=
  collectReachableIds s (s.focus :: s.stack) []

partial def isReducibleAt
    (s : SKYMachineBounded.State α) (id argc : Nat) : Bool :=
  match s.node? id with
  | some (.app f _a) => isReducibleAt s f (argc + 1)
  | some .combK => argc >= 2
  | some .combS => argc >= 3
  | some .combY => argc >= 1
  | some (.oracle _) => argc >= 2
  | none => false

def activeIds (s : SKYMachineBounded.State α) (reachable : List Nat) : List Nat :=
  reachable.filter (fun id => isReducibleAt s id 0)

def traceSampleToJson (step : Nat) (s : SKYMachineBounded.State α) : Json :=
  let reachable := reachableIds s
  let active := activeIds s reachable
  Json.mkObj
    [ ("step", toJson step)
    , ("nodesUsed", toJson s.nodes.size)
    , ("reachableNodes", toJson reachable.length)
    , ("activeRedexes", toJson active.length)
    , ("reachableIds", toJson reachable.toArray)
    , ("activeIds", toJson active.toArray)
    , ("focus", toJson s.focus)
    , ("stackDepth", toJson s.stack.length)
    ]

end HeytingLean.CLI.SKYTraceJson
