import Lean
import Std.Data.HashMap
import HeytingLean.CLI.Args
import HeytingLean.LoF.Combinators.SKYMultiway

open Lean

namespace HeytingLean
namespace CLI

open HeytingLean.LoF
open HeytingLean.LoF.Comb

/-!
CLI: bounded multiway exploration for SKY combinators

This executable emits a JSON payload for a bounded-depth multiway graph of a chosen
SKY term, together with the branchial sibling graph and per-depth path counts.

Schema (stable, WL-comparable):
- `nodes`     : Array[CombJson]            (index = node id)
- `edges`     : Array[{src,dst,label}]     label = {ruleIdx,path}
- `levels`    : Array[Array[Nat]]          node ids at each depth (dedup per depth)
- `branchial` : Array[{i,j}]               sibling edges among children of each node
- `pathCounts`: Array[Array[{id,count}]]   per-depth number of paths reaching each node id
-/

namespace SkyMultiway

structure Args where
  demo : String := "sk"
  maxDepth : Nat := 4
deriving Inhabited

private def parseArg (xs : List String) (flag : String) : Option String :=
  match xs with
  | [] => none
  | x :: y :: rest => if x = flag then some y else parseArg (y :: rest) flag
  | _ => none

private def parseArgs (argv : List String) : Args :=
  let argv := HeytingLean.CLI.stripLakeArgs argv
  let demo := (parseArg argv "--demo").getD "sk"
  let maxDepth := (parseArg argv "--maxDepth").bind (·.toNat?) |>.getD 4
  { demo, maxDepth }

/-! ## Demo terms -/

private def demoSK : Comb :=
  -- ( (K K) S ) ( (K S) K )
  Comb.app
    (Comb.app (Comb.app .K .K) .S)
    (Comb.app (Comb.app .K .S) .K)

private def demoY : Comb :=
  -- (Y K) ( (K S) K )
  Comb.app
    (Comb.app .Y .K)
    (Comb.app (Comb.app .K .S) .K)

private def selectDemo (name : String) : (String × Comb) :=
  let key := name.trim.toLower
  if key = "y" || key = "sky" then
    ("sky_demo_y", demoY)
  else
    ("sky_demo_sk", demoSK)

/-! ## JSON encodings -/

private def combToJson : Comb → Json
  | .K => Json.arr #[Json.num 0]
  | .S => Json.arr #[Json.num 1]
  | .Y => Json.arr #[Json.num 2]
  | .app f a => Json.arr #[Json.num 3, combToJson f, combToJson a]

private def pathToJson (p : Comb.RedexPath) : Json :=
  Json.arr ((p.map (fun d => Json.num d.toNat)).toArray)

private def eventToJson (ed : Comb.EventData) : Json :=
  Json.mkObj
    [ ("ruleIdx", Json.num ed.rule.toNat)
    , ("path", pathToJson ed.path) ]

/-! ## Multiway exploration (bounded) -/

private def findIdxFuel {α : Type} [DecidableEq α] (arr : Array α) (x : α) (fuel i : Nat) :
    Option Nat :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if h : i < arr.size then
        if arr[i] = x then some i else findIdxFuel arr x fuel (i + 1)
      else
        none

private def findIdx {α : Type} [DecidableEq α] (arr : Array α) (x : α) : Option Nat :=
  findIdxFuel arr x (arr.size + 1) 0

private def getIdx {α : Type} [DecidableEq α] (nodes : Array α) (x : α) : (Array α × Nat) :=
  match findIdx nodes x with
  | some i => (nodes, i)
  | none => (nodes.push x, nodes.size)

private def dedupArray {α : Type} [DecidableEq α] (xs : Array α) : Array α :=
  xs.foldl (init := (#[] : Array α)) (fun acc x => if acc.contains x then acc else acc.push x)

private def pairEdges (idxs : Array Nat) : Array (Nat × Nat) :=
  let n := idxs.size
  let rec outer (i : Nat) (acc : Array (Nat × Nat)) : Array (Nat × Nat) :=
    if i < n then
      let ii := idxs[i]!
      let rec inner (j : Nat) (acc2 : Array (Nat × Nat)) : Array (Nat × Nat) :=
        if j < n then
          let jj := idxs[j]!
          inner (j + 1) (acc2.push (ii, jj))
        else acc2
      outer (i + 1) (inner (i + 1) acc)
    else acc
  outer 0 #[]

private def getD (m : Std.HashMap Nat Nat) (k : Nat) (default : Nat) : Nat :=
  match m.get? k with
  | some v => v
  | none => default

private def incrCount (m : Std.HashMap Nat Nat) (k : Nat) (inc : Nat) : Std.HashMap Nat Nat :=
  let curr := getD m k 0
  m.insert k (curr + inc)

private def buildMultiway (sysName : String) (init : Comb) (maxDepth : Nat) : Json := Id.run do
  let mut nodes : Array Comb := #[init]
  let mut edges : Array Json := #[]
  let mut branchial : Array Json := #[]
  let mut levels : Array (Array Nat) := #[#[0]]

  let mut curr : Array Comb := #[init]
  let mut countsCurr : Std.HashMap Nat Nat := (Std.HashMap.emptyWithCapacity 8).insert 0 1
  let mut pathCounts : Array Json :=
    #[Json.arr #[Json.mkObj [("id", Json.num 0), ("count", Json.num 1)]]]

  for _step in [0:maxDepth] do
    let mut nextRaw : Array Comb := #[]
    let mut countsNext : Std.HashMap Nat Nat := Std.HashMap.emptyWithCapacity 8
    for s in curr do
      let (nodes1, srcIdx) := getIdx nodes s
      nodes := nodes1
      let srcCount := getD countsCurr srcIdx 0
      let mut childIdxs : Array Nat := #[]
      for (ed, t) in (Comb.stepEdgesList s) do
        let (nodes2, dstIdx) := getIdx nodes t
        nodes := nodes2
        edges := edges.push <|
          Json.mkObj
            [ ("src", Json.num srcIdx)
            , ("dst", Json.num dstIdx)
            , ("label", eventToJson ed) ]
        childIdxs := childIdxs.push dstIdx
        nextRaw := nextRaw.push t
        countsNext := incrCount countsNext dstIdx srcCount
      let childIdxsDedup := dedupArray childIdxs
      for (i, j) in pairEdges childIdxsDedup do
        branchial := branchial.push <| Json.mkObj [("i", Json.num i), ("j", Json.num j)]

    let next := dedupArray nextRaw
    let nextIdxs : Array Nat :=
      next.map (fun s =>
        let (_, i) := getIdx nodes s
        i)
    levels := levels.push nextIdxs
    let countsJson :=
      nextIdxs.map (fun (i : Nat) =>
        Json.mkObj [("id", Json.num i), ("count", Json.num (getD countsNext i 0))])
    pathCounts := pathCounts.push (Json.arr countsJson)
    curr := next
    countsCurr := countsNext

  let nodesJson := Json.arr (nodes.map combToJson)
  let edgesJson := Json.arr edges
  let branchialJson := Json.arr branchial
  let levelsJson := Json.arr (levels.map (fun lvl => Json.arr (lvl.map (fun (i : Nat) => Json.num i))))
  let pathCountsJson := Json.arr pathCounts

  return Json.mkObj
    [ ("system", Json.str sysName)
    , ("maxDepth", Json.num maxDepth)
    , ("nodes", nodesJson)
    , ("edges", edgesJson)
    , ("levels", levelsJson)
    , ("branchial", branchialJson)
    , ("pathCounts", pathCountsJson) ]

def main (argv : List String) : IO Unit := do
  let args := parseArgs argv
  let (sysName, init) := selectDemo args.demo
  let payload := buildMultiway sysName init args.maxDepth
  IO.println payload.pretty

end SkyMultiway

end CLI
end HeytingLean

def main (argv : List String) : IO Unit :=
  HeytingLean.CLI.SkyMultiway.main argv

