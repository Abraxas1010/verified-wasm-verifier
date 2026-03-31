import Lean
import HeytingLean.WPP.Wolfram.Branchial
import HeytingLean.WPP.Wolfram.ConfluenceCausalInvariance
import HeytingLean.WPP.Wolfram.SimpleHypergraph

open Lean

open HeytingLean.WPP
open HeytingLean.WPP.Wolfram

/-! Internal anchors to ensure the fresh-vertex and injective-WLOG Wolfram development is
elaborated whenever this executable is built. -/
private abbrev _WolframFreshAnchor (V : Type) (P : Type) := SystemFresh V P
private abbrev _WolframSimpleEdgesAnchor (V : Type) := HGraph.SimpleEdges (V := V) (0 : HGraph V)

structure Args where
  sys : String := "ce1"
  maxDepth : Nat := 3
deriving Inhabited

private def parseArg (xs : List String) (flag : String) : Option String :=
  match xs with
  | [] => none
  | x::y::rest => if x = flag then some y else parseArg (y::rest) flag
  | _ => none

private def parseArgs (argv : List String) : Args :=
  let sys := (parseArg argv "--sys").getD "ce1"
  let maxDepth := (parseArg argv "--maxDepth").bind (·.toNat?) |>.getD 3
  {sys, maxDepth}

/-! ## Pretty/JSON encodings (small Fin-based demos) -/

private def exprToJson {n : Nat} (e : Wolfram.Expr (Fin n)) : Json :=
  Json.arr ((e.map (fun v => Json.num v.1)).toArray)

private def sigmaFin2ToJson {n : Nat} (σ : Fin 2 → Fin n) : Json :=
  Json.arr #[Json.num (σ 0).1, Json.num (σ 1).1]

private def eventDataToJson {n : Nat} (sys : Wolfram.System (Fin n) (Fin 2)) (ed : sys.EventData) : Json :=
  Json.mkObj
    [ ("ruleIdx", Json.num ed.1.1)
    , ("sigma", sigmaFin2ToJson (n := n) ed.2) ]

private def mkBasisLen1Len2 (n : Nat) : Array (Wolfram.Expr (Fin n)) :=
  Id.run do
    let verts : Array (Fin n) := Array.ofFn (fun v => v)
    let mut out : Array (Wolfram.Expr (Fin n)) := #[]
    for v in verts do
      out := out.push [v]
    for a in verts do
      for b in verts do
        out := out.push [a, b]
    return out

private def stateToCountsJson {n : Nat} (basis : Array (Wolfram.Expr (Fin n))) (g : Wolfram.HGraph (Fin n)) : Json :=
  Json.arr (basis.map (fun e => Json.num (g.count e)))

private def allSigmasFin2 {n : Nat} : Array (Fin 2 → Fin n) :=
  Id.run do
    let verts : Array (Fin n) := Array.ofFn (fun v => v)
    let mut out : Array (Fin 2 → Fin n) := #[]
    for a in verts do
      for b in verts do
        if a = b then
          pure ()
        else
          out := out.push (Counterexamples.sigma2 (V := Fin n) a b)
    return out

/-! ## A tiny multiway builder for Wolfram systems (bounded depth) -/

private def findIdxFuel {α : Type} [DecidableEq α] (arr : Array α) (x : α) (fuel i : Nat) : Option Nat :=
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

private def buildMultiway {n : Nat} (sys : Wolfram.System (Fin n) (Fin 2)) (maxDepth : Nat) :
    Json := Id.run do
  -- ensure the finite instances exist
  let basis := mkBasisLen1Len2 n
  let sigmas := allSigmasFin2 (n := n)

  match hRules : sys.rules with
  | [] =>
      return Json.mkObj
        [ ("error", Json.str "system has no rules")
        , ("maxDepth", Json.num maxDepth) ]
  | _rule :: _rulesTail =>
      let mut nodes : Array (Wolfram.HGraph (Fin n)) := #[sys.init]
      let mut edges : Array Json := #[]
      let mut branchial : Array Json := #[]
      let mut levels : Array (Array Nat) := #[#[0]]

      let mut curr : Array (Wolfram.HGraph (Fin n)) := #[sys.init]
      let idx0 : Fin sys.rules.length :=
        ⟨0, by
          -- Use the equation from `match hRules : sys.rules` to rewrite the goal.
          rw [hRules]
          exact Nat.succ_pos _rulesTail.length⟩

      for _step in [0:maxDepth] do
        -- compute next level from `curr`
        let mut nextRaw : Array (Wolfram.HGraph (Fin n)) := #[]
        for s in curr do
          let (nodes1, srcIdx) := getIdx nodes s
          nodes := nodes1
          -- collect distinct child indices for branchial edges
          let mut childIdxs : Array Nat := #[]
          for σ in sigmas do
            let ed : sys.EventData := (idx0, σ)
            if System.EventData.Applicable (sys := sys) ed s then
              let t := System.EventData.apply (sys := sys) ed s
              let (nodes2, dstIdx) := getIdx nodes t
              nodes := nodes2
              edges := edges.push <|
                Json.mkObj
                  [ ("src", Json.num srcIdx)
                  , ("dst", Json.num dstIdx)
                  , ("label", eventDataToJson (n := n) sys ed) ]
              childIdxs := childIdxs.push dstIdx
              nextRaw := nextRaw.push t
            else
              pure ()
          let childIdxsDedup := dedupArray childIdxs
          for (i, j) in pairEdges childIdxsDedup do
            branchial := branchial.push <| Json.mkObj [("i", Json.num i), ("j", Json.num j)]

        let next := dedupArray nextRaw
        -- record this level (indices in the global `nodes` array)
        let nextIdxs : Array Nat :=
          next.map (fun s =>
            let (_, i) := getIdx nodes s
            i)
        levels := levels.push nextIdxs
        curr := next

      -- path counts per level (depth-indexed)
      let mut pathCounts : Array Json := #[]
      for d in [0:(maxDepth + 1)] do
        let lvl := levels[d]!
        let counts := lvl.map (fun (i : Nat) =>
          let st := nodes[i]!
          Json.mkObj [("id", Json.num i), ("count", Json.num (sys.pathCountAtDepth d st))])
        pathCounts := pathCounts.push (Json.arr counts)

      let basisJson := Json.arr (basis.map (exprToJson (n := n)))
      let nodesJson := Json.arr (nodes.map (stateToCountsJson (n := n) basis))
      let edgesJson := Json.arr edges
      let branchialJson := Json.arr branchial
      let levelsJson := Json.arr (levels.map (fun lvl => Json.arr (lvl.map (fun (i : Nat) => Json.num i))))

      return Json.mkObj
        [ ("maxDepth", Json.num maxDepth)
        , ("basis_len1_len2", basisJson)
        , ("nodes", nodesJson)
        , ("edges", edgesJson)
        , ("levels", levelsJson)
        , ("branchial", branchialJson)
        , ("pathCounts", Json.arr pathCounts) ]

private def runCE1 (maxDepth : Nat) : Json :=
  buildMultiway (n := 3) (sys := Counterexamples.CE1.sys) maxDepth

private def runCE2 (maxDepth : Nat) : Json :=
  buildMultiway (n := 2) (sys := Counterexamples.CE2.sys) maxDepth

def main (argv : List String) : IO Unit := do
  let args := parseArgs argv
  let sysName := args.sys.trim.toLower
  let payload :=
    if sysName = "ce2" then
      runCE2 args.maxDepth
    else
      runCE1 args.maxDepth
  IO.println payload.pretty
