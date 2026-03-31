import Lean
import HeytingLean.WPP.Wolfram.WM148

open Lean

namespace HeytingLean
namespace CLI

open HeytingLean.WPP
open HeytingLean.WPP.Wolfram

/-!
CLI: bounded multiway exploration for Wolfram Physics universe **WM148**

This emits a JSON payload for the rule `{{x,y}} -> {{x,y},{y,z}}` from the Wolfram Physics
Project "Causal Invariance" page.

We intentionally keep the schema close to `wolfram_multiway_demo` (basis + count vectors),
but with `Nat` vertices and an automatically chosen finite basis `0..maxVertex`.
-/

namespace WolframWM148

structure Args where
  maxDepth : Nat := 6
deriving Inhabited

private def parseArg (xs : List String) (flag : String) : Option String :=
  match xs with
  | [] => none
  | x::y::rest => if x = flag then some y else parseArg (y::rest) flag
  | _ => none

private def parseArgs (argv : List String) : Args :=
  let maxDepth := (parseArg argv "--maxDepth").bind (·.toNat?) |>.getD 6
  {maxDepth}

/-! ## JSON helpers -/

private def exprToJsonNat (e : Wolfram.Expr Nat) : Json :=
  Json.arr (e.map (fun v => Json.num v) |>.toArray)

private def sigmaFin2ToJsonNat (σ : Fin 2 → Nat) : Json :=
  Json.arr #[Json.num (σ 0), Json.num (σ 1)]

private def mkBasisLen1Len2Nat (maxVertex : Nat) : Array (Wolfram.Expr Nat) :=
  Id.run do
    let verts : Array Nat := (List.range (maxVertex + 1)).toArray
    let mut out : Array (Wolfram.Expr Nat) := #[]
    for v in verts do
      out := out.push [v]
    for a in verts do
      for b in verts do
        out := out.push [a, b]
    return out

private def stateToCountsJsonNat (basis : Array (Wolfram.Expr Nat)) (g : Wolfram.HGraph Nat) : Json :=
  Json.arr (basis.map (fun e => Json.num (g.count e)))

/-! ## Multiway exploration (bounded) -/

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

private def buildWM148Multiway (maxDepth : Nat) : Json := Id.run do
  let sys := Wolfram.WM148.sys
  let mut nodes : Array (Wolfram.HGraph Nat) := #[sys.init]
  let mut edges : Array Json := #[]
  let mut levels : Array (Array Nat) := #[#[0]]

  let mut curr : Array (Wolfram.HGraph Nat) := #[sys.init]

  for _step in [0:maxDepth] do
    let mut nextRaw : Array (Wolfram.HGraph Nat) := #[]
    for s in curr do
      let (nodes1, srcIdx) := getIdx nodes s
      nodes := nodes1

      let verts := Wolfram.HGraph.verts (V := Nat) s
      -- Enumerate candidate match-values as `0..maxVertex` (a superset of `verts`).
      -- This avoids relying on `Finset.toList` (noncomputable).
      let maxV : Nat := verts.sup id
      let vals : Array Nat := (List.range (maxV + 1)).toArray

      for a in vals do
        for b in vals do
          let σ : Fin 2 → Nat :=
            Fin.cases a (fun _ => b)
          let e := Wolfram.WM148.mkEvent σ
          if SystemFresh.Event.Applicable (sys := sys) e s then
            let t := Wolfram.WM148.applyDet (e := e) (s := s)
            let (nodes2, dstIdx) := getIdx nodes t
            nodes := nodes2
            edges := edges.push <|
              Json.mkObj
                [ ("src", Json.num srcIdx)
                , ("dst", Json.num dstIdx)
                , ("label", Json.mkObj
                    [ ("ruleIdx", Json.num 0)
                    , ("sigma", sigmaFin2ToJsonNat σ) ]) ]
            nextRaw := nextRaw.push t
          else
            pure ()

    let next := dedupArray nextRaw
    let nextIdxs : Array Nat :=
      next.map (fun s =>
        let (_, i) := getIdx nodes s
        i)
    levels := levels.push nextIdxs
    curr := next

  -- pick a finite basis from the maximum vertex label seen among all nodes
  let mut maxVertex : Nat := 0
  for s in nodes do
    let verts := Wolfram.HGraph.verts (V := Nat) s
    let m : Nat := verts.sup id
    if maxVertex < m then
      maxVertex := m
    else
      pure ()

  let basis := mkBasisLen1Len2Nat maxVertex
  let basisJson := Json.arr (basis.map exprToJsonNat)
  let nodesJson := Json.arr (nodes.map (stateToCountsJsonNat basis))
  let edgesJson := Json.arr edges
  let levelsJson := Json.arr (levels.map (fun lvl => Json.arr (lvl.map (fun (i : Nat) => Json.num i))))

  return Json.mkObj
    [ ("system", Json.str "wm148")
    , ("maxDepth", Json.num maxDepth)
    , ("maxVertex", Json.num maxVertex)
    , ("basis_len1_len2", basisJson)
    , ("nodes", nodesJson)
    , ("edges", edgesJson)
    , ("levels", levelsJson) ]

def run (argv : List String) : IO Unit := do
  let args := parseArgs argv
  let payload := buildWM148Multiway args.maxDepth
  IO.println payload.pretty

end WolframWM148

end CLI
end HeytingLean

def main (argv : List String) : IO Unit :=
  HeytingLean.CLI.WolframWM148.run argv
