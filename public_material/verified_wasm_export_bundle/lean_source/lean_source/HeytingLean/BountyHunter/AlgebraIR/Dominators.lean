import Std
import HeytingLean.BountyHunter.AlgebraIR.Types

/-!
# HeytingLean.BountyHunter.AlgebraIR.Dominators

Dominance analysis over the AlgebraIR control-flow graph (CFG over `NodeId`).

Phase 0 requirement: implement dominance-style checks such as CEI
(writes dominate boundary calls).

We use a simple iterative dataflow algorithm over finite node sets.
-/

namespace HeytingLean.BountyHunter.AlgebraIR

open Std

private def arrayToSet (xs : Array NodeId) : Std.HashSet NodeId :=
  Id.run do
    let mut s : Std.HashSet NodeId := Std.HashSet.emptyWithCapacity xs.size
    for x in xs do
      s := s.insert x
    return s

private def setIntersect (a b : Std.HashSet NodeId) : Std.HashSet NodeId :=
  Id.run do
    let mut out : Std.HashSet NodeId := Std.HashSet.emptyWithCapacity (min a.size b.size)
    for x in a.toList do
      if b.contains x then
        out := out.insert x
    return out

private def setEq (a b : Std.HashSet NodeId) : Bool :=
  a.size = b.size && a.toList.all (fun x => b.contains x)

/-- Compute the dominator sets `dom[n]` for each node `n`.

`dom[entry] = {entry}`
`dom[n] = {n} ∪ ⋂_{p ∈ preds[n]} dom[p]` otherwise.
-/
structure DomInfo where
  ids : Array NodeId
  dom : Array (Std.HashSet NodeId)
  deriving Inhabited

private def idxOf (ids : Array NodeId) (n : NodeId) : Option Nat :=
  Id.run do
    let mut i : Nat := 0
    while i < ids.size do
      if ids[i]! = n then
        return some i
      i := i + 1
    return none

private def predsOfNode (g : Graph) (n : NodeId) : Array NodeId :=
  g.nodes.foldl
    (fun acc m => if m.succs.any (fun s => s = n) then acc.push m.id else acc)
    #[]

def dominators (g : Graph) : DomInfo :=
  Id.run do
    let ids := g.nodes.map (·.id)
    let all := arrayToSet ids
    let mut dom : Array (Std.HashSet NodeId) := #[]
    for n in ids do
      if n = g.entry then
        dom := dom.push (Std.HashSet.emptyWithCapacity 1 |>.insert n)
      else
        dom := dom.push all
    let mut changed := true
    while changed do
      changed := false
      for n in ids do
        if n = g.entry then
          continue
        let ps := predsOfNode g n
        if ps.isEmpty then
          -- Unreachable nodes: keep {n} as a conservative fixed point.
          let new := Std.HashSet.emptyWithCapacity 1 |>.insert n
          match idxOf ids n with
          | none => pure ()
          | some i =>
              if !setEq dom[i]! new then
                dom := dom.set! i new
                changed := true
        else
          let base :=
            match idxOf ids ps[0]! with
            | none => all
            | some i => dom[i]!
          let mut inter : Std.HashSet NodeId := base
          for p in ps.toList.drop 1 do
            match idxOf ids p with
            | none => pure ()
            | some i => inter := setIntersect inter dom[i]!
          let new := inter.insert n
          match idxOf ids n with
          | none => pure ()
          | some i =>
              if !setEq dom[i]! new then
                dom := dom.set! i new
                changed := true
    return { ids := ids, dom := dom }

/-- `a` dominates `b` if `a ∈ dom[b]`. -/
def dominates (g : Graph) (a b : NodeId) : Bool :=
  let info := dominators g
  match idxOf info.ids b with
  | none => false
  | some i => info.dom[i]!.contains a

end HeytingLean.BountyHunter.AlgebraIR
