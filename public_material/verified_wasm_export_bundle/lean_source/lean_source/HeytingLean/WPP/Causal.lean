import Std
import HeytingLean.WPP.Examples.StringRules

namespace HeytingLean
namespace WPP

structure Edge where
  src : Nat
  dst : Nat
deriving Inhabited

structure LabeledEdge where
  src : Nat
  dst : Nat
  label : String
deriving Inhabited

structure MultiwayResult where
  nodes  : Array String
  edges  : Array Edge
  levels : Array (Array Nat)
  branchial : Array Edge := #[]
  events : Array LabeledEdge := #[]    -- labeled events (parent→child at a position/rule)
  eventEdges : Array Edge := #[]       -- dependencies between events (e1.dst = e2.src)
  deriving Inhabited

namespace Build

open Examples

private def dedup (xs : Array String) : Array String :=
  let step := fun (st : Std.HashSet String × Array String) (s : String) =>
    let seen := st.fst; let out := st.snd
    if seen.contains s then st else (seen.insert s, out.push s)
  (xs.foldl step ((Std.HashSet.emptyWithCapacity : Std.HashSet String), (#[] : Array String))).snd

def nextLevel (sys : Examples.StrSystem) (curr : Array String) : Array String :=
  let raw := curr.foldl (init := (#[] : Array String)) (fun acc s => acc ++ Examples.StrRule.step sys s)
  dedup raw

private def findIdxFuel (arr : Array String) (s : String) (fuel i : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if i < arr.size then
        let a := arr[i]!
        if a = s then some i else findIdxFuel arr s fuel (i + 1)
      else
        none

def findIdx (arr : Array String) (s : String) : Option Nat :=
  findIdxFuel arr s (arr.size + 1) 0

def buildMultiway (sys : Examples.StrSystem) (start : String)
    (maxDepth : Nat) (maxBreadth : Nat := 256) (withBranchial : Bool := true) (withEvents : Bool := true) : MultiwayResult :=
  let getIdx (nodes : Array String) (s : String) : (Array String × Nat) :=
    match findIdx nodes s with
    | some i => (nodes, i)
    | none   => (nodes.push s, nodes.size)
  let rec loop (d : Nat) (curr : Array String)
      (nodes : Array String) (edges : Array Edge) (levels : Array (Array Nat)) (branchial : Array Edge)
      (events : Array LabeledEdge) (eventEdges : Array Edge) (lastEvs : Array LabeledEdge) (lastBase : Nat) :
      MultiwayResult :=
    if d = 0 then {nodes, edges, levels, branchial, events, eventEdges}
    else
      let nxtRaw := nextLevel sys curr
      let xs := nxtRaw
      let xsTake := xs.extract 0 (Nat.min xs.size maxBreadth)
      let (nodes1, idxs) := xsTake.foldl (init := (nodes, ([] : List Nat))) (fun (st, acc) s =>
        let (nodes', j) := getIdx st s
        (nodes', j :: acc))
      let nextIdxs : Array Nat := (idxs.reverse).toArray
      -- build parent→child edges (all children)
      let (nodes2, edges2, genEvents) := curr.foldl (init := (nodes1, edges, (#[] : Array LabeledEdge))) (fun (st, es, evs) p =>
        let (nodes', pj) := getIdx st p
        let childs := (Examples.StrRule.step sys p)
        let es' := childs.foldl (init := es)
          (fun esacc c =>
            let (_, cj) := getIdx nodes' c
            esacc.push {src := pj, dst := cj})
        -- labeled events if requested
        if withEvents then
          let inLevel := xsTake.foldl (init := (Std.HashSet.emptyWithCapacity : Std.HashSet String)) (fun acc s => acc.insert s)
          let evs' := (Examples.StrRule.stepLabeled sys p).foldl (init := evs) (fun acc (c, lab) =>
            if inLevel.contains c then
              let (_, cj) := getIdx nodes' c
              acc.push {src := pj, dst := cj, label := lab}
            else acc)
          (nodes', es', evs')
        else (nodes', es', evs))
      -- optional: branchial edges among siblings restricted to xsTake
      let inLevel := xsTake.foldl (init := (Std.HashSet.emptyWithCapacity : Std.HashSet String)) (fun acc s => acc.insert s)
      let pairEdges (idxs : Array Nat) : Array Edge :=
        let n := idxs.size
        let rec outer (i : Nat) (acc : Array Edge) : Array Edge :=
          if i < n then
            let ii := idxs[i]!
            let rec inner (j : Nat) (acc2 : Array Edge) : Array Edge :=
              if j < n then
                let jj := idxs[j]!
                inner (j+1) (acc2.push {src := ii, dst := jj})
              else acc2
            let acc' := inner (i+1) acc
            outer (i+1) acc'
          else acc
        outer 0 #[]
      let (_, br) :=
        if withBranchial then
          curr.foldl (init := (nodes2, branchial)) (fun (st, bacc) p =>
            let (nodes', _pj) := getIdx st p
            let childs := (Examples.StrRule.step sys p).filter (fun c => inLevel.contains c)
            let idxs : Array Nat := childs.foldl (init := (#[] : Array Nat)) (fun a c =>
              let (_, cj) := getIdx nodes' c
              a.push cj)
            (nodes', bacc ++ pairEdges idxs))
        else (nodes2, branchial)
      let levels' := levels.push nextIdxs
      let curr' : Array String := xsTake
      -- Compute event graph pieces
      let (events', link, last, base) :=
        if withEvents then
          let base := events.size
          let events' := events ++ genEvents
          let m := lastEvs.size
          let n := genEvents.size
          let rec linkOuter (i : Nat) (acc : Array Edge) : Array Edge :=
            if i < m then
              let ePrev := lastEvs[i]!
              let prevIdx := lastBase + i
              let rec linkInner (j : Nat) (acc2 : Array Edge) : Array Edge :=
                if j < n then
                  let eCurr := genEvents[j]!
                  let acc2' := if ePrev.dst = eCurr.src then acc2.push {src := prevIdx, dst := base + j} else acc2
                  linkInner (j+1) acc2'
                else acc2
              let acc' := linkInner 0 acc
              linkOuter (i+1) acc'
            else acc
          (events', eventEdges ++ linkOuter 0 #[], genEvents, base)
        else (events, eventEdges, lastEvs, lastBase)
      loop (d-1) curr' nodes2 edges2 levels' br events' link last base
  let (nodes0, i0) := getIdx #[] start
  let levels0 := #[(#[(i0)])]
  loop maxDepth (#[(start)]) nodes0 #[] levels0 #[] #[] #[] #[] 0

/-! Bounded invariance (diamond) check at depth 1 using a join search up to `k`.
Returns `true` if every fork at level 1 admits a join within `k` steps. -/
private def reachableWithinArr (sys : Examples.StrSystem) (s : String) (k : Nat) : Array String :=
  let rec go (fr : Array String) (seen : Std.HashSet String) (acc : Array String) (fuel : Nat) : Array String :=
    if fuel = 0 then acc else
      let next := fr.foldl (init := (#[] : Array String)) (fun a x => a ++ Examples.StrRule.step sys x)
      let (seen', next') := next.foldl (init := (seen, (#[] : Array String))) (fun (st, a) x =>
        if st.contains x then (st, a) else (st.insert x, a.push x))
      let acc' := acc ++ next'
      go next' seen' acc' (fuel - 1)
  let seen0 : Std.HashSet String := (Std.HashSet.emptyWithCapacity : Std.HashSet String).insert s
  go (#[(s)]) seen0 (#[]) k

def checkInvarianceDepth1 (sys : Examples.StrSystem) (start : String) (k : Nat) : Bool :=
  let children := Examples.StrRule.step sys start
  let arr := children
  let n := arr.size
  let rec pair (i : Nat) : Bool :=
    if h : i < n then
      let si := arr[i]!
      let rec inner (j : Nat) : Bool :=
        if hj : j < n then
          if j = i then inner (j+1) else
          let sj := arr[j]!
          let ri := reachableWithinArr sys si k
          let rjSet := ri.foldl (init := (Std.HashSet.emptyWithCapacity : Std.HashSet String)) (fun st u => st.insert u)
          let rj := reachableWithinArr sys sj k
          let ok := rj.any (fun u => rjSet.contains u)
          if ok then inner (j+1) else false
        else true
      let rest := inner 0
      if rest then pair (i+1) else false
    else true
  pair 0

def firstNonInvariantWitness (sys : Examples.StrSystem) (start : String) (k : Nat) : Option (String × String × String) :=
  let children := Examples.StrRule.step sys start
  let arr := children
  let n := arr.size
  let rec outer (i : Nat) : Option (String × String × String) :=
    if i < n then
      let si := arr[i]!
      let rec inner (j : Nat) : Option (String × String × String) :=
        if hj : j < n then
          if j = i then inner (j+1) else
          let sj := arr[j]!
          let ri := reachableWithinArr sys si k
          let rjSet := ri.foldl (init := (Std.HashSet.emptyWithCapacity : Std.HashSet String)) (fun st u => st.insert u)
          let rj := reachableWithinArr sys sj k
          let ok := rj.any (fun u => rjSet.contains u)
          if ok then inner (j+1) else some (start, si, sj)
        else none
      match inner 0 with
      | some w => some w
      | none => outer (i+1)
    else none
  outer 0

def checkInvarianceAllLevels (sys : Examples.StrSystem) (res : MultiwayResult) (k : Nat) : Bool :=
  let nodes := res.nodes
  let lvls := res.levels
  let L := lvls.size
  let rec overLvl (li : Nat) : Bool :=
    if li < L then
      -- for each parent in this level, fork-check its immediate children
      let parents := lvls[li]!
      let okParent :=
        let rec goP (pi : Nat) : Bool :=
          if pi < parents.size then
            let pIdx := parents[pi]!
            let s := nodes[pIdx]!
            let children := Examples.StrRule.step sys s
            let n := children.size
            let rec pair (i : Nat) : Bool :=
              if i < n then
                let si := children[i]!
                let rec inner (j : Nat) : Bool :=
                  if j < n then
                    if j = i then inner (j+1) else
                    let sj := children[j]!
                    let ri := reachableWithinArr sys si k
                    let rjSet := ri.foldl (init := (Std.HashSet.emptyWithCapacity : Std.HashSet String)) (fun st u => st.insert u)
                    let rj := reachableWithinArr sys sj k
                    let ok := rj.any (fun u => rjSet.contains u)
                    if ok then inner (j+1) else false
                  else true
                let rest := inner 0
                if rest then pair (i+1) else false
              else true
            let okHere := pair 0
            if okHere then goP (pi+1) else false
          else true
        goP 0
      if okParent then overLvl (li+1) else false
    else true
  overLvl 0

end Build

end WPP
end HeytingLean
