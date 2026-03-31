import Std
import HeytingLean.BountyHunter.AlgebraIR.Types
import HeytingLean.BountyHunter.AlgebraIR.CEI
import HeytingLean.BountyHunter.AlgebraIR.Evidence

/-!
# HeytingLean.BountyHunter.AlgebraIR.EvidenceClosure

Implements the minimal, deterministic closure operator `R : Evidence → Evidence`
for the “lattice of evidence” spine.

v0 closure rules (cheap/deterministic):
- transitive closure for `OrderKind.happensBefore`

Everything else is intentionally left as staged follow-on work.
-/

namespace HeytingLean.BountyHunter.AlgebraIR
namespace Evidence

open Std

/-! ## Lens-style deltas -/

def deltaOfGraph (g : Graph) : Delta :=
  Id.run do
    let mut effects : Array EffectFact := #[]
    let mut orders : Array OrderFact := #[]
    for n in g.nodes do
      for e in n.effects do
        effects := effects.push { node := n.id, eff := e }
      for s in n.succs do
        orders := orders.push { kind := .happensBefore, a := n.id, b := s }
    return normalize { effects := effects, orders := orders }

def deltaOfCEIResult (slot : Nat) (slotExpr? : Option String) (v : HeytingLean.BountyHunter.AlgebraIR.Verdict)
    (w? : Option HeytingLean.BountyHunter.AlgebraIR.CEIWitness) : Delta :=
  match v, w? with
  | .safe, _ =>
      match slotExpr? with
      | none => normalize { claims := #[.ceiSafe slot] }
      | some se => normalize { claims := #[.ceiSafeSlotExpr se] }
  | .vulnerable, some w =>
      let wf : WitnessFact :=
        .ceiPath
          { boundaryNode := w.boundaryNode
            slot := w.slot
            slotExpr? := w.slotExpr?
            path := w.path
            reason := w.reason
          }
      normalize { witnesses := #[wf] }
  | .outOfScope r, _ => normalize { notes := #[s!"cei_out_of_scope:{r}"] }
  | .vulnerable, none => normalize { notes := #["cei_vulnerable_missing_witness"] }

/-! ## `R`: closure under derived evidence -/

private def sortDedupNat (xs : Array Nat) : Array Nat :=
  Id.run do
    let ys := xs.qsort (fun a b => a < b)
    let mut out : Array Nat := #[]
    for x in ys do
      match out.back? with
      | none => out := out.push x
      | some y =>
          if x = y then
            continue
          else
            out := out.push x
    return out

private def addAdj (m : Std.HashMap NodeId (Array NodeId)) (a b : NodeId) : Std.HashMap NodeId (Array NodeId) :=
  match m.get? a with
  | none => m.insert a #[b]
  | some bs => m.insert a (bs.push b)

private def normalizeAdj (m : Std.HashMap NodeId (Array NodeId)) : Std.HashMap NodeId (Array NodeId) :=
  Id.run do
    let mut out := m
    for (k, v) in m.toList do
      out := out.insert k (sortDedupNat v)
    return out

private def bfsReachable (adj : Std.HashMap NodeId (Array NodeId)) (start : NodeId) (fuel : Nat) : Array NodeId :=
  Id.run do
    let mut visited : Std.HashSet NodeId := Std.HashSet.emptyWithCapacity 64
    let mut q : List NodeId := [start]
    let mut out : Array NodeId := #[]
    visited := visited.insert start
    let mut fuel := fuel
    while fuel > 0 do
      fuel := fuel - 1
      match q with
      | [] => return out
      | v :: rest =>
          q := rest
          for s in adj.getD v #[] do
            if !visited.contains s then
              visited := visited.insert s
              out := out.push s
              q := q ++ [s]
    return out

private def closeHappensBefore (e : Evidence) : Evidence :=
  let base := normalize e
  let edges : Array (NodeId × NodeId) :=
    base.orders.foldl
      (fun acc o => if o.kind = .happensBefore then acc.push (o.a, o.b) else acc)
      #[]
  if edges.isEmpty then
    base
  else
    Id.run do
      let mut nodes : Array NodeId := #[]
      let mut adj : Std.HashMap NodeId (Array NodeId) := Std.HashMap.emptyWithCapacity (edges.size + 1)
      for (a, b) in edges do
        nodes := nodes.push a
        nodes := nodes.push b
        adj := addAdj adj a b
      nodes := sortDedupNat nodes
      adj := normalizeAdj adj
      let mut derived : Array OrderFact := #[]
      for a in nodes do
        let reach := bfsReachable adj a (nodes.size + 5)
        for b in reach do
          derived := derived.push { kind := .happensBefore, a := a, b := b }
      return merge base { orders := derived }

/-- `R`: close evidence by adding deterministic derived facts. -/
def close (e : Evidence) : Evidence :=
  closeHappensBefore e

/-! ## Verdict derivation from closed evidence -/

def ceiWitnessFromEvidence (e : Evidence) (slot : Nat) : Option HeytingLean.BountyHunter.AlgebraIR.CEIWitness :=
  let w? : Option CEIPathWitness :=
    e.witnesses.toList.findSome? (fun w =>
      match w with
      | .ceiPath ww =>
          if ww.slot = slot && ww.slotExpr?.isNone then some ww else none)
  match w? with
  | none => none
  | some w =>
      some
        { boundaryNode := w.boundaryNode
          slot := w.slot
          slotExpr? := none
          path := w.path
          reason := w.reason
        }

def ceiWitnessFromEvidenceSlotExpr (e : Evidence) (slotExpr : String) :
    Option HeytingLean.BountyHunter.AlgebraIR.CEIWitness :=
  let w? : Option CEIPathWitness :=
    e.witnesses.toList.findSome? (fun w =>
      match w with
      | .ceiPath ww =>
          match ww.slotExpr? with
          | some se => if se = slotExpr then some ww else none
          | none => none)
  match w? with
  | none => none
  | some w =>
      some
        { boundaryNode := w.boundaryNode
          slot := 0
          slotExpr? := some slotExpr
          path := w.path
          reason := w.reason
        }

def ceiSafeClaimed (e : Evidence) (slot : Nat) : Bool :=
  e.claims.toList.any (fun c => match c with | .ceiSafe s => s = slot | _ => false)

def ceiSafeSlotExprClaimed (e : Evidence) (slotExpr : String) : Bool :=
  e.claims.toList.any (fun c => match c with | .ceiSafeSlotExpr s => s = slotExpr | _ => false)

def deriveCEIFromClosedEvidence (eClosed : Evidence) (slot : Nat) :
    HeytingLean.BountyHunter.AlgebraIR.Verdict × Option HeytingLean.BountyHunter.AlgebraIR.CEIWitness :=
  match ceiWitnessFromEvidence eClosed slot with
  | some w => (.vulnerable, some w)
  | none =>
      if ceiSafeClaimed eClosed slot then
        (.safe, none)
      else
        (.outOfScope "insufficient evidence to derive CEI verdict", none)

def deriveCEIFromClosedEvidenceSlotExpr (eClosed : Evidence) (slotExpr : String) :
    HeytingLean.BountyHunter.AlgebraIR.Verdict × Option HeytingLean.BountyHunter.AlgebraIR.CEIWitness :=
  match ceiWitnessFromEvidenceSlotExpr eClosed slotExpr with
  | some w => (.vulnerable, some w)
  | none =>
      if ceiSafeSlotExprClaimed eClosed slotExpr then
        (.safe, none)
      else
        (.outOfScope "insufficient evidence to derive CEI verdict", none)

end Evidence
end HeytingLean.BountyHunter.AlgebraIR
