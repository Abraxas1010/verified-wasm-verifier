import Lean
import HeytingLean.ProofWidgets.LoFViz.State

namespace HeytingLean
namespace ProofWidgets
namespace LoFViz

open Lean
open Lean Server
open scoped Classical

namespace RegionSet

def contains : List String → String → Bool
  | [], _ => false
  | r :: rs, s => if r = s then true else contains rs s

def insert (s : List String) (r : String) : List String :=
  if contains s r then s else r :: s

def erase : List String → String → List String
  | [], _ => []
  | r :: rs, s =>
      if r = s then erase rs s else r :: erase rs s

def union (a b : List String) : List String :=
  b.foldl insert a

def inter (a b : List String) : List String :=
  a.filter (fun r => contains b r)

def diff (u a : List String) : List String :=
  u.filter (fun r => ¬ contains a r)

def subset (a b : List String) : Bool :=
  a.all (fun r => contains b r)

def equal (a b : List String) : Bool :=
  subset a b && subset b a

@[simp] def card (s : List String) : Nat := s.length

@[simp] def isEmpty (s : List String) : Bool := s.isEmpty

@[simp] def toString (s : List String) : String :=
  let body := String.intercalate ", " s.reverse
  "{" ++ body ++ "}"

end RegionSet

private def regionCycle : Array String := #["α", "β", "γ", "δ"]
private def coreRegion : String := "α"
private def satelliteRegion : String := "δ"
private def regionUniverse : List String := regionCycle.toList

/-- Certificate bundle returned alongside renders. -/
structure CertificateBundle where
  adjunction    : Bool := true
  rt₁           : Bool := true
  rt₂           : Bool := true
  classicalized : Bool := false
  messages      : Array String := #[]
  deriving Inhabited, Repr, ToJson, FromJson, Server.RpcEncodable

/-- Track aggregate information extracted from the primitive journal. -/
structure Aggregate where
  current   : List String := []
  previous  : Option (List String) := none
  stack     : List String := []
  marks     : Nat := 0
  unmarks   : Nat := 0
  reentries : Nat := 0
  deriving Inhabited

namespace Aggregate

private def nextRegion (agg : Aggregate) : String :=
  let idx := agg.marks % regionCycle.size
  regionCycle[idx]!

@[inline] def pushUnique (stack : List String) (r : String) : List String :=
  RegionSet.insert (RegionSet.erase stack r) r

/-- Apply the nucleus closure used by the illustrative LoF model. -/
def closure (base : List String) (nextReentry : Nat) : List String :=
  if RegionSet.contains base coreRegion then
    if nextReentry % 2 = 0 then RegionSet.insert base satelliteRegion else regionUniverse
  else RegionSet.insert base coreRegion

@[simp] def empty : Aggregate := {}

/-- Update aggregate state with a primitive interaction. -/
def step (agg : Aggregate) : Primitive → Aggregate
  | .mark =>
      let region := nextRegion agg
      { agg with
          previous := some agg.current
          current := RegionSet.insert agg.current region
          stack := pushUnique agg.stack region
          marks := agg.marks + 1 }
  | .unmark =>
      match agg.stack with
      | [] =>
          { agg with
              previous := some agg.current
              current := []
              stack := []
              unmarks := agg.unmarks + 1 }
      | region :: rest =>
          { agg with
              previous := some agg.current
              current := RegionSet.erase agg.current region
              stack := rest
              unmarks := agg.unmarks + 1 }
  | .reentry =>
      let nextReentry := agg.reentries + 1
      let newCurrent := closure agg.current nextReentry
      let additions := newCurrent.filter (fun region => ¬ RegionSet.contains agg.current region)
      let newStack := additions.foldl pushUnique agg.stack
      { agg with
          previous := some agg.current
          current := newCurrent
          stack := newStack
          reentries := nextReentry }

/-- Reduce a full journal into aggregate statistics. -/
def ofJournal (journal : Array JournalEntry) : Aggregate :=
  journal.foldl (fun acc entry => acc.step entry.primitive) Aggregate.empty

end Aggregate

private def renderSet (s : List String) : String :=
  RegionSet.toString s

private def renderOptionSet : Option (List String) → String
  | some s => renderSet s
  | none   => "∅ (initial)"

/-- Visualization kernel distilled from widget state. -/
structure KernelData where
  state     : State
  aggregate : Aggregate
  summary   : String

namespace KernelData

/-- Build kernel data from a persisted widget state. -/
def fromState (s : State) : KernelData :=
  let agg := Aggregate.ofJournal s.journal
  let summary :=
    s!"scene={s.sceneId} • dial={s.dialStage} • lens={s.lens} • mode={s.mode} • marks={agg.marks} • re={agg.reentries}"
  { state := s, aggregate := agg, summary }

/-- Heyting nucleus closure used for proof calculations. -/
def nucleus (s : List String) : List String :=
  if RegionSet.contains s coreRegion then regionUniverse else RegionSet.insert s coreRegion

/-- Heyting implication in this illustrative finite lattice. -/
def implication (a b : List String) : List String :=
  nucleus (RegionSet.union (RegionSet.diff regionUniverse a) b)

/-- Meet of two regions in the lattice. -/
def meet (a b : List String) : List String :=
  RegionSet.inter a b

@[inline] def currentIsActive (k : KernelData) : Bool :=
  ¬ RegionSet.isEmpty k.aggregate.current

@[inline] def previousIsActive (k : KernelData) : Bool :=
  match k.aggregate.previous with
  | some prev => ¬ RegionSet.isEmpty prev
  | none      => false

/-- Synthetic breathing angle (θ) derived from the interaction counts. -/
def breathingAngle (k : KernelData) : Nat :=
  (90 * k.aggregate.reentries + 30 * k.aggregate.marks - 20 * k.aggregate.unmarks) % 360

/-- Human-readable notes surfaced in the HUD. -/
def notes (k : KernelData) : Array String :=
  #[
    k.summary,
    s!"current subset: {renderSet k.aggregate.current}",
    s!"previous subset: {renderOptionSet k.aggregate.previous}",
    s!"counts → mark:{k.aggregate.marks} unmark:{k.aggregate.unmarks} re-entry:{k.aggregate.reentries}",
    s!"θ (breathing angle) ≈ {k.breathingAngle}°"
  ]

/-- Public string form of the current nucleus subset. -/
def currentSetString (k : KernelData) : String :=
  renderSet k.aggregate.current

/-- Public string form of the previous nucleus subset. -/
def previousSetString (k : KernelData) : String :=
  renderOptionSet k.aggregate.previous

/-- Size of the current region selection. -/
def currentCard (k : KernelData) : Nat :=
  RegionSet.card k.aggregate.current

/-- Size of the previous region selection. -/
def previousCard (k : KernelData) : Nat :=
  match k.aggregate.previous with
  | some prev => RegionSet.card prev
  | none      => 0

/-- Status flags used to colour the fibre bundle visualisation. -/
structure FiberStatus where
  logicStable    : Bool
  tensorBounded  : Bool
  graphActivated : Bool
  cliffordEven   : Bool
  deriving Inhabited

/-- Compute fibre status booleans for the HUD/renderer. -/
def fiberStatus (k : KernelData) : FiberStatus :=
  { logicStable :=
      RegionSet.equal k.aggregate.current (nucleus k.aggregate.current)
    tensorBounded := RegionSet.card k.aggregate.current ≤ 2
    graphActivated := k.aggregate.reentries > 0
    cliffordEven := k.aggregate.marks % 2 = 0 }

/-- Static note referencing the established Stage transport lemmas. -/
@[inline] def stageTransportNote : String :=
  "Stage transports (tensor/graph/clifford) proven via stageMvAdd_encode / stageEffectAdd_encode / stageOrthocomplement_encode."

/-- Notes specific to the fiber-bundle visualization. -/
def fiberNotes (k : KernelData) : Array String :=
  let status := k.fiberStatus
  #[
    s!"Logic lens: closure {if status.logicStable then "stable" else "pending"} (nucleus fixed point).",
    s!"Tensor lens: support {RegionSet.card k.aggregate.current} region(s) ({if status.tensorBounded then "within" else "beyond"} linear capacity).",
    s!"Graph lens: re-entry {if status.graphActivated then "observed" else "not yet witnessed"} in journal.",
    s!"Clifford lens: mark parity {if status.cliffordEven then "even (dualised)" else "odd (torsion)"}.",
    stageTransportNote
  ]

private def previous (k : KernelData) : List String :=
  k.aggregate.previous.getD []

/-- Certificates computed from the aggregates and the canonical LoF nucleus. -/
def certificates (k : KernelData) : CertificateBundle :=
  let prev := previous k
  let curr := k.aggregate.current
  let closedPrev := nucleus prev
  let closedCurr := nucleus curr
  let adjunction := RegionSet.subset prev (implication curr closedCurr)
  let rt₁ := RegionSet.equal closedPrev prev
  let rt₂ := RegionSet.equal closedCurr curr
  let classicalized :=
    match k.state.dialStage with
    | .s3_sphere => true
    | _          => false
  { adjunction
    rt₁
    rt₂
    classicalized
    messages :=
      k.notes ++
        #[ s!"meet(current, previous) = {renderSet (meet curr prev)}",
           s!"implication(previous ⇒ current) = {renderSet (implication prev curr)}",
           s!"nucleus(current) = {renderSet closedCurr}" ] }

end KernelData

end LoFViz
end ProofWidgets
end HeytingLean
