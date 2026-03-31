import HeytingLean.Genesis.EigenformSoup.Substrate

/-!
# Genesis.EigenformSoup.RuntimeTrace

Computable runtime mirror for LES trace payload generation.

This lane avoids noncomputable `Set`-based support equality by using finite
support carriers (`Finset Nat`) while preserving the WS2/WS3 dialectic event
shape (thesis/antithesis/synthesis).
-/

namespace HeytingLean.Genesis.EigenformSoup

/-- Finite support carrier for executable trace runs. -/
abbrev RuntimeSupport : Type := Finset Nat

/-- Runtime nucleus model over finite supports. -/
abbrev RuntimeNucleus : Type := RuntimeSupport → RuntimeSupport

/-- Executable collapse nucleus mirror (`insert 0`). -/
def collapseRuntimeNucleus : RuntimeNucleus :=
  fun s => insert 0 s

/-- Runtime LoF support semantics over finite supports. -/
def runtimeExprSupport : HeytingLean.Genesis.LoFExpr0 → RuntimeSupport
  | .void => ∅
  | .var _ => ∅
  | .reentry => {0}
  | .mark e => (runtimeExprSupport e).image Nat.succ
  | .juxt a b => runtimeExprSupport a ∪ runtimeExprSupport b

/-- Runtime substrate generation config. -/
structure RuntimeConfig where
  maxDepth : Nat := 4
  size : Nat := 16
deriving Repr

/-- Runtime expression pool (same combinatorics as WS1 substrate pool). -/
def runtimeExprPool (cfg : RuntimeConfig) : List HeytingLean.Genesis.LoFExpr0 :=
  (List.range (cfg.maxDepth + 1)).map HeytingLean.Genesis.nesting ++
    (List.range cfg.maxDepth).map
      (fun n => HeytingLean.LoF.LoFSecond.Expr.mark (HeytingLean.Genesis.nesting n))

/-- Runtime critical size model (mirrors protocol proxy calibration). -/
def runtimeCriticalSize (cfg : RuntimeConfig) : Nat :=
  Nat.shiftLeft 1 (cfg.maxDepth + 2)

/-- Runtime growth-rate model (mirrors protocol proxy calibration). -/
def runtimeGrowthRate (cfg : RuntimeConfig) : Nat :=
  if cfg.size < runtimeCriticalSize cfg then 0 else cfg.size - runtimeCriticalSize cfg + 1

/-- Runtime first-eigenform epoch model (mirrors protocol proxy calibration). -/
def runtimeFirstEigenformEpoch? (cfg : RuntimeConfig) : Option Nat :=
  let rate := runtimeGrowthRate cfg
  if rate = 0 then none else some (Nat.max 1 (runtimeCriticalSize cfg / rate))

/-- Deterministic pooled expression lookup. -/
def runtimeExprAt (cfg : RuntimeConfig) (id : Nat) : HeytingLean.Genesis.LoFExpr0 :=
  let pool := runtimeExprPool cfg
  let idx := id % (Nat.max 1 pool.length)
  (pool[idx]?).getD .void

/-- Runtime oscillator element (proof-erased/non-certified lane). -/
structure RuntimeElement where
  id : Nat
  expr : HeytingLean.Genesis.LoFExpr0
  support : RuntimeSupport
  phase : Phase

/-- Runtime one-step phase update. -/
def runtimeAdvancePhase : Phase → Phase
  | .i => .j
  | .j => .i

/-- Runtime element generation candidate. -/
def mkRuntimeElement?
    (nuc : RuntimeNucleus)
    (id : Nat)
    (expr : HeytingLean.Genesis.LoFExpr0) : Option RuntimeElement :=
  let support := runtimeExprSupport expr
  if nuc support = support then
    none
  else
    some
      { id := id
        expr := expr
        support := support
        phase := phaseOfId id }

/-- Deterministic runtime element generation. -/
def runtimeGenerateElementsAux
    (nuc : RuntimeNucleus)
    (cfg : RuntimeConfig) : Nat → Nat → List RuntimeElement
  | 0, _id => []
  | Nat.succ fuel, id =>
      let expr := runtimeExprAt cfg id
      match mkRuntimeElement? nuc id expr with
      | some el => el :: runtimeGenerateElementsAux nuc cfg fuel (id + 1)
      | none => runtimeGenerateElementsAux nuc cfg fuel (id + 1)

/-- Runtime substrate elements. -/
def runtimeGenerateElements (nuc : RuntimeNucleus) (cfg : RuntimeConfig) : List RuntimeElement :=
  runtimeGenerateElementsAux nuc cfg cfg.size 0

/-- Runtime dialectic interaction event. -/
structure RuntimeInteractionEvent where
  lhs : RuntimeElement
  rhs : RuntimeElement
  meetSupport : RuntimeSupport
  joinSupport : RuntimeSupport

/-- Runtime scheduler pairing predicate. -/
def runtimeShouldPair (a b : RuntimeElement) : Bool :=
  match a.phase, b.phase with
  | .i, .j => true
  | .j, .i => true
  | _, _ => false

/-- Runtime adjacent phase-derived pairing schedule. -/
def runtimePhaseDerivedPairs
    (xs : List RuntimeElement) : List (RuntimeElement × RuntimeElement) :=
  (List.zip xs xs.tail).filter (fun p => runtimeShouldPair p.1 p.2)

/-- Runtime interaction constructor. -/
def runtimeInteract (lhs rhs : RuntimeElement) : RuntimeInteractionEvent :=
  { lhs := lhs
    rhs := rhs
    meetSupport := lhs.support ∩ rhs.support
    joinSupport := lhs.support ∪ rhs.support }

/-- Runtime one-step interaction schedule. -/
def runtimeRunSchedule (cfg : RuntimeConfig) (epoch : Nat) (elements : List RuntimeElement) :
    List RuntimeInteractionEvent :=
  let pairs := runtimePhaseDerivedPairs elements
  let rate := runtimeGrowthRate cfg
  match runtimeFirstEigenformEpoch? cfg with
  | none => []
  | some first =>
      if epoch + 1 < first then
        []
      else
        (pairs.take rate).map (fun p => runtimeInteract p.1 p.2)

/-- Runtime stabilized synthesis support for one interaction. -/
def runtimeSynthesisSupport (nuc : RuntimeNucleus) (ev : RuntimeInteractionEvent) : RuntimeSupport :=
  let thesis := nuc ev.meetSupport
  let antithesis := nuc ev.joinSupport
  nuc (thesis ∪ antithesis)

/-- Runtime stabilized supports extracted from scheduled interactions. -/
def runtimeStabilizedSupports
    (nuc : RuntimeNucleus)
    (events : List RuntimeInteractionEvent) : List RuntimeSupport :=
  events.map (runtimeSynthesisSupport nuc)

/-- Runtime soup state. -/
structure RuntimeState where
  epoch : Nat
  elements : List RuntimeElement
  stabilized : List RuntimeSupport

/-- Runtime initial state. -/
def runtimeInitState (nuc : RuntimeNucleus) (cfg : RuntimeConfig) : RuntimeState :=
  { epoch := 0
    elements := runtimeGenerateElements nuc cfg
    stabilized := [] }

/-- Runtime one-step phase advancement. -/
def runtimeAdvanceElement (e : RuntimeElement) : RuntimeElement :=
  { e with phase := runtimeAdvancePhase e.phase }

/-- Runtime one-step state transition. -/
def runtimeStep (cfg : RuntimeConfig) (nuc : RuntimeNucleus) (s : RuntimeState) : RuntimeState :=
  let events := runtimeRunSchedule cfg s.epoch s.elements
  { epoch := s.epoch + 1
    elements := s.elements.map runtimeAdvanceElement
    stabilized := s.stabilized ++ runtimeStabilizedSupports nuc events }

/-- Runtime fuel-bounded execution. -/
def runtimeRunAux (cfg : RuntimeConfig) (nuc : RuntimeNucleus) : Nat → RuntimeState → RuntimeState
  | 0, s => s
  | Nat.succ fuel, s => runtimeRunAux cfg nuc fuel (runtimeStep cfg nuc s)

/-- Runtime trace (includes initial state). -/
def runtimeTraceAux (cfg : RuntimeConfig) (nuc : RuntimeNucleus) : Nat → RuntimeState → List RuntimeState
  | 0, s => [s]
  | Nat.succ fuel, s => s :: runtimeTraceAux cfg nuc fuel (runtimeStep cfg nuc s)

/-- Runtime config-driven trace. -/
def runtimeTrace (nuc : RuntimeNucleus) (cfg : RuntimeConfig) (fuel : Nat) : List RuntimeState :=
  runtimeTraceAux cfg nuc fuel (runtimeInitState nuc cfg)

/-- Runtime trace snapshot surface for protocol serialization. -/
structure RuntimeSnapshot where
  epoch : Nat
  stabilizedCount : Nat
  unresolvedCount : Nat
  jLevel : Nat
deriving Repr

/-- Runtime snapshot projection. -/
def runtimeSnapshotOfState (s : RuntimeState) : RuntimeSnapshot :=
  { epoch := s.epoch
    stabilizedCount := s.stabilized.length
    unresolvedCount := s.elements.length - s.stabilized.length
    jLevel := s.stabilized.length }

/-- Runtime snapshots from one trace. -/
def runtimeSnapshots (trace : List RuntimeState) : List RuntimeSnapshot :=
  trace.map runtimeSnapshotOfState

/-- Runtime trace length law. -/
theorem runtimeTraceAux_length (cfg : RuntimeConfig) (nuc : RuntimeNucleus) (fuel : Nat) (s : RuntimeState) :
    (runtimeTraceAux cfg nuc fuel s).length = fuel + 1 := by
  induction fuel generalizing s with
  | zero =>
      simp [runtimeTraceAux]
  | succ fuel ih =>
      simp [runtimeTraceAux, ih]

end HeytingLean.Genesis.EigenformSoup
