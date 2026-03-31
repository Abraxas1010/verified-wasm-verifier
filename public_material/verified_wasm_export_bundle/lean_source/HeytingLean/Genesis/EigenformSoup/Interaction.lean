import HeytingLean.Genesis.EigenformSoup.Substrate

/-!
# Genesis.EigenformSoup.Interaction

WS2 interaction engine:
- phase-derived pairing schedule,
- meet/join interaction events,
- phase advancement via `Iterant.shift`,
- stabilized candidate extraction.
-/

namespace HeytingLean.Genesis.EigenformSoup

/-- Convert phase labels to the existing iterant witnesses. -/
def phaseToIterant : Phase → HeytingLean.Genesis.Iterant Bool
  | .i => HeytingLean.Genesis.phaseI
  | .j => HeytingLean.Genesis.phaseJ

/-- Decode iterant phase back into soup labels. -/
def phaseFromIterant (x : HeytingLean.Genesis.Iterant Bool) : Phase :=
  if x = HeytingLean.Genesis.phaseI then .i else .j

/-- Phase advancement implemented through the existing iterant shift operator. -/
def advancePhase : Phase → Phase
  | .i => .j
  | .j => .i

@[simp] theorem advancePhase_i : advancePhase .i = .j := by
  rfl

@[simp] theorem advancePhase_j : advancePhase .j = .i := by
  rfl

/-- `advancePhase` agrees with iterant-shift semantics on canonical I/J phases. -/
theorem advancePhase_eq_shift (p : Phase) :
    advancePhase p = phaseFromIterant (HeytingLean.Genesis.Iterant.shift (phaseToIterant p)) := by
  cases p with
  | i =>
      have hShift :
          HeytingLean.Genesis.Iterant.shift HeytingLean.Genesis.phaseI =
            HeytingLean.Genesis.phaseJ := by
        simpa using HeytingLean.Genesis.phaseJ_eq_shift_phaseI.symm
      have hNe : HeytingLean.Genesis.phaseJ ≠ HeytingLean.Genesis.phaseI := by
        intro hEq
        exact HeytingLean.Genesis.phaseI_ne_phaseJ hEq.symm
      simp [advancePhase, phaseFromIterant, phaseToIterant, hShift, hNe]
  | j =>
      have hShift :
          HeytingLean.Genesis.Iterant.shift HeytingLean.Genesis.phaseJ =
            HeytingLean.Genesis.phaseI := by
        simpa using HeytingLean.Genesis.phaseI_eq_shift_phaseJ.symm
      simp [advancePhase, phaseFromIterant, phaseToIterant, hShift]

/-- Update one oscillatory element by advancing only the phase label. -/
def advanceElementPhase {nuc : SoupNucleus} (e : OscElement nuc) : OscElement nuc :=
  { e with phase := advancePhase e.phase }

/-- Bulk phase advancement for one soup step. -/
def advanceElementsPhases {nuc : SoupNucleus} (xs : List (OscElement nuc)) : List (OscElement nuc) :=
  xs.map advanceElementPhase

/-- Pairing predicate for the default phase-derived scheduler. -/
def shouldPair {nuc : SoupNucleus} (a b : OscElement nuc) : Bool :=
  match a.phase, b.phase with
  | .i, .j => true
  | .j, .i => true
  | _, _ => false

/-- Deterministic adjacent pairing schedule with phase checks. -/
def phaseDerivedPairs {nuc : SoupNucleus}
    (xs : List (OscElement nuc)) : List (OscElement nuc × OscElement nuc) :=
  (List.zip xs xs.tail).filter (fun p => shouldPair p.1 p.2)

/-- One interaction event records meet/join on support carriers. -/
structure InteractionEvent (nuc : SoupNucleus) where
  lhs : OscElement nuc
  rhs : OscElement nuc
  meetSupport : Support
  joinSupport : Support

/-- Build one meet/join interaction event. -/
def interact {nuc : SoupNucleus} (lhs rhs : OscElement nuc) : InteractionEvent nuc :=
  { lhs := lhs
    rhs := rhs
    meetSupport := lhs.support ⊓ rhs.support
    joinSupport := lhs.support ⊔ rhs.support }

/-- Run the default schedule over a substrate. -/
def runSchedule {nuc : SoupNucleus} (S : Substrate nuc) : List (InteractionEvent nuc) :=
  (phaseDerivedPairs S.elements).map (fun p => interact p.1 p.2)

/-- Nucleus-closure of a support value. -/
def closeSupport (nuc : SoupNucleus) (s : Support) : Support :=
  nuc s

/-- Thesis channel: closed meet support (convergence/compression). -/
def thesisSupport (nuc : SoupNucleus) (ev : InteractionEvent nuc) : Support :=
  closeSupport nuc ev.meetSupport

/-- Antithesis channel: closed join support (divergence/composition). -/
def antithesisSupport (nuc : SoupNucleus) (ev : InteractionEvent nuc) : Support :=
  closeSupport nuc ev.joinSupport

/-- Synthesis channel: closure over the tension-composed thesis/antithesis supports. -/
def synthesisSupport (nuc : SoupNucleus) (ev : InteractionEvent nuc) : Support :=
  closeSupport nuc (thesisSupport nuc ev ⊔ antithesisSupport nuc ev)

theorem thesisSupport_fixed {nuc : SoupNucleus} (ev : InteractionEvent nuc) :
    isFixed nuc (thesisSupport nuc ev) := by
  unfold thesisSupport closeSupport isFixed
  exact Nucleus.idempotent (n := nuc) (x := ev.meetSupport)

theorem antithesisSupport_fixed {nuc : SoupNucleus} (ev : InteractionEvent nuc) :
    isFixed nuc (antithesisSupport nuc ev) := by
  unfold antithesisSupport closeSupport isFixed
  exact Nucleus.idempotent (n := nuc) (x := ev.joinSupport)

theorem synthesisSupport_fixed {nuc : SoupNucleus} (ev : InteractionEvent nuc) :
    isFixed nuc (synthesisSupport nuc ev) := by
  unfold synthesisSupport closeSupport isFixed
  exact Nucleus.idempotent (n := nuc) (x := thesisSupport nuc ev ⊔ antithesisSupport nuc ev)

/-- Stabilized supports extracted from synthesis channels of interaction events. -/
def stabilizedSupports (nuc : SoupNucleus) (events : List (InteractionEvent nuc)) : List Support :=
  events.map (fun ev => synthesisSupport nuc ev)

theorem mem_stabilizedSupports_fixed
    {nuc : SoupNucleus} {events : List (InteractionEvent nuc)}
    {S : Support} (hS : S ∈ stabilizedSupports nuc events) :
    isFixed nuc S := by
  rcases List.mem_map.mp hS with ⟨ev, _hev, hEq⟩
  subst hEq
  exact synthesisSupport_fixed (nuc := nuc) ev

theorem runSchedule_deterministic {nuc : SoupNucleus} (S : Substrate nuc) :
    runSchedule S = runSchedule S := rfl

end HeytingLean.Genesis.EigenformSoup
