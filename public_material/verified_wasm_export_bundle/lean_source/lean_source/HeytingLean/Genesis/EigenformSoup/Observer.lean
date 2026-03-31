import HeytingLean.Genesis.EigenformSoup.Runner
import HeytingLean.Genesis.Observer

open scoped Classical

/-!
# Genesis.EigenformSoup.Observer

WS6 observer layer for soup traces.
-/

namespace HeytingLean.Genesis.EigenformSoup

/-- Observer configuration specialized for soup traces. -/
structure SoupObserver where
  minTransitionDepth : Nat := 1
deriving Repr

/-- One compact observation emitted from a soup state. -/
structure SoupObservation where
  epoch : Nat
  stabilizedCount : Nat
  replicationRate : Nat
deriving Repr

/-- Observe one soup state under a selected nucleus. -/
noncomputable def observe
    (nuc : SoupNucleus)
    (_observer : SoupObserver)
    (s : SoupState nuc) : SoupObservation :=
  { epoch := s.epoch
    stabilizedCount := s.stabilized.length
    replicationRate := replicationRate nuc s.stabilized }

/-- Observe a whole finite soup trace. -/
noncomputable def observeTrace
    (nuc : SoupNucleus)
    (observer : SoupObserver)
    (trace : List (SoupState nuc)) : List SoupObservation :=
  trace.map (observe nuc observer)

theorem observeTrace_length
    {nuc : SoupNucleus}
    (observer : SoupObserver)
    (trace : List (SoupState nuc)) :
    (observeTrace nuc observer trace).length = trace.length := by
  simp [observeTrace]

/-- Extract phase labels of the substrate at a state. -/
def phaseVector {nuc : SoupNucleus} (s : SoupState nuc) : List Phase :=
  s.substrate.elements.map (fun e => e.phase)

/-- Transition detector based on phase-vector change. -/
def phaseTransition {nuc : SoupNucleus} (s₁ s₂ : SoupState nuc) : Prop :=
  phaseVector s₁ ≠ phaseVector s₂

/-- Count detected phase transitions in a finite state trace. -/
noncomputable def detectPhaseTransitions {nuc : SoupNucleus} : List (SoupState nuc) → Nat
  | s₁ :: s₂ :: rest =>
      (if phaseTransition s₁ s₂ then 1 else 0) + detectPhaseTransitions (s₂ :: rest)
  | _ => 0

/-- Minimum-depth detector lemma: one changed pair yields a positive transition count. -/
theorem detectPhaseTransitions_pos_of_pair
    {nuc : SoupNucleus}
    {s₁ s₂ : SoupState nuc}
    (h : phaseTransition s₁ s₂) :
    0 < detectPhaseTransitions [s₁, s₂] := by
  classical
  simp [detectPhaseTransitions, h]

end HeytingLean.Genesis.EigenformSoup
