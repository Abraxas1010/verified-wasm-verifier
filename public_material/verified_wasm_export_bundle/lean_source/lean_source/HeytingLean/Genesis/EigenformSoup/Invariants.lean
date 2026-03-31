import HeytingLean.Genesis.EigenformSoup.Runner
import HeytingLean.Topos.JRatchet

/-!
# Genesis.EigenformSoup.Invariants

WS7 invariants and ratchet-facing quantities for soup runs.
-/

namespace HeytingLean.Genesis.EigenformSoup

/-- Carrier-size observable (stays constant under phase-only updates). -/
def carrierSize {nuc : SoupNucleus} (s : SoupState nuc) : Nat :=
  s.substrate.elements.length

/-- Monotone stabilized mass used as a simple ratchet measure. -/
def stabilizedMass {nuc : SoupNucleus} (s : SoupState nuc) : Nat :=
  s.stabilized.length

/-- Entropy surrogate: unresolved carrier mass. -/
def entropyMetric {nuc : SoupNucleus} (s : SoupState nuc) : Nat :=
  carrierSize s - stabilizedMass s

/-- Soup-local J-ratchet level proxy. -/
def jRatchetLevel {nuc : SoupNucleus} (s : SoupState nuc) : Nat :=
  stabilizedMass s

/-- Dialectic thesis mass at one epoch (closed-meet channel count). -/
def thesisMass {nuc : SoupNucleus} (s : SoupState nuc) : Nat :=
  (scheduledEvents s).map (fun ev => thesisSupport nuc ev) |>.length

/-- Dialectic antithesis mass at one epoch (closed-join channel count). -/
def antithesisMass {nuc : SoupNucleus} (s : SoupState nuc) : Nat :=
  (scheduledEvents s).map (fun ev => antithesisSupport nuc ev) |>.length

/-- Dialectic synthesis mass at one epoch (new stabilized supports). -/
def synthesisMass {nuc : SoupNucleus} (s : SoupState nuc) : Nat :=
  (newStabilized s).length

/-- A ratchet click is a strict increase in J-ratchet level after one step. -/
def ratchetClick {nuc : SoupNucleus} (s : SoupState nuc) : Prop :=
  jRatchetLevel s < jRatchetLevel (stepSoup s)

theorem thesis_antithesis_coequal {nuc : SoupNucleus} (s : SoupState nuc) :
    thesisMass s = antithesisMass s := by
  simp [thesisMass, antithesisMass]

theorem synthesisMass_eq_event_count {nuc : SoupNucleus} (s : SoupState nuc) :
    synthesisMass s = (scheduledEvents s).length := by
  simp [synthesisMass, newStabilized, stabilizedSupports]

theorem ratchetClick_iff_synthesisMass_pos {nuc : SoupNucleus} (s : SoupState nuc) :
    ratchetClick s ↔ 0 < synthesisMass s := by
  simp [ratchetClick, synthesisMass, jRatchetLevel, stabilizedMass, stepSoup]

theorem ratchetClick_of_synthesisMass_pos {nuc : SoupNucleus} (s : SoupState nuc)
    (h : 0 < synthesisMass s) : ratchetClick s :=
  (ratchetClick_iff_synthesisMass_pos (nuc := nuc) s).2 h

theorem carrierSize_step_eq {nuc : SoupNucleus} (s : SoupState nuc) :
    carrierSize (stepSoup s) = carrierSize s := by
  simp [carrierSize, stepSoup, advanceElementsPhases]

theorem jRatchetLevel_step_monotone {nuc : SoupNucleus} (s : SoupState nuc) :
    jRatchetLevel s ≤ jRatchetLevel (stepSoup s) := by
  unfold jRatchetLevel stabilizedMass
  calc
    s.stabilized.length ≤ s.stabilized.length + (newStabilized s).length :=
      Nat.le_add_right _ _
    _ = (stepSoup s).stabilized.length := by
      simp [stepSoup]

theorem entropy_nonincrease_step {nuc : SoupNucleus} (s : SoupState nuc) :
    entropyMetric (stepSoup s) ≤ entropyMetric s := by
  unfold entropyMetric stabilizedMass
  rw [carrierSize_step_eq (nuc := nuc) (s := s)]
  have hle : s.stabilized.length ≤ (stepSoup s).stabilized.length := by
    calc
      s.stabilized.length ≤ s.stabilized.length + (newStabilized s).length :=
        Nat.le_add_right _ _
      _ = (stepSoup s).stabilized.length := by
        simp [stepSoup]
  exact Nat.sub_le_sub_left hle (carrierSize s)

/--
Canonical theorem entrypoint for the three conservation-style laws used in LES:
carrier size invariance, ratchet monotonicity, and entropy non-increase.
-/
theorem three_conservation_laws_bundle {nuc : SoupNucleus} (s : SoupState nuc) :
    carrierSize (stepSoup s) = carrierSize s ∧
      jRatchetLevel s ≤ jRatchetLevel (stepSoup s) ∧
      entropyMetric (stepSoup s) ≤ entropyMetric s := by
  exact ⟨carrierSize_step_eq (nuc := nuc) s,
    jRatchetLevel_step_monotone (nuc := nuc) s,
    entropy_nonincrease_step (nuc := nuc) s⟩

/-- Composition law for fuel-bounded runs. -/
theorem runSoupAux_add {nuc : SoupNucleus} (m n : Nat) (s : SoupState nuc) :
    runSoupAux (m + n) s = runSoupAux n (runSoupAux m s) := by
  induction m generalizing s with
  | zero =>
      simp [runSoupAux]
  | succ m ih =>
      simp [Nat.succ_add, runSoupAux, ih]

/-- Symbiogenesis complexity proxy (stabilized mass) grows monotonically with fuel. -/
theorem symbiogenesis_complexity_growth {nuc : SoupNucleus}
    (fuel : Nat) (s : SoupState nuc) :
    stabilizedMass s ≤ stabilizedMass (runSoupAux fuel s) := by
  induction fuel generalizing s with
  | zero =>
      simp [runSoupAux]
  | succ fuel ih =>
      have hStep : stabilizedMass s ≤ stabilizedMass (stepSoup s) := by
        simpa [jRatchetLevel] using jRatchetLevel_step_monotone (nuc := nuc) s
      have hTail : stabilizedMass (stepSoup s) ≤ stabilizedMass (runSoupAux fuel (stepSoup s)) :=
        ih (s := stepSoup s)
      simpa [runSoupAux] using Nat.le_trans hStep hTail

/-- Run-level monotonicity of the soup-local J-ratchet level from any start state. -/
theorem jRatchetLevel_runSoupAux_monotone {nuc : SoupNucleus}
    (fuel : Nat) (s : SoupState nuc) :
    jRatchetLevel s ≤ jRatchetLevel (runSoupAux fuel s) := by
  simpa [jRatchetLevel, stabilizedMass] using
    (symbiogenesis_complexity_growth (nuc := nuc) fuel s)

/-- If fuel increases, the J-ratchet level cannot decrease. -/
theorem j_ratchet_monotonicity {nuc : SoupNucleus} (s : SoupState nuc) :
    ∀ fuel₁ fuel₂, fuel₁ ≤ fuel₂ →
      jRatchetLevel (runSoupAux fuel₁ s) ≤ jRatchetLevel (runSoupAux fuel₂ s) := by
  intro fuel₁ fuel₂ hle
  rcases Nat.exists_eq_add_of_le hle with ⟨k, hk⟩
  subst hk
  rw [runSoupAux_add]
  exact jRatchetLevel_runSoupAux_monotone (nuc := nuc) k (runSoupAux fuel₁ s)

/-- LES run-levels satisfy the shared `Topos.JRatchet` trajectory contract. -/
theorem jRatchetTrajectory {nuc : SoupNucleus} (s : SoupState nuc) :
    HeytingLean.Topos.JRatchet.RatchetTrajectory
      (fun fuel => jRatchetLevel (runSoupAux fuel s)) := by
  intro fuel₁ fuel₂ hle
  exact j_ratchet_monotonicity (nuc := nuc) s fuel₁ fuel₂ hle

/-- Bridge marker to existing J-ratchet vocabulary; strengthened in WS7/WS8. -/
def alignsWithJRatchetVocabulary {nuc : SoupNucleus} (s : SoupState nuc) : Prop :=
  HeytingLean.Topos.JRatchet.RatchetTrajectory
    (fun fuel => jRatchetLevel (runSoupAux fuel s))

theorem alignsWithJRatchetVocabulary_intro {nuc : SoupNucleus} (s : SoupState nuc) :
    alignsWithJRatchetVocabulary s :=
  jRatchetTrajectory (nuc := nuc) s

end HeytingLean.Genesis.EigenformSoup
