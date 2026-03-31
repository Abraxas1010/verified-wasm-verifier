import HeytingLean.Genesis.EigenformSoup.Stabilization

/-!
# Genesis.EigenformSoup.Runner

WS5 deterministic soup runner and certified wrapper.
-/

namespace HeytingLean.Genesis.EigenformSoup

/-- Runtime configuration for deterministic soup execution. -/
structure SoupConfig where
  substrate : SubstrateConfig := {}
  fuel : Nat := 16
deriving Repr

/-- Runtime state for one soup execution. -/
structure SoupState (nuc : SoupNucleus) where
  epoch : Nat
  substrate : Substrate nuc
  stabilized : List Support

/-- Minimal runtime statistics for reporting and extraction metadata. -/
structure SoupStats where
  steps : Nat
  stabilizedCount : Nat
deriving Repr

/-- One trace snapshot point intended for serialization/export. -/
structure TraceSnapshot where
  epoch : Nat
  stabilizedCount : Nat
  unresolvedCount : Nat
  jLevel : Nat
deriving Repr

/-- Initial state for a given soup configuration. -/
noncomputable def initState (nuc : SoupNucleus) (cfg : SoupConfig) : SoupState nuc :=
  { epoch := 0
    substrate := buildSubstrate nuc cfg.substrate
    stabilized := [] }

/-- Scheduled interaction events for the current state. -/
def scheduledEvents {nuc : SoupNucleus} (s : SoupState nuc) : List (InteractionEvent nuc) :=
  runSchedule s.substrate

/-- Newly stabilized supports extracted at the current epoch. -/
def newStabilized {nuc : SoupNucleus} (s : SoupState nuc) : List Support :=
  stabilizedSupports nuc (scheduledEvents s)

/-- One deterministic soup step. -/
def stepSoup {nuc : SoupNucleus} (s : SoupState nuc) : SoupState nuc :=
  { epoch := s.epoch + 1
    substrate :=
      { s.substrate with
        elements := advanceElementsPhases s.substrate.elements }
    stabilized := s.stabilized ++ newStabilized s }

/-- Fuel-bounded deterministic soup execution. -/
def runSoupAux {nuc : SoupNucleus} : Nat → SoupState nuc → SoupState nuc
  | 0, s => s
  | Nat.succ fuel, s => runSoupAux fuel (stepSoup s)

/-- Fuel-bounded deterministic trace (includes the initial state). -/
def runSoupTraceAux {nuc : SoupNucleus} : Nat → SoupState nuc → List (SoupState nuc)
  | 0, s => [s]
  | Nat.succ fuel, s => s :: runSoupTraceAux fuel (stepSoup s)

/-- Run soup from initial state using configured fuel budget. -/
noncomputable def runSoup (nuc : SoupNucleus) (cfg : SoupConfig) : SoupState nuc :=
  runSoupAux cfg.fuel (initState nuc cfg)

/-- Run soup trace from initial state using configured fuel budget. -/
noncomputable def runSoupTrace (nuc : SoupNucleus) (cfg : SoupConfig) : List (SoupState nuc) :=
  runSoupTraceAux cfg.fuel (initState nuc cfg)

/-- Summarize final state into compact stats. -/
def summarizeStats {nuc : SoupNucleus} (s : SoupState nuc) : SoupStats :=
  { steps := s.epoch
    stabilizedCount := s.stabilized.length }

/-- Unresolved carrier mass for one state. -/
def unresolvedCount {nuc : SoupNucleus} (s : SoupState nuc) : Nat :=
  s.substrate.elements.length - s.stabilized.length

/-- Snapshot projection for one state. -/
def snapshotOfState {nuc : SoupNucleus} (s : SoupState nuc) : TraceSnapshot :=
  { epoch := s.epoch
    stabilizedCount := s.stabilized.length
    unresolvedCount := unresolvedCount s
    jLevel := s.stabilized.length }

/-- Snapshot projection for a whole finite trace. -/
def snapshotsOfTrace {nuc : SoupNucleus} (trace : List (SoupState nuc)) : List TraceSnapshot :=
  trace.map snapshotOfState

/-- Config-driven snapshot projection for deterministic runs. -/
noncomputable def runSoupTraceSnapshots (nuc : SoupNucleus) (cfg : SoupConfig) : List TraceSnapshot :=
  snapshotsOfTrace (runSoupTrace nuc cfg)

/-- Cheap scalar checksum for trace payload parity scaffolding. -/
def traceSnapshotChecksum (xs : List TraceSnapshot) : Nat :=
  xs.foldl (fun acc x => acc + x.jLevel + x.stabilizedCount + x.unresolvedCount) 0

theorem stepSoup_epoch_succ {nuc : SoupNucleus} (s : SoupState nuc) :
    (stepSoup s).epoch = s.epoch + 1 := rfl

theorem stepSoup_preserves_eigenforms
    {nuc : SoupNucleus}
    (s : SoupState nuc)
    (hPrev : ∀ S, S ∈ s.stabilized → isEigenform nuc S) :
    ∀ S, S ∈ (stepSoup s).stabilized → isEigenform nuc S := by
  intro S hS
  have hSplit : S ∈ s.stabilized ∨ S ∈ newStabilized s := by
    simpa [stepSoup] using hS
  cases hSplit with
  | inl hOld =>
      exact hPrev S hOld
  | inr hNew =>
      exact supports_from_interactions_are_eigenforms
        (nuc := nuc)
        (events := scheduledEvents s)
        (S := S)
        (by simpa [newStabilized, scheduledEvents] using hNew)

theorem runSoupAux_preserves_eigenforms
    {nuc : SoupNucleus}
    (fuel : Nat)
    (s : SoupState nuc)
    (hPrev : ∀ S, S ∈ s.stabilized → isEigenform nuc S) :
    ∀ S, S ∈ (runSoupAux fuel s).stabilized → isEigenform nuc S := by
  induction fuel generalizing s with
  | zero =>
      simpa [runSoupAux] using hPrev
  | succ fuel ih =>
      have hStep : ∀ S, S ∈ (stepSoup s).stabilized → isEigenform nuc S :=
        stepSoup_preserves_eigenforms (nuc := nuc) s hPrev
      simpa [runSoupAux] using ih (s := stepSoup s) hStep

/-- Global soundness for deterministic runs: all stabilized supports are eigenforms. -/
theorem runSoup_sound
    (nuc : SoupNucleus)
    (cfg : SoupConfig)
    (S : Support)
    (hS : S ∈ (runSoup nuc cfg).stabilized) :
    isEigenform nuc S := by
  unfold runSoup at hS
  exact runSoupAux_preserves_eigenforms
    (nuc := nuc)
    (fuel := cfg.fuel)
    (s := initState nuc cfg)
    (hPrev := by
      intro T hT
      simp [initState] at hT)
    S
    hS

theorem runSoupTraceAux_length {nuc : SoupNucleus} (fuel : Nat) (s : SoupState nuc) :
    (runSoupTraceAux fuel s).length = fuel + 1 := by
  induction fuel generalizing s with
  | zero =>
      simp [runSoupTraceAux]
  | succ fuel ih =>
      simp [runSoupTraceAux, ih]

theorem runSoupTrace_length (nuc : SoupNucleus) (cfg : SoupConfig) :
    (runSoupTrace nuc cfg).length = cfg.fuel + 1 := by
  simp [runSoupTrace, runSoupTraceAux_length]

theorem snapshotsOfTrace_length {nuc : SoupNucleus} (trace : List (SoupState nuc)) :
    (snapshotsOfTrace trace).length = trace.length := by
  simp [snapshotsOfTrace]

theorem runSoupTraceSnapshots_length (nuc : SoupNucleus) (cfg : SoupConfig) :
    (runSoupTraceSnapshots nuc cfg).length = cfg.fuel + 1 := by
  simp [runSoupTraceSnapshots, snapshotsOfTrace_length, runSoupTrace_length]

theorem runSoupAux_mem_runSoupTraceAux {nuc : SoupNucleus} (fuel : Nat) (s : SoupState nuc) :
    runSoupAux fuel s ∈ runSoupTraceAux fuel s := by
  induction fuel generalizing s with
  | zero =>
      simp [runSoupAux, runSoupTraceAux]
  | succ fuel ih =>
      simp [runSoupAux, runSoupTraceAux]
      exact Or.inr (ih (s := stepSoup s))

/-- Certified deterministic soup run packaged with a global soundness witness. -/
structure CertifiedSoup (nuc : SoupNucleus) where
  finalState : SoupState nuc
  stats : SoupStats
  allEigenforms : ∀ S, S ∈ finalState.stabilized → isEigenform nuc S

/-- Construct a certified run bundle from a configuration. -/
noncomputable def certifyRun (nuc : SoupNucleus) (cfg : SoupConfig) : CertifiedSoup nuc :=
  let finalState := runSoup nuc cfg
  { finalState := finalState
    stats := summarizeStats finalState
    allEigenforms := by
      intro S hS
      exact runSoup_sound nuc cfg S hS }

end HeytingLean.Genesis.EigenformSoup
