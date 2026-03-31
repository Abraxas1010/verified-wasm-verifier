import HeytingLean.Bridge.Veselov.Consciousness

/-!
# Bridge.Veselov.ConsciousnessPhaseDiagram

Scoped OP05 bridge surface:
phase predicates (`K+`, boundary, `K-`) over curvature regimes with explicit
partition and separation theorems.
-/

namespace HeytingLean.Bridge.Veselov

/-- `K+` phase (high/expansive regime). -/
def KPlus (g : GapStatus) : Prop :=
  neuralCurveRegime g = (3 : RatchetStage)

/-- Boundary phase (critical regime). -/
def KBoundary (g : GapStatus) : Prop :=
  neuralCurveRegime g = (1 : RatchetStage)

/-- `K-` phase (contractive/stable regime). -/
def KMinus (g : GapStatus) : Prop :=
  neuralCurveRegime g = (0 : RatchetStage)

/-- Every qualitative regime lies in exactly one scoped phase bucket. -/
theorem phase_partition (g : GapStatus) :
    KPlus g ∨ KBoundary g ∨ KMinus g := by
  cases g <;> simp [KPlus, KBoundary, KMinus, neuralCurveRegime]

/-- `K+` and `K-` are disjoint in the scoped phase diagram. -/
theorem kplus_kminus_disjoint (g : GapStatus) :
    ¬ (KPlus g ∧ KMinus g) := by
  cases g <;> simp [KPlus, KMinus, neuralCurveRegime]

/-- Open curvature status always maps into `K+`. -/
theorem open_status_in_kplus (κ : Int)
    (h : statusOfCurvature κ = GapStatus.open) :
    KPlus (statusOfCurvature κ) := by
  simp [KPlus, neuralCurveRegime, h]

/-- Closed curvature status always maps into `K-`. -/
theorem closed_status_in_kminus (κ : Int)
    (h : statusOfCurvature κ = GapStatus.closed) :
    KMinus (statusOfCurvature κ) := by
  simp [KMinus, neuralCurveRegime, h]

/-- Critical curvature status maps to the phase boundary. -/
theorem critical_status_in_boundary (κ : Int)
    (h : statusOfCurvature κ = GapStatus.critical) :
    KBoundary (statusOfCurvature κ) := by
  simp [KBoundary, neuralCurveRegime, h]

/--
Packaged OP05 scoped theorem:
- phase partition (`K+`, boundary, `K-`) is exhaustive,
- and `K+`/`K-` separation is explicit.
-/
theorem op05_scoped_phase_theorem (g : GapStatus) :
    (KPlus g ∨ KBoundary g ∨ KMinus g) ∧ ¬ (KPlus g ∧ KMinus g) := by
  exact ⟨phase_partition g, kplus_kminus_disjoint g⟩

end HeytingLean.Bridge.Veselov
