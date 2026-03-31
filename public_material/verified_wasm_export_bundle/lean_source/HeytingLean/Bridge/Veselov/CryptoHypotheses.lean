import Mathlib

/-!
# Bridge.Veselov.CryptoHypotheses

Assumption-first hypotheses for cryptographic/discrete number-theory sections.
All numerically strong claims are represented as explicit assumptions and
monotonicity-style obligations rather than hard theorems.
-/

namespace HeytingLean.Bridge.Veselov

universe u

/-- Generic sieve hypothesis contract used for complexity-side claims. -/
structure SieveHypothesis (α : Type u) where
  predicate : α → Prop
  [decPred : DecidablePred predicate]
  nonemptyDomain : Nonempty α
  prevalence : ∀ x, 0 ≤ (if predicate x then 1 else 0 : ℝ)

/-- Complexity-trap contrast contract: constraints can dominate naive hardness. -/
structure TrapConstraint (S : Type u) where
  rawCost : S → ℝ
  constrainedCost : S → ℝ
  nonnegRaw : ∀ s, 0 ≤ rawCost s
  nonnegConstrained : ∀ s, 0 ≤ constrainedCost s
  trapReduction : ∀ s, constrainedCost s ≤ rawCost s

/-- A constrained instance can only improve or retain complexity under the contract.
This keeps the theorem statement aligned with the Trap/Constraint principle.
-/
theorem trap_reduces_complexity (S : Type u) (C : TrapConstraint S) (s : S) :
    C.constrainedCost s ≤ C.rawCost s := C.trapReduction s

/-- Nonnegativity of constrained complexity is explicit in this interface. -/
theorem trap_complexity_nonneg (S : Type u) (C : TrapConstraint S) (s : S) :
    0 ≤ C.constrainedCost s := C.nonnegConstrained s

/-- p-rough shift hypothesis encoded as explicit lower/bound functions.
This stays assumption-first and does not assert unproved asymptotics.
-/
structure PRoughShiftHypothesis where
  roughLower : ℕ → ℝ
  roughBound : ℕ → ℝ
  roughLowerNonneg : ∀ x, 0 ≤ roughLower x
  roughLowerLeBound : ∀ x, roughLower x ≤ roughBound x

theorem roughBound_nonneg (H : PRoughShiftHypothesis) (x : ℕ) :
    0 ≤ H.roughBound x := by
  exact le_trans (H.roughLowerNonneg x) (H.roughLowerLeBound x)

/-- Factorization benchmark record (empirical lane only). -/
structure FactorizationBenchmark where
  modulusBits : ℕ
  runtimeSeconds : ℝ
  runtimeNonneg : 0 ≤ runtimeSeconds
  success : Bool
  provenanceHash : String
  backendId : String

/-- Runtime normalized by a defensive nonzero denominator. -/
noncomputable def runtimePerBit (B : FactorizationBenchmark) : ℝ :=
  B.runtimeSeconds / max (1 : ℝ) (B.modulusBits : ℝ)

theorem runtimePerBit_nonneg (B : FactorizationBenchmark) :
    0 ≤ runtimePerBit B := by
  dsimp [runtimePerBit]
  have hden_pos : 0 < max (1 : ℝ) (B.modulusBits : ℝ) := by
    exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  exact div_nonneg B.runtimeNonneg (le_of_lt hden_pos)

/-- Algorithm-stub API for controlled benchmark wiring. -/
structure FactorizationAlgorithmStub where
  name : String
  run : ℕ → FactorizationBenchmark

/-- Evidence package contract for runtime-facing claims. -/
structure CryptoEvidencePackage where
  benches : List FactorizationBenchmark
  provenanceComplete : ∀ b ∈ benches, b.provenanceHash ≠ ""

/-- Any successful package witness implies the benchmark list is nonempty. -/
theorem success_implies_nonempty (P : CryptoEvidencePackage)
    (h : ∃ b ∈ P.benches, b.success = true) :
    P.benches ≠ [] := by
  intro hempty
  rcases h with ⟨b, hb, _⟩
  simp [hempty] at hb

end HeytingLean.Bridge.Veselov
