import HeytingLean.HeytingVeil.HighIR.Semantics

namespace HeytingLean.HeytingVeil.HighIR.ToRust

/-- Minimal semantic state model for planned HighIR->Rust bridge contracts. -/
abbrev HighIRState : Type := HeytingLean.HeytingVeil.HighIR.Semantics.HighIRState

/-- Conserved-balance relation used by planned Rust preservation bridge contracts. -/
def preservesConservation (pre post : HighIRState) : Prop :=
  HeytingLean.HeytingVeil.HighIR.Semantics.preservesConservation pre post

/-- Current planned ToRust bridge instruction selector. -/
def plannedInstruction : HeytingLean.HeytingVeil.HighIR.Semantics.HighIRInstr :=
  HeytingLean.HeytingVeil.HighIR.Semantics.transferInstr

/-- Planned transition scaffold for HighIR->Rust bridge modeling. -/
def plannedStep (pre post : HighIRState) (code : Int) : Prop :=
  HeytingLean.HeytingVeil.HighIR.Semantics.execInstr plannedInstruction pre post code

/-- Planned contract: HighIR->Rust lowering preserves tracked conservation payload. -/
def highIRToRustPreservationCondition : Prop :=
  ∀ pre post code, plannedStep pre post code -> preservesConservation pre post

/-- Sprint obligation `HV.HighIR.ToRust.PreservationBridge`. -/
theorem highIRToRustPreservationBridge : highIRToRustPreservationCondition := by
  intro pre post code hStep
  simpa [plannedStep, preservesConservation, plannedInstruction] using
    (HeytingLean.HeytingVeil.HighIR.Semantics.execTransferPreservesConservation hStep)

/-- Planned contract: nonzero planned Rust bridge failure codes remain negative. -/
def highIRToRustFailureCondition : Prop :=
  ∀ pre post code, plannedStep pre post code -> code ≠ 0 -> code < 0

/-- Sprint obligation `HV.HighIR.ToRust.FailureBridge`. -/
theorem highIRToRustFailureBridge : highIRToRustFailureCondition := by
  intro pre post code hStep hCodeNeZero
  simpa [plannedStep, plannedInstruction] using
    (HeytingLean.HeytingVeil.HighIR.Semantics.execTransferNonzeroCodeNegative hStep hCodeNeZero)

end HeytingLean.HeytingVeil.HighIR.ToRust
