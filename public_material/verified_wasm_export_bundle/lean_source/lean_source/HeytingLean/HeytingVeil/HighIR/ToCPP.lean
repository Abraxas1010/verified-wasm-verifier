import HeytingLean.HeytingVeil.HighIR.Semantics

namespace HeytingLean.HeytingVeil.HighIR.ToCPP

/-- Minimal semantic state model for planned HighIR->CPP bridge contracts. -/
abbrev HighIRState : Type := HeytingLean.HeytingVeil.HighIR.Semantics.HighIRState

/-- Conserved-balance relation used by planned CPP preservation bridge contracts. -/
def preservesConservation (pre post : HighIRState) : Prop :=
  HeytingLean.HeytingVeil.HighIR.Semantics.preservesConservation pre post

/-- Current planned ToCPP bridge instruction selector. -/
def plannedInstruction : HeytingLean.HeytingVeil.HighIR.Semantics.HighIRInstr :=
  HeytingLean.HeytingVeil.HighIR.Semantics.transferInstr

/-- Planned transition scaffold for HighIR->CPP bridge modeling. -/
def plannedStep (pre post : HighIRState) (code : Int) : Prop :=
  HeytingLean.HeytingVeil.HighIR.Semantics.execInstr plannedInstruction pre post code

/-- Planned contract: HighIR->CPP lowering preserves tracked conservation payload. -/
def highIRToCPPPreservationCondition : Prop :=
  ∀ pre post code, plannedStep pre post code -> preservesConservation pre post

/-- Sprint obligation `HV.HighIR.ToCPP.PreservationBridge`. -/
theorem highIRToCPPPreservationBridge : highIRToCPPPreservationCondition := by
  intro pre post code hStep
  simpa [plannedStep, preservesConservation, plannedInstruction] using
    (HeytingLean.HeytingVeil.HighIR.Semantics.execTransferPreservesConservation hStep)

/-- Planned contract: nonzero planned CPP bridge failure codes remain negative. -/
def highIRToCPPFailureCondition : Prop :=
  ∀ pre post code, plannedStep pre post code -> code ≠ 0 -> code < 0

/-- Sprint obligation `HV.HighIR.ToCPP.FailureBridge`. -/
theorem highIRToCPPFailureBridge : highIRToCPPFailureCondition := by
  intro pre post code hStep hCodeNeZero
  simpa [plannedStep, plannedInstruction] using
    (HeytingLean.HeytingVeil.HighIR.Semantics.execTransferNonzeroCodeNegative hStep hCodeNeZero)

end HeytingLean.HeytingVeil.HighIR.ToCPP
