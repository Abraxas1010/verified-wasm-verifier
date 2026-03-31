import HeytingLean.HeytingVeil.HighIR.Semantics

namespace HeytingLean.HeytingVeil.HighIR.ToC

/-- Minimal semantic state model for preview HighIR->C bridge contracts. -/
abbrev HighIRState : Type := HeytingLean.HeytingVeil.HighIR.Semantics.HighIRState

/-- Conserved-balance relation used by preview preservation bridge contracts. -/
def preservesConservation (pre post : HighIRState) : Prop :=
  HeytingLean.HeytingVeil.HighIR.Semantics.preservesConservation pre post

/-- Current preview ToC bridge instruction selector. -/
def previewInstruction : HeytingLean.HeytingVeil.HighIR.Semantics.HighIRInstr :=
  HeytingLean.HeytingVeil.HighIR.Semantics.transferInstr

/--
Preview transition scaffold for HighIR->C bridge modeling.

Current preview model delegates to `HighIR.Semantics.execInstr previewInstruction`.
-/
def previewStep (pre post : HighIRState) (code : Int) : Prop :=
  HeytingLean.HeytingVeil.HighIR.Semantics.execInstr previewInstruction pre post code

/--
Preview contract: HighIR->C lowering preserves the tracked operational payload
for the currently modeled fragment. This is a placeholder bridge theorem surface
that can be refined as concrete HighIR lowering semantics land.
-/
def highIRToCPreservationCondition : Prop :=
  ∀ pre post code, previewStep pre post code -> preservesConservation pre post

/-- Sprint obligation `HV.HighIR.ToC.PreservationBridge`. -/
theorem highIRToCPreservationBridge : highIRToCPreservationCondition := by
  intro pre post code hStep
  simpa [previewStep, preservesConservation, previewInstruction] using
    (HeytingLean.HeytingVeil.HighIR.Semantics.execTransferPreservesConservation hStep)

/--
Preview contract: HighIR->C lowering exposes a deterministic failure bridge for
non-preserving executions. This remains a conservative placeholder surface.
-/
def highIRToCFailureCondition : Prop :=
  ∀ pre post code, previewStep pre post code -> code ≠ 0 -> code < 0

/-- Sprint obligation `HV.HighIR.ToC.FailureBridge`. -/
theorem highIRToCFailureBridge : highIRToCFailureCondition := by
  intro pre post code hStep hCodeNeZero
  simpa [previewStep, previewInstruction] using
    (HeytingLean.HeytingVeil.HighIR.Semantics.execTransferNonzeroCodeNegative hStep hCodeNeZero)

end HeytingLean.HeytingVeil.HighIR.ToC
