namespace HeytingLean.HeytingVeil.HighIR.Semantics

/-- Minimal semantic state model for preview HighIR execution. -/
abbrev HighIRState : Type := String -> Int

/-- Conserved-balance relation over transfer endpoints. -/
def preservesConservation (pre post : HighIRState) : Prop :=
  post "srcBal" + post "dstBal" = pre "srcBal" + pre "dstBal"

/-- Preview HighIR operation family (to be expanded with concrete IR ops). -/
inductive HighIROp where
  | transfer
  | halt
deriving DecidableEq, Repr

/--
Single-step HighIR execution relation for the current preview fragment.
- `transfer` succeeds with code `0` when `amount <= srcBal`, else fails with `-1`.
- `halt` is a no-op success used as a neutral control marker.
-/
def step (op : HighIROp) (pre post : HighIRState) (code : Int) : Prop :=
  match op with
  | .transfer =>
      if pre "amount" <= pre "srcBal" then
        code = 0 ∧ post = pre
      else
        code = -1 ∧ post = pre
  | .halt =>
      code = 0 ∧ post = pre

/--
Concrete preview instruction fragment:
- operation-backed instructions,
- explicit fail-fast instruction for deterministic negative-code paths.
-/
inductive HighIRInstr where
  | op (opcode : HighIROp)
  | failFast (failCode : Int)
deriving DecidableEq, Repr

/-- Execute one preview instruction. -/
def execInstr (instr : HighIRInstr) (pre post : HighIRState) (code : Int) : Prop :=
  match instr with
  | .op opcode =>
      step opcode pre post code
  | .failFast failCode =>
      failCode < 0 ∧ code = failCode ∧ post = pre

/-- Canonical preview transfer instruction. -/
def transferInstr : HighIRInstr := .op .transfer

/-- Transfer step preserves endpoint-balance conservation. -/
theorem transferStepPreservesConservation {pre post : HighIRState} {code : Int}
    (hStep : step .transfer pre post code) : preservesConservation pre post := by
  by_cases hGuard : pre "amount" <= pre "srcBal"
  · simp [step, hGuard] at hStep
    rcases hStep with ⟨_, rfl⟩
    simp [preservesConservation]
  · simp [step, hGuard] at hStep
    rcases hStep with ⟨_, rfl⟩
    simp [preservesConservation]

/-- Transfer step failure codes are deterministically negative when nonzero. -/
theorem transferStepNonzeroCodeNegative {pre post : HighIRState} {code : Int}
    (hStep : step .transfer pre post code) (hCodeNeZero : code ≠ 0) : code < 0 := by
  by_cases hGuard : pre "amount" <= pre "srcBal"
  · simp [step, hGuard] at hStep
    rcases hStep with ⟨hCodeZero, _⟩
    exact False.elim (hCodeNeZero hCodeZero)
  · simp [step, hGuard] at hStep
    rcases hStep with ⟨hCodeNegOne, _⟩
    have hNegOne : (-1 : Int) < 0 := by decide
    rw [hCodeNegOne]
    exact hNegOne

/-- Conservation bridge for the preview transfer instruction fragment. -/
theorem execTransferPreservesConservation {pre post : HighIRState} {code : Int}
    (hExec : execInstr transferInstr pre post code) : preservesConservation pre post := by
  simpa [execInstr, transferInstr] using transferStepPreservesConservation hExec

/-- Failure-polarity bridge for the preview transfer instruction fragment. -/
theorem execTransferNonzeroCodeNegative {pre post : HighIRState} {code : Int}
    (hExec : execInstr transferInstr pre post code) (hCodeNeZero : code ≠ 0) : code < 0 := by
  simpa [execInstr, transferInstr] using transferStepNonzeroCodeNegative hExec hCodeNeZero

end HeytingLean.HeytingVeil.HighIR.Semantics
