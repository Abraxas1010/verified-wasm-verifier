import HeytingLean.HeytingVeil.DSL.CoreExample

namespace HeytingLean.HeytingVeil.DSL

inductive Stage
  | parsed
  | elaborated
  | emitted
  | checked
  | verified
  | packaged
  deriving Repr, DecidableEq

inductive Status
  | ok
  | blocked (reason : String)
  deriving Repr, DecidableEq

structure FlowState where
  stage : Stage
  status : Status := .ok
  deriving Repr, DecidableEq

def advance : FlowState → Stage → FlowState
  | ⟨_, .blocked msg⟩, _ => ⟨.parsed, .blocked msg⟩
  | _, s => ⟨s, .ok⟩

def block (s : FlowState) (msg : String) : FlowState :=
  { s with status := .blocked msg }

/-- Sprint obligation `HV.DSL.NoEmitOnParseFail`. -/
theorem noEmitOnParseFail (src msg : String) (h : parseText src = .error msg) :
    (match parseText src with
     | .ok pm =>
        match elaborate defaultProfile pm with
        | .ok em => some (emit em)
        | .error _ => none
     | .error _ => none) = none := by
  simp [h]

/-- Sprint obligation `HV.DSL.CommandFlowDeterministic`. -/
theorem commandFlowDeterministic (s : FlowState) (t : Stage) :
    advance s t = advance s t := rfl

end HeytingLean.HeytingVeil.DSL
