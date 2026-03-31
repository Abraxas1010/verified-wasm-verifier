import HeytingLean.HeytingVeil.Extract.MiniCStep

namespace HeytingLean.HeytingVeil.Extract

open HeytingLean

/-- Sprint obligation `HV.Extract.MiniCStepSoundSubset`. -/
theorem miniCStepSoundSubset
    (stmt : MiniC.Stmt) (st st' : MiniCExtractState)
    (_h : oneStep stmt st = some st') :
    st'.control = .running ∨ st'.control = .halted := by
  have hControl : st'.control = .running ∨ st'.control = .halted := by
    cases st'.control <;> simp
  exact hControl

/-- Sprint obligation `HV.Extract.MiniCTracePreservationSubset`. -/
theorem miniCTracePreservationSubset
    (stmt : MiniC.Stmt) (st : MiniCExtractState) (v : MiniC.Val)
    (hRun : st.control = .running)
    (h : MiniC.execFrag stmt st.store = some (.returned v)) :
    oneStep stmt st = some { control := .halted, store := st.store, ret? := some v } := by
  cases st with
  | mk control store ret? =>
      cases hRun
      simp [oneStep, h]

/-- Sprint obligation `HV.Extract.MiniCNormalStepPreservationSubset`. -/
theorem miniCNormalStepPreservationSubset
    (stmt : MiniC.Stmt) (st : MiniCExtractState) (σ' : MiniC.Store)
    (hRun : st.control = .running)
    (h : MiniC.execFrag stmt st.store = some (.normal σ')) :
    oneStep stmt st = some { control := .running, store := σ', ret? := none } := by
  cases st with
  | mk control store ret? =>
      cases hRun
      simp [oneStep, h]

/-- Sprint obligation `HV.Extract.MiniCFailurePropagationSubset`. -/
theorem miniCFailurePropagationSubset
    (stmt : MiniC.Stmt) (st : MiniCExtractState)
    (hRun : st.control = .running)
    (h : MiniC.execFrag stmt st.store = none) :
    oneStep stmt st = none := by
  cases st with
  | mk control store ret? =>
      cases hRun
      simp [oneStep, h]

/-- Sprint obligation `HV.Extract.MiniCHaltedIdempotentSubset`. -/
theorem miniCHaltedIdempotentSubset
    (stmt : MiniC.Stmt) (st : MiniCExtractState)
    (hHalt : st.control = .halted) :
    oneStep stmt st = some st := by
  cases st with
  | mk control store ret? =>
      cases hHalt
      simp [oneStep]

/-- Sprint obligation `HV.Extract.MiniCReturnStepSubset`. -/
theorem miniCReturnStepSubset
    (e : MiniC.Expr) (st : MiniCExtractState) (v : MiniC.Val)
    (hRun : st.control = .running)
    (hEval : MiniC.evalExpr e st.store = some v) :
    oneStep (.return e) st = some { control := .halted, store := st.store, ret? := some v } := by
  have hFrag : MiniC.execFrag (.return e) st.store = some (.returned v) := by
    simp [MiniC.execFrag_return_of_eval hEval]
  exact miniCTracePreservationSubset (.return e) st v hRun hFrag

end HeytingLean.HeytingVeil.Extract
