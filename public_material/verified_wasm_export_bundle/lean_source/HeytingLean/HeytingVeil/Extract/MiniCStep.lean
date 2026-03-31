import HeytingLean.HeytingVeil.Extract.MiniCState

namespace HeytingLean.HeytingVeil.Extract

open HeytingLean

def oneStep (stmt : MiniC.Stmt) (st : MiniCExtractState) : Option MiniCExtractState :=
  match st.control with
  | .halted => some st
  | .running =>
      match MiniC.execFrag stmt st.store with
      | some (.returned v) => some { control := .halted, store := st.store, ret? := some v }
      | some (.normal σ') => some { control := .running, store := σ', ret? := none }
      | none => none

end HeytingLean.HeytingVeil.Extract
