import HeytingLean.LambdaIR.NatCompileFragCorrectness
import HeytingLean.LambdaIR.Nat2CompileFragCorrectness
import HeytingLean.MiniC.ToCCorrectness
import HeytingLean.HeytingVeil.Extract.MiniCAdequacy

namespace HeytingLean.HeytingVeil.Route.Witnesses

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.NatFunFragment
open HeytingLean.LambdaIR.Nat2FunFragment

/-- Route witness: LambdaIR nat fragment compilation preserves semantics in MiniC. -/
theorem lambdaIRToMiniCNatFrag
    {funName paramName : String}
    {t : Term [] (Ty.arrow Ty.nat Ty.nat)}
    (ht : IsNatFun t) :
    LambdaIR.NatCompileFrag.NatFunSpecFrag funName paramName t := by
  exact LambdaIR.NatCompileFrag.compileNatFunFrag_correct ht

/-- Route witness: LambdaIR nat2 fragment compilation preserves semantics in MiniC. -/
theorem lambdaIRToMiniCNat2Frag
    {funName : String}
    {t : Term [] (Ty.arrow Ty.nat (Ty.arrow Ty.nat Ty.nat))}
    (ht : IsNat2Fun t) :
    LambdaIR.Nat2CompileFrag.Nat2FunSpec
      funName
      LambdaIR.Nat2CompileFragCorrectness.param1
      LambdaIR.Nat2CompileFragCorrectness.param2
      (fun x y => LambdaIR.evalClosed
        (Term.app (Term.app t (Term.constNat x)) (Term.constNat y)))
      t := by
  refine LambdaIR.Nat2CompileFragCorrectness.compileNat2FunFrag_correct
      (t := t) (funName := funName) ht
      (leanF := fun x y => LambdaIR.evalClosed
        (Term.app (Term.app t (Term.constNat x)) (Term.constNat y)))
      ?_
  intro x y
  rfl

/-- Route witness: MiniC nat-fragment runner semantics are preserved by C compilation. -/
theorem miniCToCRunNatFrag
    (fn : MiniC.Fun) (paramName : String) (n out : Nat)
    (h : MiniC.runNatFunFrag fn paramName n = some out) :
    C.runCFunFrag (MiniC.ToC.compileFun fn) [Int.ofNat n] = some (Int.ofNat out) := by
  exact MiniC.ToC.runNatFunFrag_correct_toC fn paramName n out h

/-- Route witness: HeytingVeil MiniC extraction return-step bridge is preserved. -/
theorem heytingVeilMiniCReturnBridge
    (stmt : MiniC.Stmt) (st : HeytingLean.HeytingVeil.Extract.MiniCExtractState) (v : MiniC.Val)
    (hRun : st.control = .running)
    (h : MiniC.execFrag stmt st.store = some (.returned v)) :
    HeytingLean.HeytingVeil.Extract.oneStep stmt st
      = some { control := .halted, store := st.store, ret? := some v } := by
  exact HeytingLean.HeytingVeil.Extract.miniCTracePreservationSubset stmt st v hRun h

/-- Route witness: HeytingVeil MiniC extraction normal-step bridge is preserved. -/
theorem heytingVeilMiniCNormalBridge
    (stmt : MiniC.Stmt) (st : HeytingLean.HeytingVeil.Extract.MiniCExtractState) (σ' : MiniC.Store)
    (hRun : st.control = .running)
    (h : MiniC.execFrag stmt st.store = some (.normal σ')) :
    HeytingLean.HeytingVeil.Extract.oneStep stmt st
      = some { control := .running, store := σ', ret? := none } := by
  exact HeytingLean.HeytingVeil.Extract.miniCNormalStepPreservationSubset stmt st σ' hRun h

/-- Route witness: HeytingVeil MiniC extraction failure propagation is preserved. -/
theorem heytingVeilMiniCFailureBridge
    (stmt : MiniC.Stmt) (st : HeytingLean.HeytingVeil.Extract.MiniCExtractState)
    (hRun : st.control = .running)
    (h : MiniC.execFrag stmt st.store = none) :
    HeytingLean.HeytingVeil.Extract.oneStep stmt st = none := by
  exact HeytingLean.HeytingVeil.Extract.miniCFailurePropagationSubset stmt st hRun h

/-- Route witness: HeytingVeil MiniC extraction halted-state idempotence is preserved. -/
theorem heytingVeilMiniCHaltedBridge
    (stmt : MiniC.Stmt) (st : HeytingLean.HeytingVeil.Extract.MiniCExtractState)
    (hHalt : st.control = .halted) :
    HeytingLean.HeytingVeil.Extract.oneStep stmt st = some st := by
  exact HeytingLean.HeytingVeil.Extract.miniCHaltedIdempotentSubset stmt st hHalt

end HeytingLean.HeytingVeil.Route.Witnesses
