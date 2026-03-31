import HeytingLean.LeanCP.Compile.SKYLoweringSemantics
import HeytingLean.LoF.Combinators.SKYReducerGPUWrapper

namespace HeytingLean
namespace LeanCP
namespace Compile
namespace SKYReducerGPUWrapperLowering

open HeytingLean.LoF.Combinators.SKYReducerKernel
open HeytingLean.LoF.Combinators.SKYReducerGPUWrapper
open SKYLoweringSemantics

abbrev KernelState := HeytingLean.LoF.Combinators.SKYReducerKernel.State
abbrev BoundedState := HeytingLean.LoF.Combinators.SKYMachineBounded.State Nat

def packedStep? (s : KernelState) (oracleVals : Array Int) :
    Option (StepStatus × WrapperState) := do
  let packed ← ofKernelState? s
  step? (SKYLoweringSemantics.oracleArrayEval oracleVals) packed

def packedExpectedStep? (s : KernelState) (oracleVals : Array Int) :
    Option (StepStatus × WrapperState) := do
  let _packed ← ofKernelState? s
  let result := step (SKYLoweringSemantics.oracleArrayEval oracleVals) s
  let packed' ← ofKernelState? result.state
  pure (result.status, packed')

def packedRunLoweredStep? (s : KernelState) (oracleVals : Array Int) :
    Option (StepStatus × WrapperState) := do
  let _packed ← ofKernelState? s
  let result ← runLoweredStep? s oracleVals
  let packed' ← ofKernelState? result.2
  pure (result.1, packed')

def packedRunFuel? (fuel : Nat) (s : KernelState) (oracleVals : Array Int) :
    Option (StepStatus × WrapperState) := do
  let packed ← ofKernelState? s
  runFuel? (SKYLoweringSemantics.oracleArrayEval oracleVals) fuel packed

def packedExpectedRunFuel? (fuel : Nat) (s : KernelState) (oracleVals : Array Int) :
    Option (StepStatus × WrapperState) :=
  match fuel with
  | 0 => do
      let packed ← ofKernelState? s
      pure (.halted, packed)
  | fuel + 1 =>
      match packedExpectedStep? s oracleVals with
      | some (.progress, packed') => do
          let core ← toKernelState? packed'
          packedExpectedRunFuel? fuel core oracleVals
      | some result => some result
      | none => none

def packedRunLoweredFuel? (fuel : Nat) (s : KernelState) (oracleVals : Array Int) :
    Option (StepStatus × WrapperState) :=
  match fuel with
  | 0 => do
      let packed ← ofKernelState? s
      pure (.halted, packed)
  | fuel + 1 =>
      match packedRunLoweredStep? s oracleVals with
      | some (.progress, packed') => do
          let core ← toKernelState? packed'
          packedRunLoweredFuel? fuel core oracleVals
      | some result => some result
      | none => none

private theorem stack_le_maxNodes_of_ofKernelState?_eq_some
    (s : KernelState) {packed : WrapperState}
    (hpack : ofKernelState? s = some packed) :
    s.stack.length ≤ s.maxNodes := by
  by_cases hnode : s.nodeCount ≤ s.maxNodes
  · by_cases hstack : s.stack.length ≤ s.maxNodes
    · exact hstack
    · simp [ofKernelState?, hnode, hstack] at hpack
  · simp [ofKernelState?, hnode] at hpack

private theorem toKernelState?_of_ofKernelState?_eq_some
    (s : KernelState) (hwf : s.WellFormed) {packed : WrapperState}
    (hpack : ofKernelState? s = some packed) :
    toKernelState? packed = some s := by
  have hstack := stack_le_maxNodes_of_ofKernelState?_eq_some s hpack
  have hround := toKernelState?_ofKernelState?_wellFormed s hwf hstack
  simpa [hpack] using hround

theorem packedExpectedStep?_eq_packedStep?
    (s : KernelState) (oracleVals : Array Int) (hwf : s.WellFormed) :
    packedExpectedStep? s oracleVals = packedStep? s oracleVals := by
  unfold packedExpectedStep? packedStep? step?
  cases hpack : ofKernelState? s with
  | none =>
      simp [hpack]
  | some packed =>
      have hround : toKernelState? packed = some s := by
        exact toKernelState?_of_ofKernelState?_eq_some s hwf hpack
      simp [hpack, hround]

theorem packedRunLoweredStep?_eq_packedExpectedStep?
    (s : KernelState) (oracleVals : Array Int) (hwf : s.WellFormed) :
    packedRunLoweredStep? s oracleVals = packedExpectedStep? s oracleVals := by
  unfold packedRunLoweredStep? packedExpectedStep?
  rw [runLoweredStep?_eq_expectedStep? s oracleVals hwf]
  simp [expectedStep?]

theorem packedRunLoweredStep?_eq_packedStep?
    (s : KernelState) (oracleVals : Array Int) (hwf : s.WellFormed) :
    packedRunLoweredStep? s oracleVals = packedStep? s oracleVals := by
  rw [packedRunLoweredStep?_eq_packedExpectedStep? s oracleVals hwf]
  exact packedExpectedStep?_eq_packedStep? s oracleVals hwf

private theorem packedExpectedRunFuel?_eq_packedRunFuel_ofKernelState
    (fuel : Nat) (s : KernelState) (oracleVals : Array Int) (hwf : s.WellFormed) :
    packedExpectedRunFuel? fuel s oracleVals = packedRunFuel? fuel s oracleVals := by
  induction fuel generalizing s with
  | zero =>
      unfold packedExpectedRunFuel? packedRunFuel? runFuel?
      simp
  | succ fuel ih =>
      unfold packedExpectedRunFuel? packedRunFuel? runFuel?
      cases hpack : ofKernelState? s with
      | none =>
          simp [packedExpectedStep?, packedStep?, hpack]
      | some packed =>
          have hround : toKernelState? packed = some s := by
            exact toKernelState?_of_ofKernelState?_eq_some s hwf hpack
          cases hstepCore : step (SKYLoweringSemantics.oracleArrayEval oracleVals) s with
          | mk status state =>
              have hstepExpected :
                  packedExpectedStep? s oracleVals =
                    (do
                      let packed' ← ofKernelState? state
                      pure (status, packed')) := by
                simp [packedExpectedStep?, hpack, hstepCore]
              have hstepPacked :
                  step? (SKYLoweringSemantics.oracleArrayEval oracleVals) packed =
                    (do
                      let packed' ← ofKernelState? state
                      pure (status, packed')) := by
                simp [step?, hround, hstepCore]
              cases hnext : ofKernelState? state with
              | none =>
                  cases status <;>
                    simp [hstepExpected, hstepPacked, packedRunFuel?, hpack, hnext]
              | some packed' =>
                  cases status with
                  | halted =>
                      simp [hstepExpected, hstepPacked, packedRunFuel?, hpack, hnext]
                  | outOfHeap =>
                      simp [hstepExpected, hstepPacked, packedRunFuel?, hpack, hnext]
                  | progress =>
                      have hwf' : state.WellFormed := by
                        have hstepWf :
                            (step (oracleEval := SKYLoweringSemantics.oracleArrayEval oracleVals) s).state.WellFormed :=
                          step_wellFormed
                            (oracleEval := SKYLoweringSemantics.oracleArrayEval oracleVals) (s := s) hwf
                        simpa [hstepCore] using hstepWf
                      have hround' : toKernelState? packed' = some state := by
                        exact toKernelState?_of_ofKernelState?_eq_some state hwf' hnext
                      simp [hstepExpected, hstepPacked, packedRunFuel?, hpack, hnext, hround']
                      simpa [packedRunFuel?, hnext] using ih state hwf'

theorem packedExpectedRunFuel?_eq_packedRunFuel?
    (fuel : Nat) (s : KernelState) (oracleVals : Array Int) (hwf : s.WellFormed) :
    packedExpectedRunFuel? fuel s oracleVals = packedRunFuel? fuel s oracleVals := by
  exact packedExpectedRunFuel?_eq_packedRunFuel_ofKernelState fuel s oracleVals hwf

theorem packedRunLoweredFuel?_eq_packedExpectedRunFuel?
    (fuel : Nat) (s : KernelState) (oracleVals : Array Int) (hwf : s.WellFormed) :
    packedRunLoweredFuel? fuel s oracleVals = packedExpectedRunFuel? fuel s oracleVals := by
  induction fuel generalizing s with
  | zero =>
      rfl
  | succ fuel ih =>
      unfold packedRunLoweredFuel? packedExpectedRunFuel?
      rw [packedRunLoweredStep?_eq_packedExpectedStep? s oracleVals hwf]
      cases hstep : packedExpectedStep? s oracleVals with
      | none =>
          simp [hstep]
      | some result =>
          cases result with
          | mk status packed =>
              cases status with
              | halted =>
                  simp [hstep]
              | outOfHeap =>
                  simp [hstep]
              | progress =>
                  have hstepCoreEq : packedExpectedStep? s oracleVals = some (.progress, packed) := hstep
                  rw [packedExpectedStep?_eq_packedStep? s oracleVals hwf] at hstepCoreEq
                  unfold packedStep? step? at hstepCoreEq
                  cases hpack : ofKernelState? s with
                  | none =>
                      simp [hpack] at hstepCoreEq
                  | some packedIn =>
                      have hroundIn : toKernelState? packedIn = some s := by
                        exact toKernelState?_of_ofKernelState?_eq_some s hwf hpack
                      cases hstepCore : step (SKYLoweringSemantics.oracleArrayEval oracleVals) s with
                      | mk status state =>
                          cases hnext : ofKernelState? state with
                          | none =>
                              simp [hpack, hroundIn, hstepCore, hnext] at hstepCoreEq
                          | some packedOut =>
                              cases status <;> simp [hpack, hroundIn, hstepCore, hnext] at hstepCoreEq
                              case progress =>
                                  subst packed
                                  have hstepWf :
                                      (step (oracleEval := SKYLoweringSemantics.oracleArrayEval oracleVals) s).state.WellFormed :=
                                    step_wellFormed
                                      (oracleEval := SKYLoweringSemantics.oracleArrayEval oracleVals) (s := s) hwf
                                  have hwfState : state.WellFormed := by
                                    simpa [hstepCore] using hstepWf
                                  have hroundOut : toKernelState? packedOut = some state := by
                                    exact toKernelState?_of_ofKernelState?_eq_some state hwfState hnext
                                  cases hdecode : toKernelState? packedOut with
                                  | none =>
                                      simp [hdecode] at hroundOut
                                  | some core =>
                                      have hcore : core = state := by
                                        simpa [hdecode] using hroundOut
                                      subst core
                                      simpa [hdecode, hstepCore] using ih state hwfState

theorem packedRunLoweredFuel?_eq_packedRunFuel?
    (fuel : Nat) (s : KernelState) (oracleVals : Array Int) (hwf : s.WellFormed) :
    packedRunLoweredFuel? fuel s oracleVals = packedRunFuel? fuel s oracleVals := by
  rw [packedRunLoweredFuel?_eq_packedExpectedRunFuel? fuel s oracleVals hwf]
  exact packedExpectedRunFuel?_eq_packedRunFuel? fuel s oracleVals hwf

/--
Pack the kernel one-step result directly at the output boundary.
Unlike `packedStep?`, this does not require the input state itself to be wrapper-packable.
-/
def kernelOutputPackedStep? (s : KernelState) (oracleVals : Array Int) :
    Option (StepStatus × WrapperState) := do
  let result := step (SKYLoweringSemantics.oracleArrayEval oracleVals) s
  let packed ← ofKernelState? result.state
  pure (result.status, packed)

/--
Pack the lowered one-step result directly at the output boundary.
-/
def runLoweredOutputPackedStep? (s : KernelState) (oracleVals : Array Int) :
    Option (StepStatus × WrapperState) := do
  let result ← runLoweredStep? s oracleVals
  let packed ← ofKernelState? result.2
  pure (result.1, packed)

/--
Pack the kernel fuel result directly at the output boundary.
-/
def kernelOutputPackedRunFuel? (fuel : Nat) (s : KernelState) (oracleVals : Array Int) :
    Option (StepStatus × WrapperState) := do
  let result := runFuel (SKYLoweringSemantics.oracleArrayEval oracleVals) fuel s
  let packed ← ofKernelState? result.state
  pure (result.status, packed)

/--
Pack the lowered fuel result directly at the output boundary.
-/
def runLoweredOutputPackedRunFuel? (fuel : Nat) (s : KernelState) (oracleVals : Array Int) :
    Option (StepStatus × WrapperState) := do
  let result ← runLoweredFuel? fuel s oracleVals
  let packed ← ofKernelState? result.2
  pure (result.1, packed)

/--
Direct bounded-machine one-step result packed at the wrapper output boundary.
-/
def boundedOutputPackedStep? (maxNodes : Nat) (s : BoundedState) (oracleVals : Array Int) :
    Option (StepStatus × WrapperState) := do
  let result :=
    HeytingLean.LoF.Combinators.SKYReducerKernel.ofBoundedStepResult maxNodes
      (HeytingLean.LoF.Combinators.SKYMachineBounded.State.step
        (SKYLoweringSemantics.oracleArrayEval oracleVals) maxNodes s)
  let packed ← ofKernelState? result.state
  pure (result.status, packed)

/--
Direct bounded-machine fuel result packed at the wrapper output boundary.
-/
def boundedOutputPackedRunFuel? (maxNodes fuel : Nat) (s : BoundedState) (oracleVals : Array Int) :
    Option (StepStatus × WrapperState) := do
  let result :=
    HeytingLean.LoF.Combinators.SKYReducerKernel.ofBoundedStepResult maxNodes
      (HeytingLean.LoF.Combinators.SKYMachineBounded.State.runFuel
        (SKYLoweringSemantics.oracleArrayEval oracleVals) maxNodes fuel s)
  let packed ← ofKernelState? result.state
  pure (result.status, packed)

theorem runLoweredOutputPackedStep?_eq_kernelOutputPackedStep?
    (s : KernelState) (oracleVals : Array Int) (hwf : s.WellFormed) :
    runLoweredOutputPackedStep? s oracleVals = kernelOutputPackedStep? s oracleVals := by
  unfold runLoweredOutputPackedStep? kernelOutputPackedStep?
  rw [runLoweredStep?_eq_expectedStep? s oracleVals hwf]
  simp [expectedStep?]

theorem runLoweredOutputPackedRunFuel?_eq_kernelOutputPackedRunFuel?
    (fuel : Nat) (s : KernelState) (oracleVals : Array Int) (hwf : s.WellFormed) :
    runLoweredOutputPackedRunFuel? fuel s oracleVals = kernelOutputPackedRunFuel? fuel s oracleVals := by
  unfold runLoweredOutputPackedRunFuel? kernelOutputPackedRunFuel?
  rw [runLoweredFuel?_eq_expectedRunFuel? fuel s oracleVals hwf]
  simp [expectedRunFuel?]

theorem kernelOutputPackedStep?_ofBoundedState (maxNodes : Nat) (s : BoundedState)
    (oracleVals : Array Int) :
    kernelOutputPackedStep?
        (HeytingLean.LoF.Combinators.SKYReducerKernel.ofBoundedState maxNodes s) oracleVals =
      boundedOutputPackedStep? maxNodes s oracleVals := by
  unfold kernelOutputPackedStep? boundedOutputPackedStep?
  rw [HeytingLean.LoF.Combinators.SKYReducerKernel.step_ofBoundedState
    (oracleEval := SKYLoweringSemantics.oracleArrayEval oracleVals) maxNodes s]

theorem kernelOutputPackedRunFuel?_ofBoundedState (maxNodes fuel : Nat) (s : BoundedState)
    (oracleVals : Array Int) :
    kernelOutputPackedRunFuel? fuel
        (HeytingLean.LoF.Combinators.SKYReducerKernel.ofBoundedState maxNodes s) oracleVals =
      boundedOutputPackedRunFuel? maxNodes fuel s oracleVals := by
  unfold kernelOutputPackedRunFuel? boundedOutputPackedRunFuel?
  rw [HeytingLean.LoF.Combinators.SKYReducerKernel.runFuel_ofBoundedState
    (oracleEval := SKYLoweringSemantics.oracleArrayEval oracleVals) maxNodes fuel s]

theorem runLoweredOutputPackedStep?_ofBoundedState (maxNodes : Nat) (s : BoundedState)
    (oracleVals : Array Int) (hmax : s.nodes.size ≤ maxNodes) :
    runLoweredOutputPackedStep?
        (HeytingLean.LoF.Combinators.SKYReducerKernel.ofBoundedState maxNodes s) oracleVals =
      boundedOutputPackedStep? maxNodes s oracleVals := by
  have hwf :
      (HeytingLean.LoF.Combinators.SKYReducerKernel.ofBoundedState maxNodes s).WellFormed :=
    HeytingLean.LoF.Combinators.SKYReducerKernel.wellFormed_ofBoundedState maxNodes s hmax
  rw [runLoweredOutputPackedStep?_eq_kernelOutputPackedStep? _ _ hwf]
  exact kernelOutputPackedStep?_ofBoundedState maxNodes s oracleVals

theorem runLoweredOutputPackedRunFuel?_ofBoundedState (maxNodes fuel : Nat) (s : BoundedState)
    (oracleVals : Array Int) (hmax : s.nodes.size ≤ maxNodes) :
    runLoweredOutputPackedRunFuel? fuel
        (HeytingLean.LoF.Combinators.SKYReducerKernel.ofBoundedState maxNodes s) oracleVals =
      boundedOutputPackedRunFuel? maxNodes fuel s oracleVals := by
  have hwf :
      (HeytingLean.LoF.Combinators.SKYReducerKernel.ofBoundedState maxNodes s).WellFormed :=
    HeytingLean.LoF.Combinators.SKYReducerKernel.wellFormed_ofBoundedState maxNodes s hmax
  rw [runLoweredOutputPackedRunFuel?_eq_kernelOutputPackedRunFuel? fuel _ _ hwf]
  exact kernelOutputPackedRunFuel?_ofBoundedState maxNodes fuel s oracleVals

end SKYReducerGPUWrapperLowering
end Compile
end LeanCP
end HeytingLean
