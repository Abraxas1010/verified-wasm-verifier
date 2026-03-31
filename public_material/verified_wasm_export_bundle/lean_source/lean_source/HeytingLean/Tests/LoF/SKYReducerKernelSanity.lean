import HeytingLean.LoF.Combinators.SKYReducerKernel

namespace HeytingLean
namespace Tests
namespace LoF
namespace SKYReducerKernelSanity

open HeytingLean.LoF.Combinators
open HeytingLean.LoF.Combinators.SKYMachineBounded
open HeytingLean.LoF.Combinators.SKYReducerKernel

def oracleEval : Nat → Bool
  | 0 => true
  | _ => false

def appMachine : SKYMachineBounded.State Nat :=
  { nodes :=
      #[ SKYGraph.Node.combK
       , SKYGraph.Node.combS
       , SKYGraph.Node.app 0 1 ]
    focus := 2
    stack := [] }

def kMachine : SKYMachineBounded.State Nat :=
  { nodes := #[SKYGraph.Node.combK]
    focus := 0
    stack := [7, 8] }

def sMachine : SKYMachineBounded.State Nat :=
  { nodes := #[SKYGraph.Node.combS]
    focus := 0
    stack := [1, 2, 3] }

def yMachine : SKYMachineBounded.State Nat :=
  { nodes := #[SKYGraph.Node.combY]
    focus := 0
    stack := [5] }

def oracleMachine : SKYMachineBounded.State Nat :=
  { nodes := #[SKYGraph.Node.oracle 0]
    focus := 0
    stack := [11, 12] }

example :
    step oracleEval (ofBoundedState 8 appMachine) =
      ofBoundedStepResult 8 (SKYMachineBounded.State.step oracleEval 8 appMachine) := by
  rfl

example :
    step oracleEval (ofBoundedState 8 kMachine) =
      ofBoundedStepResult 8 (SKYMachineBounded.State.step oracleEval 8 kMachine) := by
  rfl

example :
    step oracleEval (ofBoundedState 8 sMachine) =
      ofBoundedStepResult 8 (SKYMachineBounded.State.step oracleEval 8 sMachine) := by
  rfl

example :
    step oracleEval (ofBoundedState 8 yMachine) =
      ofBoundedStepResult 8 (SKYMachineBounded.State.step oracleEval 8 yMachine) := by
  rfl

example :
    step oracleEval (ofBoundedState 8 oracleMachine) =
      ofBoundedStepResult 8 (SKYMachineBounded.State.step oracleEval 8 oracleMachine) := by
  rfl

end SKYReducerKernelSanity
end LoF
end Tests
end HeytingLean
