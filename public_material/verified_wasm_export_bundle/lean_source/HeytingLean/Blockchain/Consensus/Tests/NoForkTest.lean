import HeytingLean.Blockchain.Consensus.Core

open HeytingLean.Blockchain.Consensus.Core

/-- Example: All honest nodes see the same chain at each time. -/
def exampleChain : Time → Chain := fun t => List.range (t + 1)

def exampleHonest : NodeId → Prop := fun n => n < 3

/-- Example execution: 3 honest nodes, all see the same chain at each time. -/
def exampleExec : Execution := {
  chainAt := fun t n => exampleChain t,
  honest := exampleHonest
}

/-- Assert NoFork holds for this execution. -/
theorem exampleExec_noFork : NoFork exampleExec :=
  noForkTheorem_equalChains exampleExec exampleChain (by intros t n hn; rfl)

-- QA: Print axioms to ensure no proof holes
#print axioms exampleExec_noFork
