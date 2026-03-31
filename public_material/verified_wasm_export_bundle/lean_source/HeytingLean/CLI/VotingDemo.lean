import Lean
import HeytingLean.Governance.Model

/-
# voting_demo CLI

Tiny CLI that exercises the abstract governance model by tallying a
small hard-coded ballot set and printing the result.
-/

namespace HeytingLean
namespace CLI
namespace VotingDemo

open HeytingLean.Governance.Model

def main (_argv : List String) : IO UInt32 := do
  let bs : List Ballot :=
    [ { voter := "alice", weight := 1, choice := true }
    , { voter := "bob",   weight := 2, choice := false }
    , { voter := "carol", weight := 3, choice := true } ]
  let t := tallyBallots bs
  IO.println s!"voting_demo: yes={t.yes}, no={t.no}, totalWeight={t.totalWeight}"
  -- Small DAO snapshot and invariant commentary.
  let st := exampleDAOState
  IO.println s!"voting_demo: exampleDAOState proposals={st.proposals.length}, currentTime={st.currentTime}"
  IO.println "voting_demo: ProposalExecutionCorrect, TimelockSecurity, and VetoMechanismsCorrect provably hold for this snapshot."
  IO.println "voting_demo: DAOInvariant is preserved for all finite sequences of DAOAction steps (DAOInvariant_run)."
  pure 0

end VotingDemo
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.VotingDemo.main args
