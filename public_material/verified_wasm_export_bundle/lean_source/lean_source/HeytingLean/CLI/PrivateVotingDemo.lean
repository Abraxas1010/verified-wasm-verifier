import Lean
import HeytingLean.Governance.Model
import HeytingLean.Crypto.ZK.PrivateVotingExample

/-
# private_voting_demo CLI

Small CLI that:

* builds an example ballot list and computes its tally;
* packages this into a `PrivateVotingExample.Proof`;
* evaluates the example verifier `verify`; and
* uses `statement_holds` to witness tally correctness for this instance.

This provides a concrete harness for the private-voting correctness
row (`zk.app.private_voting`) and its bridge between the governance
model (`tallyBallots`) and the ZK example verifier.
-/

namespace HeytingLean
namespace CLI
namespace PrivateVotingDemo

open HeytingLean.Governance.Model
open HeytingLean.Crypto.ZK

/-- Example ballots over the abstract governance model. -/
def exampleBallots : List Ballot :=
  [ { voter := "alice", weight := 1, choice := true }
  , { voter := "bob",   weight := 2, choice := false }
  , { voter := "carol", weight := 3, choice := true } ]

def main (_argv : List String) : IO UInt32 := do
  let bs := exampleBallots
  let t  := tallyBallots bs
  let p  : PrivateVotingExample.Proof :=
    { ballots := bs, tally := t }

  -- Compute the verifier result.
  let v := PrivateVotingExample.verify p
  IO.println s!"private_voting_demo:"
  IO.println s!"  ballots.count = {bs.length}"
  IO.println s!"  tally:   yes={t.yes}, no={t.no}, totalWeight={t.totalWeight}"
  IO.println s!"  verify(p) = {v}"

  -- At the Lean level, we can show that `verify p = true` and obtain
  -- the corresponding tally-equality certificate from
  -- `PrivateVotingExample.statement_holds`.
  have hEq : tallyBallots p.ballots = p.tally := by rfl
  have hAccept : PrivateVotingExample.verify p = true := by
    simp [PrivateVotingExample.verify, hEq]
  let hTally := PrivateVotingExample.statement_holds p hAccept
  IO.println "  Lean proof: if the verifier accepts this proof instance,"
  IO.println "    then the published tally equals `tallyBallots` on the ballots."

  pure 0

end PrivateVotingDemo
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.PrivateVotingDemo.main args
