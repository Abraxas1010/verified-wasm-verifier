import HeytingLean.Governance.Spec
import HeytingLean.Governance.Model

/-
# Governance.Bridge

Registry-style bridge from `Governance.Spec.PropertyId` to concrete
predicates over `DAOState` and the tally model in `Governance.Model`.

This mirrors the pattern used in other domains (consensus, privacy,
economics): a lightweight `propertyHolds` function plus small witness
lemmas for example instances. It is intentionally minimal and focused on
the DAO-related rows for now.
-/

namespace HeytingLean
namespace Governance
namespace Bridge

open Governance.Model

/-- Interpretation of governance `PropertyId`s for a given DAO state.

For now we give concrete meanings only to tally correctness and the
DAO-style properties; the remaining mechanism-design / privacy rows
are currently treated as `True` until more detailed models are added. -/
def propertyHolds (st : DAOState) (p : Spec.PropertyId) : Prop :=
  match p with
  | .tallyCorrectness =>
      ∀ bs : List Ballot, TallyCorrect bs (tallyBallots bs)
  | .proposalExecutionCorrectness =>
      ProposalExecutionCorrect st
  | .timelockSecurity =>
      TimelockSecurity st
  | .vetoMechanismsCorrectness =>
      VetoMechanismsCorrect st
  | .incentiveCompatibility      => True
  | .stakingEquilibrium          => True
  | .mevResistance               => True
  | .auctionTruthfulness         => True
  | .costOfAttack                => True
  | .slashingDeterrence          => True
  | .inflationDeflationModels    => True
  | .liquidityMiningSafety       => True
  | .ballotPrivacy               => True
  | .coercionResistance          => True
  | .receiptFreeness             => True
  | .quorumRequirements          => True

/-- For any DAO state, the `tallyCorrectness` row holds in the sense
that `tallyBallots` always produces a tally satisfying `TallyCorrect`. -/
theorem propertyHolds_tallyCorrectness (st : DAOState) :
    propertyHolds st Spec.PropertyId.tallyCorrectness := by
  classical
  dsimp [propertyHolds]
  intro bs
  exact tallyBallots_correct bs

/-- In `exampleDAOState`, the registry row
`proposalExecutionCorrectness` holds, as witnessed by
`exampleDAOState_ProposalExecutionCorrect`. -/
theorem propertyHolds_proposalExecution_example :
    propertyHolds Model.exampleDAOState Spec.PropertyId.proposalExecutionCorrectness := by
  classical
  simpa [propertyHolds] using Model.exampleDAOState_ProposalExecutionCorrect

/-- In `exampleDAOState`, the registry row `timelockSecurity` holds. -/
theorem propertyHolds_timelockSecurity_example :
    propertyHolds Model.exampleDAOState Spec.PropertyId.timelockSecurity := by
  classical
  simpa [propertyHolds] using Model.exampleDAOState_TimelockSecurity

/-- In `exampleDAOState`, the registry row
`vetoMechanismsCorrectness` holds. -/
theorem propertyHolds_vetoMechanisms_example :
    propertyHolds Model.exampleDAOState Spec.PropertyId.vetoMechanismsCorrectness := by
  classical
  simpa [propertyHolds] using Model.exampleDAOState_VetoMechanismsCorrect

end Bridge
end Governance
end HeytingLean
