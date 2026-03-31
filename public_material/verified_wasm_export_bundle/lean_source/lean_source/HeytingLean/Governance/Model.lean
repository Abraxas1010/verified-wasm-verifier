import HeytingLean.Governance.Spec

/-
# Governance.Model

Abstract models for voting and DAO-style governance.

This module introduces:
* a simple ballot and tally structure;
* a minimal proposal/DAO state model; and
* statement shapes for core governance properties such as tally
  correctness and proposal execution correctness.

The emphasis is on stable types and predicate names; detailed proofs are
left to future developments.
-/

namespace HeytingLean
namespace Governance
namespace Model

open Classical

/-- Abstract address/account identifier for governance participants. -/
abbrev Address := String

/-- A single ballot with a Boolean choice and weight. -/
structure Ballot where
  voter  : Address
  weight : Nat
  choice : Bool
  deriving Repr

/-- Aggregate tally of yes/no votes and total weight. -/
structure Tally where
  yes         : Nat
  no          : Nat
  totalWeight : Nat
  deriving Repr, DecidableEq

namespace Ballots

/-- Total yes-vote weight for a list of ballots. -/
def yesWeight : List Ballot → Nat
  | [] => 0
  | b :: bs => (if b.choice then b.weight else 0) + yesWeight bs

/-- Total no-vote weight for a list of ballots. -/
def noWeight : List Ballot → Nat
  | [] => 0
  | b :: bs => (if b.choice then 0 else b.weight) + noWeight bs

/-- Total voting weight for a list of ballots. -/
def totalWeight : List Ballot → Nat
  | [] => 0
  | b :: bs => b.weight + totalWeight bs

end Ballots

/-- Compute a simple tally for a list of ballots. -/
def tallyBallots : List Ballot → Tally
  | [] =>
      { yes := 0, no := 0, totalWeight := 0 }
  | b :: bs =>
      let acc := tallyBallots bs
      if b.choice then
        { yes := acc.yes + b.weight
          , no := acc.no
          , totalWeight := acc.totalWeight + b.weight }
      else
        { yes := acc.yes
          , no := acc.no + b.weight
          , totalWeight := acc.totalWeight + b.weight }

/-- Parameters governing DAO proposal acceptance. -/
structure DAOParams where
  quorum    : Nat
  threshold : Nat
  timelock  : Nat
  deriving Repr

/-- Minimal proposal state with timing, execution, veto, and tally info. -/
structure Proposal where
  id          : Nat
  description : String
  startTime   : Nat
  endTime     : Nat
  executed    : Bool
  vetoed      : Bool
  tally       : Tally
  deriving Repr

/-- Global DAO state with parameters, proposals, and a notion of current
    time. -/
structure DAOState where
  params      : DAOParams
  proposals   : List Proposal
  currentTime : Nat
  deriving Repr

/-- Specification-level predicate capturing tally correctness. A tally is
    correct when its fields agree with the total yes/no/overall voting
    weights of the underlying ballots. -/
def TallyCorrect (bs : List Ballot) (t : Tally) : Prop :=
  t.yes = Ballots.yesWeight bs ∧
  t.no = Ballots.noWeight bs ∧
  t.totalWeight = Ballots.totalWeight bs

/-- `tallyBallots` computes yes/no/total weights as specified by
    `Ballots.yesWeight`, `Ballots.noWeight`, and `Ballots.totalWeight`. -/
theorem tallyBallots_correct (bs : List Ballot) :
    TallyCorrect bs (tallyBallots bs) := by
  classical
  induction bs with
  | nil =>
      simp [TallyCorrect, tallyBallots,
            Ballots.yesWeight, Ballots.noWeight, Ballots.totalWeight]
  | cons b bs ih =>
      -- Expand the statement for `bs` from the induction hypothesis.
      have ih' := ih
      simp [TallyCorrect] at ih'
      rcases ih' with ⟨hy, hn, ht⟩
      -- Now analyze the head ballot.
      by_cases hChoice : b.choice
      · -- Yes-branch.
        simp [TallyCorrect, tallyBallots, hChoice,
              Ballots.yesWeight, Ballots.noWeight, Ballots.totalWeight,
              hy, hn, ht, Nat.add_comm]
      · -- No-branch.
        simp [TallyCorrect, tallyBallots, hChoice,
              Ballots.yesWeight, Ballots.noWeight, Ballots.totalWeight,
              hy, hn, ht, Nat.add_comm]

/-- A proposal has passed under the DAO parameters and current time if
    it meets quorum and yes-vote thresholds, its voting period has
    ended, and it has not been vetoed. -/
def ProposalPassed (st : DAOState) (p : Proposal) : Prop :=
  p.tally.totalWeight ≥ st.params.quorum ∧
  p.tally.yes ≥ st.params.threshold ∧
  st.currentTime ≥ p.endTime ∧
  ¬ p.vetoed

/-- Proposal execution correctness: in a given DAO state, every executed
    proposal in `proposals` must have passed according to
    `ProposalPassed`. This captures a minimal form of “executed implies
    accepted and not vetoed”. -/
def ProposalExecutionCorrect (st : DAOState) : Prop :=
  ∀ p ∈ st.proposals, p.executed → ProposalPassed st p

/-- Timelock security: any executed proposal must satisfy the timelock
    delay `timelock` from its `endTime` to the DAO’s `currentTime`. In
    a more detailed model this would be phrased over transitions; here
    it is recorded as a static safety check on the snapshot. -/
def TimelockSecurity (st : DAOState) : Prop :=
  ∀ p ∈ st.proposals, p.executed →
    st.currentTime ≥ p.endTime + st.params.timelock

/-- Veto mechanism correctness: no vetoed proposal is marked as
    executed. This forbids the obviously inconsistent combination
    `vetoed = true ∧ executed = true` for any proposal in the DAO
    state. -/
def VetoMechanismsCorrect (st : DAOState) : Prop :=
  ∀ p ∈ st.proposals, p.vetoed → ¬ p.executed

/-- Example DAO parameters with minimal quorum, threshold, and zero
    timelock to witness the governance predicates above. -/
def exampleDAOParams : DAOParams :=
  { quorum := 1
    , threshold := 1
    , timelock := 0 }

/-- Example tally with a single yes vote meeting quorum and threshold. -/
def exampleTally : Tally :=
  { yes := 1
    , no := 0
    , totalWeight := 1 }

/-- Example proposal that has passed, is executed, and not vetoed. -/
def exampleProposal : Proposal :=
  { id := 0
    , description := "example proposal"
    , startTime := 0
    , endTime := 0
    , executed := true
    , vetoed := false
    , tally := exampleTally }

/-- Example DAO state with a single executed proposal satisfying
    quorum/threshold, timelock, and veto conditions. -/
def exampleDAOState : DAOState :=
  { params := exampleDAOParams
    , proposals := [exampleProposal]
    , currentTime := 0 }

/-- In `exampleDAOState`, every executed proposal has passed according
    to `ProposalPassed`, so `ProposalExecutionCorrect` holds. -/
theorem exampleDAOState_ProposalExecutionCorrect :
    ProposalExecutionCorrect exampleDAOState := by
  intro p hp hExec
  -- There is only one proposal in the list, `exampleProposal`.
  have hEq : p = exampleProposal := by
    simpa [exampleDAOState] using hp
  subst hEq
  -- Now check the passing conditions directly.
  -- After substitution, `ProposalPassed` reduces to a conjunction of
  -- trivial inequalities and boolean facts.
  dsimp [ProposalExecutionCorrect, ProposalPassed,
        exampleDAOState, exampleDAOParams, exampleProposal] at hExec ⊢
  -- `hExec` is just `True` in this example; we can ignore it.
  clear hExec
  -- All numeric conditions are reflexive (`1 ≥ 1`, `0 ≥ 0`), and
  -- veto is false.
  constructor
  · decide
  · constructor
    · decide
    · constructor
      · decide
      · decide

/-- In `exampleDAOState`, any executed proposal satisfies the timelock
    condition (with `timelock = 0`). -/
theorem exampleDAOState_TimelockSecurity :
    TimelockSecurity exampleDAOState := by
  intro p hp hExec
  have hEq : p = exampleProposal := by
    simpa [exampleDAOState] using hp
  subst hEq
  simp [exampleDAOState, exampleDAOParams, exampleProposal]

/-- In `exampleDAOState`, no vetoed proposal is executed, so
    `VetoMechanismsCorrect` holds. -/
theorem exampleDAOState_VetoMechanismsCorrect :
    VetoMechanismsCorrect exampleDAOState := by
  intro p hp hVeto hExec
  have hEq : p = exampleProposal := by
    simpa [exampleDAOState] using hp
  subst hEq
  -- This case is impossible since `exampleProposal.vetoed = false`.
  have hVeto' := hVeto
  simp [exampleProposal] at hVeto'

/-- Bundled DAO safety invariant combining proposal execution correctness,
    timelock security, and veto-mechanism correctness. -/
def DAOInvariant (st : DAOState) : Prop :=
  ProposalExecutionCorrect st ∧
  TimelockSecurity st ∧
  VetoMechanismsCorrect st

/-- Simple DAO actions: advance time, add a proposal, cast a vote, execute a proposal, or veto a proposal. -/
inductive DAOAction where
  | advanceTime (dt : Nat)
  | addProposal (p : Proposal)
  | castVote (pid : Nat) (b : Ballot)
  | executeProposal (pid : Nat)
  | vetoProposal (pid : Nat)
  deriving Repr

/-- Guard for when it is safe to execute a proposal in the current DAO
    state: correct id, passed according to `ProposalPassed`, timelock
    satisfied, and not already executed. -/
def canExecute (st : DAOState) (pid : Nat) (p : Proposal) : Prop :=
  p.id = pid ∧
  ProposalPassed st p ∧
  st.currentTime ≥ p.endTime + st.params.timelock ∧
  ¬ p.executed

/-- Update a proposal in response to an execution attempt: if `canExecute`
    holds, mark `executed := true`, otherwise leave the proposal unchanged. -/
noncomputable def executeUpdate (st : DAOState) (pid : Nat) (p : Proposal) : Proposal :=
  if canExecute st pid p then
    { p with executed := true }
  else
    p

/-- `executeUpdate` never changes the `vetoed` flag. -/
theorem executeUpdate_preserves_veto
    (st : DAOState) (pid : Nat) (p : Proposal) :
    (executeUpdate st pid p).vetoed = p.vetoed := by
  unfold executeUpdate
  by_cases h : canExecute st pid p
  · simp [h]
  · simp [h]

/-- `executeUpdate` never changes the `endTime`. -/
theorem executeUpdate_preserves_endTime
    (st : DAOState) (pid : Nat) (p : Proposal) :
    (executeUpdate st pid p).endTime = p.endTime := by
  unfold executeUpdate
  by_cases h : canExecute st pid p
  · simp [h]
  · simp [h]

/-- If `executeUpdate` produces an executed proposal, then either the proposal
    was already executed, or the `canExecute` guard held in the pre-state. -/
theorem executeUpdate_exec_cases
    (st : DAOState) (pid : Nat) (p : Proposal) :
    (executeUpdate st pid p).executed →
      p.executed ∨ canExecute st pid p := by
  intro hExecNew
  unfold executeUpdate at hExecNew
  by_cases h : canExecute st pid p
  · -- Guard branch: we explicitly set `executed := true`, so `canExecute` holds.
    exact Or.inr h
  · -- Else branch: the proposal is unchanged.
    have : p.executed := by
      simpa [h] using hExecNew
    exact Or.inl this

/-- Executing does not break `ProposalPassed`: the fields used by
    `ProposalPassed` are unchanged by `executeUpdate`. -/
theorem ProposalPassed_executeUpdate
    (st : DAOState) (pid : Nat) (p : Proposal) :
    ProposalPassed st p → ProposalPassed st (executeUpdate st pid p) := by
  intro hPass
  unfold executeUpdate
  by_cases h : canExecute st pid p
  · -- In the guard branch we update only `executed`.
    simpa [h, ProposalPassed] using hPass
  · -- Otherwise the proposal is unchanged.
    simpa [h] using hPass

/-- Update a proposal in response to a veto attempt: if the id matches and the
    proposal is not yet executed (`executed = false`), set `vetoed := true`;
    otherwise leave the proposal unchanged. -/
noncomputable def vetoUpdate (pid : Nat) (p : Proposal) : Proposal :=
  if p.id = pid ∧ p.executed = false then
    { p with vetoed := true }
  else
    p

/-- `vetoUpdate` never changes the `executed` flag. -/
theorem vetoUpdate_preserves_executed
    (pid : Nat) (p : Proposal) :
    (vetoUpdate pid p).executed = p.executed := by
  unfold vetoUpdate
  by_cases h : p.id = pid ∧ p.executed = false
  · simp [h]
  · simp [h]

/-- Update a proposal's tally in response to a vote, without changing
    any control flags or timing fields. -/
def castVoteUpdate (pid : Nat) (b : Ballot) (p : Proposal) : Proposal :=
  if p.id = pid then
    let t := p.tally
    if b.choice then
      { p with
        tally :=
          { yes := t.yes + b.weight
            , no := t.no
            , totalWeight := t.totalWeight + b.weight } }
    else
      { p with
        tally :=
          { yes := t.yes
            , no := t.no + b.weight
            , totalWeight := t.totalWeight + b.weight } }
  else
    p

/-- `castVoteUpdate` never changes the executed/vetoed flags of a proposal. -/
theorem castVoteUpdate_preserves_flags
    (pid : Nat) (b : Ballot) (p : Proposal) :
    (castVoteUpdate pid b p).executed = p.executed ∧
    (castVoteUpdate pid b p).vetoed = p.vetoed := by
  unfold castVoteUpdate
  by_cases h : p.id = pid
  · -- Updated proposal: only the tally field is modified; split on the vote.
    by_cases hChoice : b.choice
    · simp [h, hChoice]
    · simp [h, hChoice]
  · -- Unaffected proposal.
    simp [h]

/-- `castVoteUpdate` leaves the proposal's `endTime` unchanged. -/
theorem castVoteUpdate_preserves_endTime
    (pid : Nat) (b : Ballot) (p : Proposal) :
    (castVoteUpdate pid b p).endTime = p.endTime := by
  unfold castVoteUpdate
  by_cases h : p.id = pid
  · by_cases hChoice : b.choice
    · simp [h, hChoice]
    · simp [h, hChoice]
  · simp [h]

/-- Casting a vote preserves the `ProposalPassed` predicate for that proposal. -/
theorem ProposalPassed_castVoteUpdate
    (st : DAOState) (pid : Nat) (b : Ballot) (p : Proposal) :
    ProposalPassed st p → ProposalPassed st (castVoteUpdate pid b p) := by
  intro hPass
  -- Split on whether this proposal is the target of the vote.
  by_cases hpid : p.id = pid
  · -- The tally is updated but only in a monotone way.
    rcases hPass with ⟨hq, hyes, htime, hNotVeto⟩
    unfold ProposalPassed
    constructor
    · -- Total voting weight can only increase.
      have hq' : st.params.quorum ≤ p.tally.totalWeight + b.weight :=
        Nat.le_trans hq (Nat.le_add_right _ _)
      by_cases hChoice : b.choice
      · -- Yes-vote branch; total weight is `t.totalWeight + b.weight`.
        simpa [castVoteUpdate, hpid, hChoice] using hq'
      · -- No-vote branch; total weight is still `t.totalWeight + b.weight`.
        simpa [castVoteUpdate, hpid, hChoice] using hq'
    · constructor
      · -- Yes-vote weight is monotone in the vote.
        -- First, show `p.tally.yes ≤ (castVoteUpdate pid b p).tally.yes`.
        have hYesMonotone :
            p.tally.yes ≤ (castVoteUpdate pid b p).tally.yes := by
          by_cases hChoice : b.choice
          · have hEq :
              (castVoteUpdate pid b p).tally.yes =
                p.tally.yes + b.weight := by
              simp [castVoteUpdate, hpid, hChoice]
            simp [hEq]
          · have hEq :
              (castVoteUpdate pid b p).tally.yes = p.tally.yes := by
              simp [castVoteUpdate, hpid, hChoice]
            simp [hEq]
        -- Then compose with the original threshold bound.
        exact Nat.le_trans hyes hYesMonotone
      · constructor
        · -- `endTime` is unchanged by `castVoteUpdate`.
          have hend :
              (castVoteUpdate pid b p).endTime = p.endTime :=
            castVoteUpdate_preserves_endTime pid b p
          -- Rewrite the bound on `currentTime`.
          simpa [hend] using htime
        · -- `vetoed` is unchanged by `castVoteUpdate`.
          have hFlags :=
            castVoteUpdate_preserves_flags pid b p
          have hVetoEq :
              (castVoteUpdate pid b p).vetoed = p.vetoed :=
            hFlags.right
          -- Transport the non-veto condition through the equality.
          intro hV
          have : p.vetoed := by
            simpa [hVetoEq] using hV
          exact hNotVeto this
  · -- This proposal is not affected by the vote; `castVoteUpdate` is the identity.
    have hEq : castVoteUpdate pid b p = p := by
      simp [castVoteUpdate, hpid]
    simpa [hEq] using hPass


/-- One-step DAO transition corresponding to a single action. -/
noncomputable def daoStep (st : DAOState) : DAOAction → DAOState
  | .advanceTime dt =>
      { st with currentTime := st.currentTime + dt }
  | .addProposal p =>
      -- New proposals are normalised to start non-executed and non-vetoed.
      let p0 : Proposal := { p with executed := false, vetoed := false }
      { st with proposals := p0 :: st.proposals }
  | .castVote pid b =>
      { st with proposals := st.proposals.map (castVoteUpdate pid b) }
  | .executeProposal pid =>
      { st with proposals := st.proposals.map (executeUpdate st pid) }
  | .vetoProposal pid =>
      { st with proposals := st.proposals.map (vetoUpdate pid) }

/-- Run a list of DAO actions from an initial state. -/
noncomputable def daoRun (st : DAOState) (acts : List DAOAction) : DAOState :=
  acts.foldl (fun st a => daoStep st a) st

/-- `DAOInvariant` is preserved by advancing time. -/
theorem DAOInvariant_advanceTime
    (st : DAOState) (dt : Nat) :
    DAOInvariant st → DAOInvariant (daoStep st (.advanceTime dt)) := by
  intro h
  rcases h with ⟨hExec, hTime, hVeto⟩
  refine And.intro ?hExec' (And.intro ?hTime' ?hVeto')
  · -- Proposal execution correctness is preserved since only time changes.
    intro p hp hExecP
    have hp' : p ∈ st.proposals := by
      simpa [daoStep] using hp
    have hPass : ProposalPassed st p := hExec p hp' hExecP
    rcases hPass with ⟨hq, hth, htime, hNotVeto⟩
    have htime' : p.endTime ≤ st.currentTime := htime
    have htime'' : p.endTime ≤ st.currentTime + dt :=
      Nat.le_trans htime' (Nat.le_add_right _ _)
    exact And.intro hq (And.intro hth (And.intro htime'' hNotVeto))
  · -- Timelock security: increasing time preserves the inequality.
    intro p hp hExecP
    have hp' : p ∈ st.proposals := by
      simpa [daoStep] using hp
    have hTime0 : st.currentTime ≥ p.endTime + st.params.timelock :=
      hTime p hp' hExecP
    have hTime0' : p.endTime + st.params.timelock ≤ st.currentTime :=
      hTime0
    have hTime1 :
        p.endTime + st.params.timelock ≤ st.currentTime + dt :=
      Nat.le_trans hTime0' (Nat.le_add_right _ _)
    simpa [daoStep] using hTime1
  · -- Veto mechanism correctness: flags and proposals list are unchanged.
    intro p hp hVetoP
    have hp' : p ∈ st.proposals := by
      simpa [daoStep] using hp
    have hVeto0 : ¬ p.executed := hVeto p hp' hVetoP
    simpa [daoStep] using hVeto0

/-- `DAOInvariant` is preserved by adding a (sanitised) proposal. -/
theorem DAOInvariant_addProposal
    (st : DAOState) (p : Proposal) :
    DAOInvariant st → DAOInvariant (daoStep st (.addProposal p)) := by
  intro h
  rcases h with ⟨hExec, hTime, hVeto⟩
  -- Sanitised form of the newly added proposal.
  let p0 : Proposal := { p with executed := false, vetoed := false }
  refine And.intro ?hExec' (And.intro ?hTime' ?hVeto')
  · -- Proposal execution correctness.
    intro q hq hExecQ
    have hMem : q ∈ p0 :: st.proposals := by
      simpa [daoStep, p0] using hq
    have hCases : q = p0 ∨ q ∈ st.proposals := by
      simpa [List.mem_cons] using hMem
    cases hCases with
    | inl hEq =>
        subst hEq
        -- `p0.executed` is `false`, so this case is impossible.
        have : False := by
          have h := hExecQ
          simp [p0] at h
        exact this.elim
    | inr hIn =>
        have hPassOld : ProposalPassed st q := hExec q hIn hExecQ
        simpa [daoStep, p0] using hPassOld
  · -- Timelock security.
    intro q hq hExecQ
    have hMem : q ∈ p0 :: st.proposals := by
      simpa [daoStep, p0] using hq
    have hCases : q = p0 ∨ q ∈ st.proposals := by
      simpa [List.mem_cons] using hMem
    cases hCases with
    | inl hEq =>
        subst hEq
        -- `p0.executed` is `false`, so this case is impossible.
        have : False := by
          have h := hExecQ
          simp [p0] at h
        exact this.elim
    | inr hIn =>
        have hTimeOld :
            st.currentTime ≥ q.endTime + st.params.timelock :=
          hTime q hIn hExecQ
        simpa [daoStep, p0] using hTimeOld
  · -- Veto mechanisms correctness.
    intro q hq hVetoQ
    have hMem : q ∈ p0 :: st.proposals := by
      simpa [daoStep, p0] using hq
    have hCases : q = p0 ∨ q ∈ st.proposals := by
      simpa [List.mem_cons] using hMem
    cases hCases with
    | inl hEq =>
        subst hEq
        -- `p0.vetoed` is `false`, so this case is impossible.
        have : False := by
          have h := hVetoQ
          simp [p0] at h
        exact this.elim
    | inr hIn =>
        have hVetoOld : ¬ q.executed := hVeto q hIn hVetoQ
        simpa [daoStep, p0] using hVetoOld

/-- `DAOInvariant` is preserved by casting a vote (which only changes tallies). -/
theorem DAOInvariant_castVote
    (st : DAOState) (pid : Nat) (b : Ballot) :
    DAOInvariant st → DAOInvariant (daoStep st (.castVote pid b)) := by
  intro h
  rcases h with ⟨hExec, hTime, hVeto⟩
  refine And.intro ?hExec' (And.intro ?hTime' ?hVeto')
  · -- Proposal execution correctness.
    intro q hq hExecQ
    -- Relate `q` in the post-state to some `p` in the pre-state.
    rcases List.mem_map.1 hq with ⟨p, hp, hEq⟩
    -- Executed flag is preserved by `castVoteUpdate`.
    have hExecEq :
        (castVoteUpdate pid b p).executed = p.executed :=
      (castVoteUpdate_preserves_flags pid b p).left
    have hExecP : p.executed := by
      have hExecQ' : (castVoteUpdate pid b p).executed := by
        simpa [hEq] using hExecQ
      -- Transport execution back to the pre-state.
      simpa [hExecEq] using hExecQ'
    -- Use the original execution correctness on `p`.
    have hPassP : ProposalPassed st p := hExec p hp hExecP
    -- Casting a vote preserves `ProposalPassed` for this proposal.
    have hPassQ_st :
        ProposalPassed st (castVoteUpdate pid b p) :=
      ProposalPassed_castVoteUpdate st pid b p hPassP
    -- Rewrite to the post-state and to `q`.
    have hPassQ :
        ProposalPassed (daoStep st (.castVote pid b)) q := by
      simpa [daoStep, ProposalPassed, hEq] using hPassQ_st
    exact hPassQ
  · -- Timelock security: execution flags and `endTime` are unchanged.
    intro q hq hExecQ
    rcases List.mem_map.1 hq with ⟨p, hp, hEq⟩
    -- Transport execution back to `p`.
    have hExecEq :
        (castVoteUpdate pid b p).executed = p.executed :=
      (castVoteUpdate_preserves_flags pid b p).left
    have hExecP : p.executed := by
      have hExecQ' : (castVoteUpdate pid b p).executed := by
        simpa [hEq] using hExecQ
      simpa [hExecEq] using hExecQ'
    -- Apply the original timelock condition to `p`.
    have hTimeOld :
        st.currentTime ≥ p.endTime + st.params.timelock :=
      hTime p hp hExecP
    -- `endTime` is preserved by `castVoteUpdate`.
    have hend :
        (castVoteUpdate pid b p).endTime = p.endTime :=
      castVoteUpdate_preserves_endTime pid b p
    -- First, rewrite the bound for the updated proposal in the old state.
    have hTimeQ_st :
        st.currentTime ≥
          q.endTime + st.params.timelock := by
      -- Use the equalities for `q` and its `endTime`.
      have hTimeOld' :
          st.currentTime ≥
            (castVoteUpdate pid b p).endTime + st.params.timelock := by
        simpa [hend] using hTimeOld
      simpa [hEq] using hTimeOld'
    -- Now upgrade to the post-state, where `currentTime` and `params`
    -- are unchanged.
    have hTimeQ :
        (daoStep st (.castVote pid b)).currentTime ≥
          q.endTime + (daoStep st (.castVote pid b)).params.timelock := by
      simpa [daoStep] using hTimeQ_st
    exact hTimeQ
  · -- Veto mechanisms correctness: veto/executed flags are unchanged.
    intro q hq hVetoQ
    rcases List.mem_map.1 hq with ⟨p, hp, hEq⟩
    have hFlags := castVoteUpdate_preserves_flags pid b p
    have hVetoEq :
        (castVoteUpdate pid b p).vetoed = p.vetoed :=
      hFlags.right
    have hExecEq :
        (castVoteUpdate pid b p).executed = p.executed :=
      hFlags.left
    -- Transport veto flag back to `p`.
    have hVetoP : p.vetoed := by
      have hVetoQ' : (castVoteUpdate pid b p).vetoed := by
        simpa [hEq] using hVetoQ
      simpa [hVetoEq] using hVetoQ'
    -- Original invariant forbids executed & vetoed for `p`.
    have hNotExecP : ¬ p.executed := hVeto p hp hVetoP
    -- Show that `q.executed` leads to a contradiction.
    intro hExecQ
    have hExecQ' : (castVoteUpdate pid b p).executed := by
      simpa [hEq] using hExecQ
    have hExecP : p.executed := by
      simpa [hExecEq] using hExecQ'
    exact hNotExecP hExecP

/-- `DAOInvariant` is preserved by executing a proposal under the guarded
    update `executeUpdate`. -/
theorem DAOInvariant_executeProposal
    (st : DAOState) (pid : Nat) :
    DAOInvariant st → DAOInvariant (daoStep st (.executeProposal pid)) := by
  intro h
  rcases h with ⟨hExec, hTime, hVeto⟩
  refine And.intro ?hExec' (And.intro ?hTime' ?hVeto')
  · -- Proposal execution correctness.
    intro q hq hExecQ
    -- Relate `q` in the post-state to some `p` in the pre-state.
    rcases List.mem_map.1 hq with ⟨p, hp, hEq⟩
    have hExecUpdate :
        (executeUpdate st pid p).executed := by
      simpa [hEq] using hExecQ
    -- Either `p` was already executed, or the guard held.
    have hCase :
        p.executed ∨ canExecute st pid p :=
      executeUpdate_exec_cases st pid p hExecUpdate
    -- In both cases we obtain `ProposalPassed st p`.
    have hPassedP : ProposalPassed st p := by
      cases hCase with
      | inl hPE =>
          exact hExec p hp hPE
      | inr hCan =>
          -- `canExecute` includes `ProposalPassed st p` in its conjunction.
          exact hCan.right.left
    -- Transport `ProposalPassed` through `executeUpdate` and the equality `hEq`.
    have hPassedUpdate :
        ProposalPassed st (executeUpdate st pid p) :=
      ProposalPassed_executeUpdate st pid p hPassedP
    have hPassedQ_st :
        ProposalPassed st q := by
      simpa [hEq] using hPassedUpdate
    -- Lift to the post-state; `params` and `currentTime` are unchanged.
    have hPassedQ :
        ProposalPassed (daoStep st (.executeProposal pid)) q := by
      simpa [daoStep, ProposalPassed] using hPassedQ_st
    exact hPassedQ
  · -- Timelock security.
    intro q hq hExecQ
    rcases List.mem_map.1 hq with ⟨p, hp, hEq⟩
    have hExecUpdate :
        (executeUpdate st pid p).executed := by
      simpa [hEq] using hExecQ
    have hCase :
        p.executed ∨ canExecute st pid p :=
      executeUpdate_exec_cases st pid p hExecUpdate
    -- Timelock bound for `p` in the pre-state.
    have hTimeOld :
        st.currentTime ≥ p.endTime + st.params.timelock := by
      cases hCase with
      | inl hPE =>
          -- Use the original timelock security when `p` was already executed.
          exact hTime p hp hPE
      | inr hCan =>
          -- `canExecute` includes the timelock bound as its third conjunct.
          exact hCan.right.right.left
    -- `endTime` is preserved by `executeUpdate`.
    have hend :
        (executeUpdate st pid p).endTime = p.endTime :=
      executeUpdate_preserves_endTime st pid p
    -- Rewrite the bound for `q` in the old state.
    have hTimeQ_st :
        st.currentTime ≥
          q.endTime + st.params.timelock := by
      have hTimeOld' :
          st.currentTime ≥
            (executeUpdate st pid p).endTime + st.params.timelock := by
        simpa [hend] using hTimeOld
      simpa [hEq] using hTimeOld'
    -- Upgrade to the post-state, where `currentTime` and `params` are unchanged.
    have hTimeQ :
        (daoStep st (.executeProposal pid)).currentTime ≥
          q.endTime + (daoStep st (.executeProposal pid)).params.timelock := by
      simpa [daoStep] using hTimeQ_st
    exact hTimeQ
  · -- Veto mechanisms correctness.
    intro q hq hVetoQ
    rcases List.mem_map.1 hq with ⟨p, hp, hEq⟩
    -- Transport veto flag back to `p`.
    have hVetoEq :
        (executeUpdate st pid p).vetoed = p.vetoed :=
      executeUpdate_preserves_veto st pid p
    have hVetoP : p.vetoed := by
      have hVetoQ' : (executeUpdate st pid p).vetoed := by
        simpa [hEq] using hVetoQ
      simpa [hVetoEq] using hVetoQ'
    -- Original invariant forbids executed & vetoed for `p`.
    have hNotExecP : ¬ p.executed := hVeto p hp hVetoP
    -- Show that `q.executed` leads to a contradiction.
    intro hExecQ
    have hExecUpdate :
        (executeUpdate st pid p).executed := by
      simpa [hEq] using hExecQ
    have hCase2 :
        p.executed ∨ canExecute st pid p :=
      executeUpdate_exec_cases st pid p hExecUpdate
    cases hCase2 with
    | inl hPE =>
        -- Direct contradiction with the original invariant.
        exact hNotExecP hPE
    | inr hCan =>
        -- `canExecute` includes `ProposalPassed`, whose last conjunct is
        -- `¬ p.vetoed`, contradicting `p.vetoed`.
        have hPassedP : ProposalPassed st p := hCan.right.left
        have hNotVeto : ¬ p.vetoed := hPassedP.right.right.right
        exact hNotVeto hVetoP

/-- `DAOInvariant` is preserved by vetoing a proposal under the guarded
    update `vetoUpdate`. -/
theorem DAOInvariant_vetoProposal
    (st : DAOState) (pid : Nat) :
    DAOInvariant st → DAOInvariant (daoStep st (.vetoProposal pid)) := by
  intro h
  rcases h with ⟨hExec, hTime, hVeto⟩
  refine And.intro ?hExec' (And.intro ?hTime' ?hVeto')
  · -- Proposal execution correctness: executed proposals are unchanged.
    intro q hq hExecQ
    -- Relate `q` in the post-state to some `p` in the pre-state.
    rcases List.mem_map.1 hq with ⟨p, hp, hEq⟩
    have hExecUpdate :
        (vetoUpdate pid p).executed := by
      simpa [hEq] using hExecQ
    -- Transport execution back to the pre-state using the preservation lemma.
    have hExecEq :
        (vetoUpdate pid p).executed = p.executed :=
      vetoUpdate_preserves_executed pid p
    have hExecP : p.executed := by
      simpa [hExecEq] using hExecUpdate
    -- If `p` is executed, the veto guard `p.id = pid ∧ p.executed = false` is
    -- impossible, so `vetoUpdate` is the identity on `p`.
    have hGuardFalse : ¬ (p.id = pid ∧ p.executed = false) := by
      intro hGuard
      -- From `p.executed = true` and `p.executed = false` we derive a contradiction.
      have : p.executed = false := hGuard.right
      have : False := by
        have hExecFalse := this
        simp [hExecP] at hExecFalse
      exact this
    have hUpdate_eq_p : vetoUpdate pid p = p := by
      unfold vetoUpdate
      by_cases hGuard : p.id = pid ∧ p.executed = false
      · exact (hGuardFalse hGuard).elim
      · simp [hGuard]
    -- Use the original execution correctness on `p`.
    have hPassP : ProposalPassed st p := hExec p hp hExecP
    -- Transport `ProposalPassed` from `p` to `q` via the equality obtained above.
    have hpq : p = q := by
      simpa [hUpdate_eq_p] using hEq
    have hPassedQ_st :
        ProposalPassed st q := by
      simpa [hpq] using hPassP
    -- Lift to the post-state; `params` and `currentTime` are unchanged.
    have hPassedQ :
        ProposalPassed (daoStep st (.vetoProposal pid)) q := by
      simpa [daoStep, ProposalPassed] using hPassedQ_st
    exact hPassedQ
  · -- Timelock security: executed proposals are unchanged.
    intro q hq hExecQ
    rcases List.mem_map.1 hq with ⟨p, hp, hEq⟩
    have hExecUpdate :
        (vetoUpdate pid p).executed := by
      simpa [hEq] using hExecQ
    have hExecEq :
        (vetoUpdate pid p).executed = p.executed :=
      vetoUpdate_preserves_executed pid p
    have hExecP : p.executed := by
      simpa [hExecEq] using hExecUpdate
    -- Apply the original timelock condition to `p`.
    have hTimeOld :
        st.currentTime ≥ p.endTime + st.params.timelock :=
      hTime p hp hExecP
    -- As above, the guard is impossible for an executed proposal, so
    -- `vetoUpdate` is the identity on `p`.
    have hGuardFalse : ¬ (p.id = pid ∧ p.executed = false) := by
      intro hGuard
      have : p.executed = false := hGuard.right
      have : False := by
        have hExecFalse := this
        simp [hExecP] at hExecFalse
      exact this
    have hUpdate_eq_p : vetoUpdate pid p = p := by
      unfold vetoUpdate
      by_cases hGuard : p.id = pid ∧ p.executed = false
      · exact (hGuardFalse hGuard).elim
      · simp [hGuard]
    -- Rewrite the timelock bound to talk about `q` in the old state.
    have hpq : p = q := by
      simpa [hUpdate_eq_p] using hEq
    have hTimeQ_st :
        st.currentTime ≥
          q.endTime + st.params.timelock := by
      simpa [hpq] using hTimeOld
    -- Upgrade to the post-state.
    have hTimeQ :
        (daoStep st (.vetoProposal pid)).currentTime ≥
          q.endTime + (daoStep st (.vetoProposal pid)).params.timelock := by
      simpa [daoStep] using hTimeQ_st
    exact hTimeQ
  · -- Veto mechanisms correctness: vetoed proposals remain non-executed.
    intro q hq hVetoQ
    rcases List.mem_map.1 hq with ⟨p, hp, hEq⟩
    have hVetoUpdate :
        (vetoUpdate pid p).vetoed := by
      simpa [hEq] using hVetoQ
    -- Show that `q.executed` leads to a contradiction.
    intro hExecQ
    have hExecUpdate :
        (vetoUpdate pid p).executed := by
      simpa [hEq] using hExecQ
    have hExecEq :
        (vetoUpdate pid p).executed = p.executed :=
      vetoUpdate_preserves_executed pid p
    have hExecP : p.executed := by
      simpa [hExecEq] using hExecUpdate
    -- Analyse whether the veto guard fired.
    unfold vetoUpdate at hVetoUpdate
    by_cases hGuard : p.id = pid ∧ p.executed = false
    · -- Guard branch: we derive `p.executed = false`, contradicting `p.executed = true`.
      have hExecFalse : p.executed = false := hGuard.right
      have : False := by
        have hExecFalse' := hExecFalse
        simp [hExecP] at hExecFalse'
      exact this.elim
    · -- Else branch: the proposal is unchanged and `p.vetoed` holds in the pre-state.
      have hVetoP : p.vetoed := by
        simpa [hGuard] using hVetoUpdate
      have hNotExecP : ¬ p.executed := hVeto p hp hVetoP
      exact hNotExecP hExecP

/-- `DAOInvariant` is preserved along any finite sequence of actions. -/
theorem DAOInvariant_run
    (st : DAOState) (acts : List DAOAction) :
    DAOInvariant st → DAOInvariant (daoRun st acts) := by
  induction acts generalizing st with
  | nil =>
      intro h
      simpa [daoRun] using h
  | cons a as ih =>
      intro h
      have hStep : DAOInvariant (daoStep st a) := by
        cases a with
        | advanceTime dt =>
            exact DAOInvariant_advanceTime st dt h
        | addProposal p =>
            exact DAOInvariant_addProposal st p h
        | castVote pid b =>
            exact DAOInvariant_castVote st pid b h
        | executeProposal pid =>
            exact DAOInvariant_executeProposal st pid h
        | vetoProposal pid =>
            exact DAOInvariant_vetoProposal st pid h
      have hRun : DAOInvariant (daoRun (daoStep st a) as) :=
        ih (daoStep st a) hStep
      simpa [daoRun, List.foldl] using hRun

/-- Reachability in the DAO model via `daoRun`. -/
def DAOReachable (st₀ st : DAOState) : Prop :=
  ∃ acts : List DAOAction, daoRun st₀ acts = st

/-- Bundled invariant statement: any run starting from a state that
    satisfies `DAOInvariant` preserves the invariant. -/
def DAOInvariantStatement : Prop :=
  ∀ st₀ acts, DAOInvariant st₀ → DAOInvariant (daoRun st₀ acts)

/-- Proof that `DAOInvariantStatement` holds. -/
theorem daoInvariantStatement_holds : DAOInvariantStatement := by
  intro st₀ acts h0
  exact DAOInvariant_run st₀ acts h0

end Model
end Governance
end HeytingLean
