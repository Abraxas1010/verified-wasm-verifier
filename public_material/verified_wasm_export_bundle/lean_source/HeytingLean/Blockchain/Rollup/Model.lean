import HeytingLean.Blockchain.Rollup.StateTransition
import HeytingLean.Crypto.Form
import HeytingLean.Crypto.CoreSemantics

/-
# Blockchain.Rollup.Model

Minimal concrete rollup model layered on top of the generic
`Blockchain.Rollup.StateTransition.Spec` structure.

This file does **not** aim to be a full rollup semantics; instead it:

* introduces a simple `Account`/`Tx`/`State` model with a state
  commitment field;
* provides a basic `Spec` instantiation in terms of a `Form`/environment;
* records, as `Prop`s, the intended single-step and multi-step
  correctness statements that Section 3 refers to.

The proofs of these statements are left for later dedicated development;
here we focus on exposing a stable API that other modules can depend on.
-/

namespace HeytingLean
namespace Blockchain
namespace Rollup

open HeytingLean.LoF
open HeytingLean.Crypto

universe u v

variable {α : Type u} [PrimaryAlgebra α]
variable {R : Reentry α}

/-- A minimal account model for a rollup: address, balance, and nonce. -/
structure Account where
  addr    : Nat
  balance : Int
  nonce   : Nat
  deriving Repr, Inhabited, DecidableEq

/-- A minimal transaction model: sender, recipient, and amount. -/
structure Tx where
  fromAddr : Nat
  toAddr   : Nat
  amount   : Int
  deriving Repr, Inhabited, DecidableEq

/-- A minimal rollup state: a list of accounts plus an abstract state
    commitment (e.g. a Merkle root or other hash). -/
structure State where
  accounts : List Account
  commit   : String
  deriving Repr, Inhabited, DecidableEq

/-- Apply a single transaction to a rollup state at the abstract level.

This function does **not** attempt to model all edge cases; it simply
captures the idea that balances are updated while the commitment is left
to be recomputed by an external function. -/
def applyTx (s : State) (tx : Tx) : State :=
  let upd (a : Account) : Account :=
    if a.addr = tx.fromAddr then
      { a with balance := a.balance - tx.amount, nonce := a.nonce + 1 }
    else if a.addr = tx.toAddr then
      { a with balance := a.balance + tx.amount }
    else
      a
  { s with accounts := s.accounts.map upd }

/-- A concrete nontrivial example: applying a transaction can change
the rollup state (balances/nonce), so the model is not degenerate. -/
theorem applyTx_nontrivial_example :
    ∃ (s : State) (tx : Tx), applyTx s tx ≠ s := by
  classical
  let aFrom : Account := { addr := 0, balance := 0, nonce := 0 }
  let aTo : Account := { addr := 1, balance := 0, nonce := 0 }
  let s : State := { accounts := [aFrom, aTo], commit := "" }
  let tx : Tx := { fromAddr := 0, toAddr := 1, amount := 1 }
  refine ⟨s, tx, ?_⟩
  decide

/-- Apply a list of transactions sequentially. -/
def applyTxs (s : State) (txs : List Tx) : State :=
  txs.foldl applyTx s

/-- Composition law for `applyTxs` over list append. -/
lemma applyTxs_append (s : State) (txs₁ txs₂ : List Tx) :
    applyTxs s (txs₁ ++ txs₂) =
      applyTxs (applyTxs s txs₁) txs₂ := by
  simp [applyTxs, List.foldl_append]

/-- Abstract state-commitment updater: for now, a simple function
    from state to commitment string. Concrete rollup models can supply a
    more refined hash/Merkle implementation. -/
def updateCommit (s : State) : String :=
  s!"commit:{s.accounts.length}"

/-- A simple rollup transition spec: given a list of transactions,
    `State` evolves by applying them and updating the commitment.

To relate the abstract `Spec.State` used in the core Ωᵣ layer to the
concrete `State` defined above, we provide explicit `encode`/`decode`
maps. Concrete instantiations can choose these to be identities or
structured embeddings as appropriate. -/
structure StepSpec (R : Reentry α) (n : ℕ) where
  txs   : List Tx
  spec  : Spec.{u, v} (R := R) n
  encode : State → spec.State
  decode : spec.State → State

namespace StepSpec

/-- A basic instantiation of `Spec` where the `Form` is `⊤` and the
    environment is constant `⊤`. This makes `validTransition` coincide
    with the abstract `applyTxs`/`updateCommit` relation recorded below. -/
def basic (R : Reentry α) : StepSpec (R := R) 1 :=
  { txs := []
    spec :=
      { State := State
        transitionForm := fun _ _ => Crypto.Form.top
        env := fun _ _ _ => (⊤ : R.Omega) }
    encode := id
    decode := id }

end StepSpec

/-- Ωᵣ-level rollup spec that ties `validTransition` to the concrete
    `applyTxs`/`updateCommit` relation for a fixed transaction list. -/
def specForTxs (R : Reentry α) (txs : List Tx) : Spec (R := R) 1 :=
  { State := State
    transitionForm := fun _ _ => Crypto.Form.var 0
    env := fun s₁ s₂ =>
      let s' := applyTxs s₁ txs
      fun _ =>
        if s₂ = { s' with commit := updateCommit s' } then
          (⊤ : R.Omega)
        else
          (⊥ : R.Omega) }

/-- For the concrete spec `specForTxs`, taking the post-state to be
    `applyTxs` followed by `updateCommit` yields a core-valid
    transition. -/
theorem specForTxs_valid (R : Reentry α) (txs : List Tx)
    (s₁ : State) :
    Spec.validTransition (R := R) (specForTxs (R := R) txs) s₁
      ({ applyTxs s₁ txs with commit := updateCommit (applyTxs s₁ txs) }) := by
  classical
  unfold Spec.validTransition
  -- Expand the evaluation of the single variable against the guarded environment.
  simp [specForTxs]

/-- Validity of a single concrete rollup step, relative to an abstract
    Ωᵣ-level specification and encode/decode maps.

Given a concrete initial state `s₁ : State`, we encode it into the
abstract state space of `spec`, take one core-valid transition, and
require that there exists an abstract post-state whose decoding
coincides with applying the transactions and updating the commitment at
the concrete level. -/
def RollupStepValidStatement
    (spec : Spec.{u, v} (R := R) n)
    (encode : State → spec.State)
    (decode : spec.State → State)
    (txs : List Tx) : Prop :=
  ∀ (s₁ : State),
    ∃ s₂' : spec.State,
      Spec.validTransition (R := R) spec (encode s₁) s₂' ∧
        let s' := applyTxs s₁ txs
        decode s₂' = { s' with commit := updateCommit s' }

/-- A specialised instance of `RollupStepValidStatement` for the basic
    always-true `Spec` from `StepSpec.basic`.

For any fixed transaction list `txs`, we can view `StepSpec.basic` as a
highly non-deterministic rollup step specification in which every
abstract transition is core-valid. The statement below exhibits, for
each concrete initial state `s₁`, a particular abstract post-state that
matches the result of replaying `txs` and updating the commitment. -/
theorem rollupStepValid_basic (R : Reentry α) (txs : List Tx) :
    RollupStepValidStatement (R := R) (n := 1)
      (spec := (StepSpec.basic (R := R)).spec)
      (encode := (StepSpec.basic (R := R)).encode)
      (decode := (StepSpec.basic (R := R)).decode)
      (txs := txs) := by
  intro s₁
  -- Take as abstract post-state the concrete state obtained by applying
  -- the transactions and updating the commitment.
  let s' : State := applyTxs s₁ txs
  refine ⟨{ s' with commit := updateCommit s' }, ?_⟩
  constructor
  · -- In the basic spec, every transition is core-valid because the
    -- transition formula is `⊤` with a constant `⊤` environment.
    simp [Rollup.StepSpec.basic, Spec.validTransition]
  · -- Decoding is the identity, so decoding the chosen abstract state
    -- recovers the intended concrete post-state.
    rfl

/-- Specialised instance of `RollupStepValidStatement` for the concrete
    spec `specForTxs`, where core validity *characterises* the intended
    `applyTxs`/`updateCommit` relation. -/
theorem rollupStepValid_concrete (R : Reentry α) (txs : List Tx) :
    RollupStepValidStatement (R := R) (n := 1)
      (spec := specForTxs (R := R) txs)
      (encode := id)
      (decode := id)
      (txs := txs) := by
  intro s₁
  let s' : State := applyTxs s₁ txs
  refine ⟨{ s' with commit := updateCommit s' }, ?_⟩
  constructor
  · -- Core validity follows directly from `specForTxs_valid`.
    simpa [specForTxs] using
      specForTxs_valid (R := R) (txs := txs) s₁
  · rfl

/-- Canonical concrete post-state for a single batch of transactions. -/
def concretePost (s₀ : State) (txs : List Tx) : State :=
  let s' := applyTxs s₀ txs
  { s' with commit := updateCommit s' }

/-- Repeat a batch of transactions `k` times by concatenation. -/
def repeatTxs (txs : List Tx) (k : Nat) : List Tx :=
  Nat.recOn k [] (fun _ acc => acc ++ txs)

/-- One-step unfolding of `repeatTxs`. -/
lemma repeatTxs_succ (txs : List Tx) (k : Nat) :
    repeatTxs txs (Nat.succ k) =
      repeatTxs txs k ++ txs := by
  unfold repeatTxs
  simp

/-- Compatibility of `applyTxs` with repeated batches. -/
lemma applyTxs_repeat (s₀ : State) (txs : List Tx) :
    ∀ k,
      applyTxs s₀ (repeatTxs txs k) =
        Nat.recOn k s₀ (fun _ s => applyTxs s txs)
  := by
  intro k
  induction k with
  | zero =>
      simp [repeatTxs, applyTxs]
  | succ k ih =>
      simp [repeatTxs_succ, applyTxs_append, ih]

/-- Iterated concrete rollup state obtained by applying `concretePost`
    exactly `k` times starting from `s₀`. -/
def stateAfterSteps (s₀ : State) (txs : List Tx) : Nat → State
  | 0 => s₀
  | Nat.succ k => concretePost (stateAfterSteps s₀ txs k) txs

/-- If two states have the same `accounts` list then their
    `updateCommit` values coincide. -/
lemma updateCommit_eq_of_accounts_eq
    (s₁ s₂ : State)
    (h : s₁.accounts = s₂.accounts) :
    updateCommit s₁ = updateCommit s₂ := by
  simp [updateCommit, h]

/-- If two states have the same `accounts` list, then applying the same
    transaction list yields states with the same `accounts`. -/
lemma applyTxs_accounts_eq_of_accounts_eq
    (s₁ s₂ : State) (txs : List Tx)
    (h : s₁.accounts = s₂.accounts) :
    (applyTxs s₁ txs).accounts = (applyTxs s₂ txs).accounts := by
  induction txs generalizing s₁ s₂ with
  | nil =>
      simp [applyTxs, h]
  | cons tx txs ih =>
      -- One step of `applyTx`, then reuse the induction hypothesis.
      have hApply :
          (applyTx s₁ tx).accounts = (applyTx s₂ tx).accounts := by
        -- `applyTx` updates accounts by mapping a fixed function over them.
        unfold applyTx
        -- After rewriting with `h`, the mapped lists coincide.
        simp [h]
      -- Apply the hypothesis to the tails.
      have hTail :=
        ih (applyTx s₁ tx) (applyTx s₂ tx) hApply
      simpa [applyTxs] using hTail

/-- Big-batch description of the `accounts` component of
    `stateAfterSteps`: applying `txs` for `k` steps yields the same
    accounts as a single application of `applyTxs` to
    `repeatTxs txs k`. -/
lemma stateAfterSteps_accounts_bigBatch
    (s₀ : State) (txs : List Tx) :
    ∀ k,
      (stateAfterSteps s₀ txs k).accounts =
        (applyTxs s₀ (repeatTxs txs k)).accounts := by
  intro k
  induction k with
  | zero =>
      simp [stateAfterSteps, repeatTxs, applyTxs]
  | succ k ih =>
      -- Accounts after one more step on the left.
      have hLeft :
          (stateAfterSteps s₀ txs (Nat.succ k)).accounts =
            (applyTxs (stateAfterSteps s₀ txs k) txs).accounts := by
        simp [stateAfterSteps, concretePost]
      -- Accounts after one more repetition on the right.
      have hRight :
          (applyTxs s₀ (repeatTxs txs (Nat.succ k))).accounts =
            (applyTxs (applyTxs s₀ (repeatTxs txs k)) txs).accounts := by
        simp [repeatTxs_succ, applyTxs_append]
      -- Transport the induction hypothesis through a final `applyTxs`.
      have hStep :
          (applyTxs (stateAfterSteps s₀ txs k) txs).accounts =
            (applyTxs (applyTxs s₀ (repeatTxs txs k)) txs).accounts :=
        applyTxs_accounts_eq_of_accounts_eq
          (s₁ := stateAfterSteps s₀ txs k)
          (s₂ := applyTxs s₀ (repeatTxs txs k))
          (txs := txs) ih
      -- Glue the equalities.
      exact
        (hLeft.trans (hStep.trans hRight.symm))

/-- Helper lemma: equality of `State` values from equality of both
    fields. -/
lemma state_eq_of_accounts_commit_eq
    (s₁ s₂ : State)
    (hAcc : s₁.accounts = s₂.accounts)
    (hCommit : s₁.commit = s₂.commit) :
    s₁ = s₂ := by
  cases s₁; cases s₂; cases hAcc; cases hCommit; rfl

/-- Closed-form description of the commitment component of
    `stateAfterSteps` in terms of a single big-batch execution of
    `txs`. This is stated for `Nat.succ k` (at least one batch). -/
lemma stateAfterSteps_succ_commit_bigBatch
    (s₀ : State) (txs : List Tx) :
    ∀ k,
      (stateAfterSteps s₀ txs (Nat.succ k)).commit =
        updateCommit (applyTxs s₀ (repeatTxs txs (Nat.succ k))) := by
  intro k
  induction k with
  | zero =>
      -- One batch: this is just `concretePost s₀ txs`.
      simp [stateAfterSteps, concretePost, repeatTxs, applyTxs]
  | succ k ih =>
      -- Unfold the `(k+2)`-step state on the left.
      have hL :
          (stateAfterSteps s₀ txs (Nat.succ (Nat.succ k))).commit =
            updateCommit
              (applyTxs (stateAfterSteps s₀ txs (Nat.succ k)) txs) := by
        simp [stateAfterSteps, concretePost]
      -- Rewrite the right-hand side using `repeatTxs_succ` and
      -- `applyTxs_append`.
      have hR :
          updateCommit
              (applyTxs s₀ (repeatTxs txs (Nat.succ (Nat.succ k)))) =
            updateCommit
              (applyTxs (applyTxs s₀ (repeatTxs txs (Nat.succ k))) txs) := by
        simp [repeatTxs_succ, applyTxs_append]
      -- Use `stateAfterSteps_accounts_bigBatch` at step `Nat.succ k`
      -- to relate the accounts of the two intermediate states.
      have hAccountsStep :
          (stateAfterSteps s₀ txs (Nat.succ k)).accounts =
            (applyTxs s₀ (repeatTxs txs (Nat.succ k))).accounts := by
        simpa using
          stateAfterSteps_accounts_bigBatch s₀ txs (Nat.succ k)
      have hAccounts :
          (applyTxs (stateAfterSteps s₀ txs (Nat.succ k)) txs).accounts =
            (applyTxs (applyTxs s₀ (repeatTxs txs (Nat.succ k))) txs).accounts :=
        applyTxs_accounts_eq_of_accounts_eq
          (s₁ := stateAfterSteps s₀ txs (Nat.succ k))
          (s₂ := applyTxs s₀ (repeatTxs txs (Nat.succ k)))
          (txs := txs) hAccountsStep
      -- The commitment updater depends only on `accounts`, so it
      -- preserves this equality.
      have hCommit :
          updateCommit
              (applyTxs (stateAfterSteps s₀ txs (Nat.succ k)) txs) =
            updateCommit
              (applyTxs (applyTxs s₀ (repeatTxs txs (Nat.succ k))) txs) :=
        updateCommit_eq_of_accounts_eq _ _ hAccounts
      -- Assemble the equalities.
      simpa [hL, hR] using hCommit

/-- Big-batch concrete rollup state: result of applying `txs` for `k`
    batches starting from `s₀`, with the commitment recomputed once.

For `k = 0` this is just the initial state; for `k.succ` it coincides
with `applyTxs s₀ (repeatTxs txs k.succ)` followed by `updateCommit`. -/
def bigBatchState (s₀ : State) (txs : List Tx) (k : Nat) : State :=
  match k with
  | 0 => s₀
  | Nat.succ k' =>
      let s' := applyTxs s₀ (repeatTxs txs (Nat.succ k'))
      { s' with commit := updateCommit s' }

/-- Closed-form link between the iterated concrete rollup state defined
    by `stateAfterSteps` and the big-batch state obtained from a single
    application of `applyTxs` to `repeatTxs txs k`.

For `k = 0` this is definitionally the identity; for `k.succ` it
identifies `stateAfterSteps` with `bigBatchState`. -/
lemma stateAfterSteps_eq_bigBatch
    (s₀ : State) (txs : List Tx) :
    ∀ k, stateAfterSteps s₀ txs k =
      bigBatchState s₀ txs k := by
  intro k
  cases k with
  | zero =>
      simp [stateAfterSteps, bigBatchState]
  | succ k =>
      -- Prove equality by matching both the `accounts` and `commit`
      -- components.
      apply state_eq_of_accounts_commit_eq
      · -- `accounts` agree by `stateAfterSteps_accounts_bigBatch`.
        have hAccounts :
            (stateAfterSteps s₀ txs (Nat.succ k)).accounts =
              (applyTxs s₀ (repeatTxs txs (Nat.succ k))).accounts := by
          simpa using
            stateAfterSteps_accounts_bigBatch s₀ txs (Nat.succ k)
        simpa [bigBatchState] using hAccounts
      · -- `commit` agrees by `stateAfterSteps_succ_commit_bigBatch`.
        have hCommit :
            (stateAfterSteps s₀ txs (Nat.succ k)).commit =
              updateCommit
                (applyTxs s₀ (repeatTxs txs (Nat.succ k))) :=
          stateAfterSteps_succ_commit_bigBatch s₀ txs k
        simpa [bigBatchState] using hCommit

/-- Composition of `stateAfterSteps` over an intermediate point:
    starting from `s₀` and taking `k + i` batches is the same as first
    taking `k` batches and then taking `i` more from the resulting
    state. -/
lemma stateAfterSteps_add (s₀ : State) (txs : List Tx) :
    ∀ k i,
      stateAfterSteps s₀ txs (k + i) =
        stateAfterSteps (stateAfterSteps s₀ txs k) txs i := by
  intro k i
  induction i with
  | zero =>
      simp [stateAfterSteps]
  | succ i ih =>
      -- For the left-hand side, `k + (i+1)` is `Nat.succ (k + i)`.
      -- For the right-hand side, unfold one step of `stateAfterSteps`
      -- from the intermediate state and reuse the induction hypothesis.
      simp [stateAfterSteps, ih]

/-- Iterated concrete rollup chain built from `stateAfterSteps`:
    after `k` batches we collect the successive post-states
    `stateAfterSteps s₀ txs 1, …, stateAfterSteps s₀ txs k`. -/
def iteratedChain (s₀ : State) (txs : List Tx) : Nat → List State
  | 0 => []
  | Nat.succ k =>
      List.concat (iteratedChain s₀ txs k)
        (stateAfterSteps s₀ txs (Nat.succ k))

@[simp]
lemma iteratedChain_zero (s₀ : State) (txs : List Tx) :
    iteratedChain s₀ txs 0 = [] := by
  rfl

@[simp]
lemma iteratedChain_succ (s₀ : State) (txs : List Tx) (k : Nat) :
    iteratedChain s₀ txs (Nat.succ k) =
      iteratedChain s₀ txs k ++ [stateAfterSteps s₀ txs (Nat.succ k)] := by
  simp [iteratedChain, List.concat_eq_append]

/-- Reverse of `iteratedChain` at `Nat.succ k`: the head of the reversed
    list is exactly the `k.succ`-step concrete state. -/
lemma iteratedChain_reverse_succ (s₀ : State) (txs : List Tx) (k : Nat) :
    (iteratedChain s₀ txs (Nat.succ k)).reverse =
      stateAfterSteps s₀ txs (Nat.succ k) ::
        (iteratedChain s₀ txs k).reverse := by
  -- Use the append definition and the standard reverse-append lemma.
  simp [iteratedChain, List.concat_eq_append, List.reverse_append]

/-- The last state in the iterated chain after `k.succ` batches is
    `stateAfterSteps s₀ txs (k.succ)`. We phrase this using `reverse`
    so that it mirrors the shape used in `RollupChainValidStatement`. -/
lemma iteratedChain_last_stateAfterSteps (s₀ : State) (txs : List Tx) (k : Nat) :
    match (iteratedChain s₀ txs (Nat.succ k)).reverse with
    | [] => False
    | sLast :: _ => sLast = stateAfterSteps s₀ txs (Nat.succ k) := by
  simp [iteratedChain, List.concat_eq_append, List.reverse_append]

/-- Closed-form description of the last state in the iterated chain
    after `k.succ` batches: it coincides with the big-batch state
    obtained from `repeatTxs` and a single `updateCommit`. -/
lemma iteratedChain_last_bigBatch (s₀ : State) (txs : List Tx) (k : Nat) :
    match (iteratedChain s₀ txs (Nat.succ k)).reverse with
    | [] => False
    | sLast :: _ => sLast = bigBatchState s₀ txs (Nat.succ k) := by
  have hStep :
      stateAfterSteps s₀ txs (Nat.succ k) =
        bigBatchState s₀ txs (Nat.succ k) :=
    stateAfterSteps_eq_bigBatch (s₀ := s₀) (txs := txs) (k := Nat.succ k)
  simp [iteratedChain, List.concat_eq_append, List.reverse_append, hStep]

/-- `getLast`-based description of the last state in the iterated
    concrete rollup chain after `k.succ` batches: it is exactly the
    `k.succ`-step concrete state `stateAfterSteps`. -/
lemma iteratedChain_getLast_stateAfterSteps
    (s₀ : State) (txs : List Tx) (k : Nat) :
    List.getLast (iteratedChain s₀ txs (Nat.succ k))
      (by simp [iteratedChain]) =
      stateAfterSteps s₀ txs (Nat.succ k) := by
  simp [iteratedChain]

/-- `getLast`-based big-batch description of the last state in the
    iterated concrete chain after `k.succ` batches. -/
lemma iteratedChain_getLast_bigBatch
    (s₀ : State) (txs : List Tx) (k : Nat) :
    List.getLast (iteratedChain s₀ txs (Nat.succ k))
      (by simp [iteratedChain]) =
      bigBatchState s₀ txs (Nat.succ k) := by
  have h :=
    iteratedChain_getLast_stateAfterSteps (s₀ := s₀) (txs := txs) (k := k)
  have hStep :
      stateAfterSteps s₀ txs (Nat.succ k) =
        bigBatchState s₀ txs (Nat.succ k) :=
    stateAfterSteps_eq_bigBatch (s₀ := s₀) (txs := txs) (k := Nat.succ k)
  exact h.trans hStep


/-- Singleton chain containing the canonical concrete post-state. -/
def concreteSteps (s₀ : State) (txs : List Tx) : List State :=
  [concretePost s₀ txs]

/-- Auxiliary definition: build a `k`-step concrete chain by repeatedly
    applying `concretePost`. -/
def concreteChainAux (s : State) (txs : List Tx) : Nat → List State
  | 0 => []
  | Nat.succ k =>
      let s' := concretePost s txs
      s' :: concreteChainAux s' txs k

/-- `k`-step concrete rollup chain starting from `s₀`. -/
def concreteChain (s₀ : State) (txs : List Tx) (k : Nat) : List State :=
  concreteChainAux s₀ txs k

/-- Core-valid chain for a fixed abstract specification: each adjacent
    pair of abstract states satisfies `Spec.validTransition`. -/
def ValidChain (spec : Spec.{u, v} (R := R) n)
    (s₀' : spec.State) (steps : List spec.State) : Prop :=
  match steps with
  | [] => True
  | s₁' :: rest =>
      Spec.validTransition (R := R) spec s₀' s₁' ∧
      ValidChain spec s₁' rest

/-- Any `k`-step concrete chain for `specForTxs` is core-valid. -/
lemma concreteChain_valid (R : Reentry α) (txs : List Tx) :
    ∀ (k : Nat) (s₀ : State),
      ValidChain (R := R) (n := 1)
        (spec := specForTxs (R := R) txs)
        (s₀' := s₀)
        (steps := concreteChain s₀ txs k) := by
  classical
  intro k s₀
  induction k generalizing s₀ with
  | zero =>
      simp [concreteChain, concreteChainAux, ValidChain]
  | succ k ih =>
      -- First step: `s₀` transitions to `concretePost s₀ txs`.
      have hStep :
          Spec.validTransition (R := R) (specForTxs (R := R) txs) s₀
            (concretePost s₀ txs) := by
        simpa [concretePost, specForTxs] using
          specForTxs_valid (R := R) (txs := txs) s₀
      -- Remaining steps form a valid chain from `concretePost s₀ txs`.
      have hTail :
          ValidChain (R := R) (n := 1)
            (spec := specForTxs (R := R) txs)
            (s₀' := concretePost s₀ txs)
            (steps := concreteChain (concretePost s₀ txs) txs k) :=
        ih (concretePost s₀ txs)
      -- Package the head step with the inductive tail.
      have hPair :
          Spec.validTransition (R := R) (specForTxs (R := R) txs) s₀
            (concretePost s₀ txs) ∧
          ValidChain (R := R) (n := 1)
            (spec := specForTxs (R := R) txs)
            (s₀' := concretePost s₀ txs)
            (steps := concreteChain (concretePost s₀ txs) txs k) :=
        ⟨hStep, hTail⟩
      simpa [concreteChain, concreteChainAux, ValidChain] using hPair

/-- Multi-step rollup correctness statement.

Starting from a concrete state `s₀`, we encode it into the abstract
state space, follow a chain of core-valid transitions, and require that
decoding the final abstract state agrees with replaying the same
transactions at the concrete level and updating the commitment. -/
def RollupChainValidStatement (R : Reentry α) (n : ℕ) : Prop :=
  ∀ (spec : Spec.{u, v} (R := R) n)
    (encode : State → spec.State)
    (decode : spec.State → State)
    (txs : List Tx)
    (s₀ : State) (steps : List spec.State),
    ValidChain spec (encode s₀) steps →
      match steps.reverse with
      | [] =>
          -- No steps: decoded initial abstract state matches the
          -- concrete state and its commitment.
          decode (encode s₀) =
            let s' := applyTxs s₀ txs
            { s' with commit := updateCommit s' }
      | sLast' :: _ =>
          decode sLast' =
            let s' := applyTxs s₀ txs
            { s' with commit := updateCommit s' }

/-- One-step chain lemma for the concrete rollup spec `specForTxs`.

Starting from any `s₀`, the singleton chain containing `concretePost s₀ txs`
is core-valid, and its final abstract state coincides with `concretePost`
itself. This mirrors the shape of `RollupChainValidStatement` for the
specialised concrete spec. -/
theorem rollupChainValid_concrete_oneStep (R : Reentry α) (txs : List Tx)
    (s₀ : State) :
    ValidChain (R := R) (n := 1)
        (spec := specForTxs (R := R) txs)
        (s₀' := s₀)
        (steps := concreteSteps s₀ txs) ∧
      match (concreteSteps s₀ txs).reverse with
      | [] => True
      | sLast' :: _ => sLast' = concretePost s₀ txs := by
  classical
  -- Single-step core validity for the concrete spec.
  have hStep :
      Spec.validTransition (R := R) (specForTxs (R := R) txs) s₀
        (concretePost s₀ txs) := by
    -- Unfold `concretePost` and reuse `specForTxs_valid`.
    simpa [concretePost, specForTxs] using
      specForTxs_valid (R := R) (txs := txs) s₀
  -- Package this into a `ValidChain` over the singleton list.
  have hChain :
      ValidChain (R := R) (n := 1)
        (spec := specForTxs (R := R) txs)
        (s₀' := s₀)
        (steps := concreteSteps s₀ txs) := by
    -- By definition, a singleton chain is this step together with `True`.
    have hPair :
        Spec.validTransition (R := R) (specForTxs (R := R) txs) s₀
          (concretePost s₀ txs) ∧ True :=
      ⟨hStep, trivial⟩
    simpa [ValidChain, concreteSteps] using hPair
  -- The last element of the singleton chain is `concretePost s₀ txs`.
  have hLast :
      match (concreteSteps s₀ txs).reverse with
      | [] => True
      | sLast' :: _ => sLast' = concretePost s₀ txs := by
    simp [concreteSteps, concretePost]
  exact ⟨hChain, hLast⟩

end Rollup
end Blockchain
end HeytingLean
