import HeytingLean.Blockchain.MerkleModel
import HeytingLean.Crypto.Commit
import Mathlib.Data.Int.Basic

/-
# Privacy.Model

Abstract mixer and confidential-transaction models.

This module introduces:
* a minimal mixer state with commitments and nullifiers; and
* a sketch of confidential-transaction state and balance invariants.

These models are intentionally lightweight; they serve as anchors for the
properties listed in `Privacy.Spec.PropertyId`.
-/

namespace HeytingLean
namespace Privacy
namespace Model

open HeytingLean.Blockchain

/-- A mixer note: identifier, owner, and value. -/
structure Note where
  id    : String
  owner : String
  value : Nat
  deriving Repr

/-- Mixer state with committed notes (by commitment string) and a set of
    spent nullifiers. -/
structure MixerState where
  commitments : List String
  nullifiers  : List String
  deriving Repr

/-- Record a new deposit by adding a commitment. -/
def deposit (s : MixerState) (commitment : String) : MixerState :=
  { s with commitments := commitment :: s.commitments }

/-- Record a withdrawal by adding a nullifier. -/
def withdraw (s : MixerState) (nullifier : String) : MixerState :=
  { s with nullifiers := nullifier :: s.nullifiers }

/-- Nullifier uniqueness: the list of nullifiers has no duplicates, so
    the same nullifier is never recorded twice. This is the core
    no-double-spend condition for mixer notes at the model level. -/
def NullifierUnique (s : MixerState) : Prop :=
  s.nullifiers.Nodup

/-- Basic mixer conservation: every recorded nullifier must correspond
    to a previously recorded commitment. In this lightweight model we
    do not track values explicitly; instead we require that withdrawals
    always reference deposited commitments. -/
def MixerConservation (s : MixerState) : Prop :=
  ∀ {n : String}, n ∈ s.nullifiers → n ∈ s.commitments

/-- Deposits leave the nullifier set unchanged, so nullifier uniqueness
    is preserved. -/
lemma deposit_preserves_NullifierUnique
    (s : MixerState) (c : String)
    (h : NullifierUnique s) :
    NullifierUnique (deposit s c) := by
  dsimp [NullifierUnique, deposit] at *
  simpa using h

/-- Withdrawals preserve nullifier uniqueness provided the new
    nullifier is fresh. -/
lemma withdraw_preserves_NullifierUnique
    (s : MixerState) (n : String)
    (hUnique : NullifierUnique s)
    (hFresh : n ∉ s.nullifiers) :
    NullifierUnique (withdraw s n) := by
  dsimp [NullifierUnique, withdraw] at *
  simpa [List.nodup_cons, hFresh] using hUnique

/-- Deposits preserve mixer conservation: adding an extra commitment
    does not invalidate the “nullifiers come from commitments”
    invariant. -/
lemma deposit_preserves_MixerConservation
    (s : MixerState) (c : String)
    (h : MixerConservation s) :
    MixerConservation (deposit s c) := by
  intro n hn
  have hIn : n ∈ s.commitments := h hn
  simp [deposit, hIn]

/-- Withdrawals preserve mixer conservation when the new nullifier
    corresponds to an existing commitment. -/
lemma withdraw_preserves_MixerConservation
    (s : MixerState) (n : String)
    (h : MixerConservation s)
    (hCommit : n ∈ s.commitments) :
    MixerConservation (withdraw s n) := by
  intro m hm
  have hm' : m = n ∨ m ∈ s.nullifiers := by
    simpa [withdraw] using hm
  cases hm' with
  | inl hEq =>
      subst hEq
      exact hCommit
  | inr hInNull =>
      exact h hInNull

/-- Public projection of a mixer state: counts of commitments and
    nullifiers. This is the simple anonymity-set view used in
    trace-level anonymity statements. -/
def MixerState.publicView (s : MixerState) : Nat × Nat :=
  (s.commitments.length, s.nullifiers.length)

/-- Mixer operations: either record a deposit (by commitment string) or
    a withdrawal (by nullifier). -/
inductive MixerOp
  | deposit (commitment : String)
  | withdraw (nullifier : String)
  deriving Repr

/-- Apply a single mixer operation to a mixer state. -/
def applyMixerOp (s : MixerState) (op : MixerOp) : MixerState :=
  match op with
  | MixerOp.deposit c   => deposit s c
  | MixerOp.withdraw n  => withdraw s n

/-- Run a sequence of mixer operations by folding `applyMixerOp`
    from an initial state. -/
def runMixerOps (s : MixerState) (ops : List MixerOp) : MixerState :=
  ops.foldl applyMixerOp s

/-- Public view of a mixer trace: the sequence of public projections
    of the states seen along the trace, starting from the initial
    state. -/
def mixerTraceView : MixerState → List MixerOp → List (Nat × Nat)
  | s, [] => [s.publicView]
  | s, op :: ops => s.publicView :: mixerTraceView (applyMixerOp s op) ops

/-- Mixer invariants bundled together: nullifier uniqueness and the
    “withdrawals come from deposits” conservation property. -/
def MixerInvariants (s : MixerState) : Prop :=
  NullifierUnique s ∧ MixerConservation s

/-- Well-formedness of a mixer operation trace relative to an initial
    state: every withdrawal in the trace must correspond to an existing
    commitment at the point where it is applied, and must use a fresh
    nullifier. This ensures that the `MixerConservation` and
    `NullifierUnique` invariants can be propagated along the trace. -/
def MixerTraceWellFormed : MixerState → List MixerOp → Prop
  | _, [] => True
  | s, MixerOp.deposit c :: ops =>
      MixerTraceWellFormed (deposit s c) ops
  | s, MixerOp.withdraw n :: ops =>
      n ∈ s.commitments ∧ n ∉ s.nullifiers ∧
        MixerTraceWellFormed (withdraw s n) ops

/-- A well-formed mixer trace preserves the bundled `MixerInvariants`
    predicate when run from any initial state satisfying these
    invariants. -/
lemma runMixerOps_preserves_MixerInvariants
    (s : MixerState) (ops : List MixerOp)
    (hInv : MixerInvariants s)
    (hWF : MixerTraceWellFormed s ops) :
    MixerInvariants (runMixerOps s ops) := by
  classical
  revert s hInv hWF
  induction ops with
  | nil =>
      intro s hInv hWF
      simpa [runMixerOps] using hInv
  | cons op ops ih =>
      intro s hInv hWF
      cases op with
      | deposit c =>
          -- Deposit case: invariants preserved unconditionally, and
          -- well-formedness propagates to the tail on the updated state.
          have hInv' : MixerInvariants (deposit s c) := by
            rcases hInv with ⟨hUnique, hCons⟩
            refine And.intro
              (deposit_preserves_NullifierUnique s c hUnique)
              (deposit_preserves_MixerConservation s c hCons)
          have hWF' : MixerTraceWellFormed (deposit s c) ops := by
            simpa [MixerTraceWellFormed] using hWF
          have hTail :=
            ih (deposit s c) hInv' hWF'
          simpa [runMixerOps, applyMixerOp, List.foldl] using hTail
      | withdraw n =>
          -- Withdraw case: use the well-formedness side-condition for
          -- both conservation and uniqueness, then recurse.
          rcases hInv with ⟨hUnique, hCons⟩
          rcases hWF with ⟨hCommit, hFresh, hWF'⟩
          have hInv' : MixerInvariants (withdraw s n) := by
            refine And.intro
              (withdraw_preserves_NullifierUnique s n hUnique hFresh)
              (withdraw_preserves_MixerConservation s n hCons hCommit)
          have hTail :=
            ih (withdraw s n) hInv' hWF'
          simpa [runMixerOps, applyMixerOp, List.foldl] using hTail

/-- Confidential-transaction balance entry: a commitment and a signed
    value (for specification purposes), together with an abstract
    asset-type tag. -/
structure CTBalance where
  commitment : String
  asset      : String
  value      : Int
  deriving Repr

/-- Minimal confidential-transaction state: a list of balances. -/
structure CTState where
  balances : List CTBalance
  deriving Repr

/-- Total signed value of all confidential balances in a state. -/
def CTState.totalValue (s : CTState) : Int :=
  (s.balances.map (fun b => b.value)).sum

/-- Public projection of a confidential-transaction state that erases
    asset-type information, keeping only commitments and signed values.
    This is the “observable” part of the state for simple
    asset-hiding-style properties. -/
def CTState.eraseAssets (s : CTState) : List (String × Int) :=
  s.balances.map (fun b => (b.commitment, b.value))

/-- A confidential-transaction delta: a finite list of balance entries
    whose signed values sum to zero. Applying such a delta extends the
    balance list without changing the global total value. -/
structure CTDelta where
  balances : List CTBalance
  sumZero  : (balances.map (fun b => b.value)).sum = 0
  deriving Repr

/-- Apply a confidential-transaction delta by appending its balances to
    the existing list of balances. -/
def applyDelta (s : CTState) (d : CTDelta) : CTState :=
  { balances := s.balances ++ d.balances }

/-- Total value after applying a delta is the sum of the original total
    and the delta’s total. -/
lemma applyDelta_totalValue (s : CTState) (d : CTDelta) :
    (applyDelta s d).totalValue =
      s.totalValue +
        (d.balances.map (fun b => b.value)).sum := by
  unfold CTState.totalValue applyDelta
  -- Local lemma: sum over an appended list of `Int`s splits as a sum.
  have sum_append :
      ∀ xs ys : List Int,
        (xs ++ ys).sum = xs.sum + ys.sum := by
    intro xs ys
    induction xs with
    | nil =>
        simp
    | cons x xs ih =>
        simp [ih, Int.add_assoc]
  -- Rewrite with `map_append` and the local `sum_append` lemma.
  simp [List.map_append, sum_append]

/-- Public view of a confidential-transaction trace: the sequence of
    public projections of the states seen along the trace, starting
    from the initial state. -/
def ctTraceView : CTState → List CTDelta → List (List (String × Int))
  | s, [] => [s.eraseAssets]
  | s, d :: ds =>
      s.eraseAssets :: ctTraceView (applyDelta s d) ds

/-- Trace of total signed values along a confidential-transaction
    delta trace, starting from the initial state. This is used in
    trace-level amount-hiding properties where only aggregate totals
    are considered observable. -/
def ctTraceTotalsView : CTState → List CTDelta → List Int
  | s, [] => [s.totalValue]
  | s, d :: ds =>
      s.totalValue :: ctTraceTotalsView (applyDelta s d) ds

/-- Static balance invariant: the sum of all confidential values in a
    state is zero. This models “balanced” confidential transactions
    where inputs and outputs conserve value. -/
def BalanceInvariant (s : CTState) : Prop :=
  s.totalValue = 0

/-- Applying a zero-sum delta preserves the balance invariant. -/
lemma applyDelta_preserves_BalanceInvariant
    (s : CTState) (d : CTDelta)
    (hBal : BalanceInvariant s)
    (hDelta : (d.balances.map (fun b => b.value)).sum = 0) :
    BalanceInvariant (applyDelta s d) := by
  unfold BalanceInvariant at *
  have hTotal := applyDelta_totalValue s d
  -- Substitute the known equalities for the original total and delta.
  have h := hTotal
  -- From `hBal : s.totalValue = 0` and `hDelta`, we get the desired equality.
  simp [hBal, hDelta] at h
  exact h

/-- Abstract one-step confidential-transaction relation: a post-state
    `s'` is related to a pre-state `s` when the total signed value is
    preserved. Concrete transition systems (e.g. adding/removing
    entries, redistributing values) should refine this relation. -/
def CTStep (s s' : CTState) : Prop :=
  s'.totalValue = s.totalValue

/-- Any zero-sum delta step refines the abstract `CTStep` relation. -/
lemma CTStep_of_applyDelta (s : CTState) (d : CTDelta) :
    CTStep s (applyDelta s d) := by
  unfold CTStep
  have hTotal := applyDelta_totalValue s d
  -- Using the `sumZero` field on `CTDelta`.
  have hDelta : (d.balances.map (fun b => b.value)).sum = 0 := d.sumZero
  -- Rewrite to show the totals are equal.
  have h := hTotal
  simp [hDelta] at h
  exact h

/-- A sequence of confidential-transaction deltas is well formed when
    each delta has total signed value zero. -/
def DeltasWellFormed (ds : List CTDelta) : Prop :=
  ∀ d, d ∈ ds → (d.balances.map (fun b => b.value)).sum = 0

/-- Run a sequence of deltas by folding `applyDelta` from an initial
    state. -/
def runDeltas (s : CTState) (ds : List CTDelta) : CTState :=
  ds.foldl (fun acc d => applyDelta acc d) s

/-- A well-formed sequence of zero-sum deltas preserves the global
    balance invariant when run from any balanced initial state. -/
lemma runDeltas_preserves_BalanceInvariant
    (s : CTState) (ds : List CTDelta)
    (hBal : BalanceInvariant s)
    (hWellFormed : DeltasWellFormed ds) :
    BalanceInvariant (runDeltas s ds) := by
  unfold runDeltas
  -- Induction on the list of deltas.
  revert s hBal hWellFormed
  induction ds with
  | nil =>
      intro s hBal hWellFormed
      simpa using hBal
  | cons d ds ih =>
      intro s hBal hWellFormed
      have hDeltaZero :
          (d.balances.map (fun b => b.value)).sum = 0 := by
        exact hWellFormed d (by simp)
      have hTail :
          DeltasWellFormed ds := by
        intro d' hd'
        exact hWellFormed d' (by simp [hd'])
      -- First apply the head delta, preserving `BalanceInvariant`.
      have hBal' :
          BalanceInvariant (applyDelta s d) :=
        applyDelta_preserves_BalanceInvariant s d hBal hDeltaZero
      -- Then apply the induction hypothesis to the tail.
      have hRunTail :
          BalanceInvariant
            (ds.foldl (fun acc d => applyDelta acc d) (applyDelta s d)) :=
        ih (applyDelta s d) hBal' hTail
      simpa using hRunTail

/-- Asset-type hiding for a given state: there exists another state
    with the same public projection (commitments and signed values) but
    a different sequence of asset-type tags. This captures, at the
    current level of modelling, that asset types are not determined by
    what is publicly observable in `eraseAssets`. -/
def AssetTypeHiding (s : CTState) : Prop :=
  ∃ s' : CTState,
    s'.eraseAssets = s.eraseAssets ∧
    (s'.balances.map (fun b => b.asset)) ≠
      (s.balances.map (fun b => b.asset))

end Model
end Privacy
end HeytingLean
