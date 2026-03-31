import HeytingLean.CCI.Core
import HeytingLean.Privacy.Model
import HeytingLean.Crypto.Commit.Spec
import HeytingLean.Crypto.Form
import HeytingLean.Crypto.BoolLens

/-
# Privacy.Spec

Identifiers and metadata for privacy protocol properties from section 8 of
`crypto_proofs_master_list.md`.
-/

namespace HeytingLean
namespace Privacy
namespace Spec

open HeytingLean.CCI
open HeytingLean.Privacy
open HeytingLean.Crypto

inductive PropertyId
  | tornadoCashLogic
  | mixerAnonymitySet
  | nullifierUniqueness
  | amountHiding
  | balanceProofs
  | assetTypeHiding
  deriving DecidableEq, Repr

def PropertyId.slug : PropertyId → String
  | .tornadoCashLogic   => "privacy.tornado_cash_logic"
  | .mixerAnonymitySet  => "privacy.anonymity_set"
  | .nullifierUniqueness => "privacy.nullifier_uniqueness"
  | .amountHiding       => "privacy.amount_hiding"
  | .balanceProofs      => "privacy.balance_proofs"
  | .assetTypeHiding    => "privacy.asset_type_hiding"

def PropertyId.title : PropertyId → String
  | .tornadoCashLogic   => "Tornado Cash Logic"
  | .mixerAnonymitySet  => "Anonymity Set"
  | .nullifierUniqueness => "Nullifier Uniqueness"
  | .amountHiding       => "Amount Hiding"
  | .balanceProofs      => "Balance Proofs"
  | .assetTypeHiding    => "Asset Type Hiding"

def PropertyId.description : PropertyId → String
  | .tornadoCashLogic =>
      "Deposit and withdraw operations for mixers are functionally correct."
  | .mixerAnonymitySet =>
      "Mixers provide the stated anonymity set size under the threat model."
  | .nullifierUniqueness =>
      "Nullifiers prevent double-spending of mixer notes or commitments."
  | .amountHiding =>
      "Transaction amounts remain hidden while preserving validity."
  | .balanceProofs =>
      "Proofs show sufficient funds without revealing underlying balances."
  | .assetTypeHiding =>
      "Protocols hide asset type in multi-asset settings while preserving safety."

def PropertyId.toExpr (p : PropertyId) : Expr :=
  Expr.atom p.slug

/-- Specification-level statement shape for nullifier uniqueness in the
    abstract mixer model: extending a state by recording a fresh
    nullifier preserves `NullifierUnique`. This is a step-level
    realisation of `PropertyId.nullifierUniqueness`. -/
def NullifierUniquenessStatement : Prop :=
  ∀ s n, Model.NullifierUnique s →
    n ∉ s.nullifiers →
    Model.NullifierUnique (Model.withdraw s n)

/-- The abstract mixer conservation statement: extending a state by
    recording a nullifier corresponding to an existing commitment
    preserves `MixerConservation`. This captures the “withdrawals come
    from deposits” part of `PropertyId.tornadoCashLogic` in the current
    string-based model. -/
def MixerConservationStatement : Prop :=
  ∀ s n, Model.MixerConservation s →
    n ∈ s.commitments →
    Model.MixerConservation (Model.withdraw s n)

/-- A step-based balance-invariant statement for confidential
    transactions: any one-step transition that preserves total signed
    value also preserves `BalanceInvariant`. This connects the static
    invariant to the abstract `CTStep` relation from the model. -/
def BalanceInvariantStatement : Prop :=
  ∀ s s', Model.CTStep s s' →
    Model.BalanceInvariant s → Model.BalanceInvariant s'

/-- Decidability of the balance invariant, inherited from decidable
    equality on integers. -/
instance instDecidableBalanceInvariant (s : Model.CTState) :
    Decidable (Model.BalanceInvariant s) := by
  unfold Model.BalanceInvariant
  infer_instance

/-- A single-atom boolean `Form` encoding the confidential-transaction
    balance invariant via a Bool-lens environment. -/
def CTBalanceForm : Crypto.Form 1 :=
  Crypto.Form.var ⟨0, by decide⟩

/-- Boolean environment sending the sole atom of `CTBalanceForm` to the
    decision procedure for `BalanceInvariant s`. -/
def ctBalanceEnv (s : Model.CTState) : Crypto.BoolLens.Env 1 :=
  fun _ => decide (Model.BalanceInvariant s)

/-- Evaluating `CTBalanceForm` under `ctBalanceEnv s` yields the
    boolean view of `BalanceInvariant s`. -/
lemma eval_CTBalanceForm (s : Model.CTState) :
    Crypto.BoolLens.eval CTBalanceForm (ctBalanceEnv s) =
      decide (Model.BalanceInvariant s) := by
  unfold CTBalanceForm ctBalanceEnv
  simp [Crypto.BoolLens.eval, Model.BalanceInvariant, Model.CTState.totalValue]

/-- Form-level characterisation of the balance invariant: the
    Bool-lens evaluation of `CTBalanceForm` under `ctBalanceEnv s` is
    `true` exactly when `BalanceInvariant s` holds. -/
def BalanceFormStatement : Prop :=
  ∀ s : Model.CTState,
    Crypto.BoolLens.eval CTBalanceForm (ctBalanceEnv s) = true ↔
      Model.BalanceInvariant s

/-- `BalanceFormStatement` holds: the Bool-lens evaluation of
    `CTBalanceForm` is `true` exactly when the underlying
    `BalanceInvariant` holds. -/
theorem balanceFormStatement_holds :
    BalanceFormStatement := by
  intro s
  have hEval := eval_CTBalanceForm s
  constructor
  · intro h
    -- From `eval = true`, derive `BalanceInvariant s` via `of_decide_eq_true`.
    have hDec :
        decide (Model.BalanceInvariant s) = true := by
      simpa [hEval] using h
    exact of_decide_eq_true hDec
  · intro hBal
    -- From `BalanceInvariant s`, derive `eval = true`.
    have hDec :
        decide (Model.BalanceInvariant s) = true :=
      (decide_eq_true_eq (p := Model.BalanceInvariant s)).mpr hBal
    simpa [hEval] using hDec

/-- `NullifierUniquenessStatement` holds in the abstract mixer model via
    the step-level lemma `withdraw_preserves_NullifierUnique`. -/
theorem nullifierUniquenessStatement_holds :
    NullifierUniquenessStatement := by
  intro s n hUnique hFresh
  exact Model.withdraw_preserves_NullifierUnique s n hUnique hFresh

/-- `MixerConservationStatement` holds in the abstract mixer model via
    the step-level lemma `withdraw_preserves_MixerConservation`. -/
theorem mixerConservationStatement_holds :
    MixerConservationStatement := by
  intro s n hCons hCommit
  exact Model.withdraw_preserves_MixerConservation s n hCons hCommit

/-- The step-based `BalanceInvariantStatement` holds directly from the
    definition of `CTStep` and `BalanceInvariant`: if a transition
    preserves total signed value, then any state satisfying
    `BalanceInvariant` transitions to a state that also satisfies it. -/
theorem balanceInvariantStatement_holds :
    BalanceInvariantStatement := by
  intro s s' hStep hBal
  dsimp [Model.CTStep, Model.BalanceInvariant, Model.CTState.totalValue] at *
  simpa [hStep] using hBal

/-- Combined Tornado-style mixer logic statement: in the abstract mixer
    model, recording a nullifier corresponding to an existing
    commitment preserves `MixerConservation`, and recording a fresh
    nullifier preserves `NullifierUnique`. This bundles the two
    step-level invariants into a single statement aligned with
    `PropertyId.tornadoCashLogic`. -/
def TornadoCashLogicStatement : Prop :=
  MixerConservationStatement ∧ NullifierUniquenessStatement

/-- `TornadoCashLogicStatement` holds in the abstract mixer model by
    combining the conservation and uniqueness statements. -/
theorem tornadoCashLogicStatement_holds :
    TornadoCashLogicStatement := by
  exact And.intro mixerConservationStatement_holds
    nullifierUniquenessStatement_holds

/-- A minimal anonymity-set statement for mixers: there exist two
    distinct mixer states with the same number of commitments and the
    same number of nullifiers. This expresses, at the current level of
    modelling, that observing only the anonymity-set size (counts of
    commitments and nullifiers) does not determine the underlying mixer
    state. More refined indistinguishability properties are reserved
    for later refinements that model adversarial views explicitly. -/
def MixerAnonymityStatement : Prop :=
  ∃ s₁ s₂ : Model.MixerState,
    s₁.commitments.length = s₂.commitments.length ∧
    s₁.nullifiers.length = s₂.nullifiers.length ∧
    s₁ ≠ s₂

/-- `MixerAnonymityStatement` holds via two states that differ in their
    concrete commitments but have the same anonymity-set sizes (number
    of commitments and number of nullifiers). -/
theorem mixerAnonymityStatement_holds :
    MixerAnonymityStatement := by
  classical
  let s₁ : Model.MixerState :=
    { commitments := ["c₁", "c₂"], nullifiers := [] }
  let s₂ : Model.MixerState :=
    { commitments := ["c₃", "c₄"], nullifiers := [] }
  refine ⟨s₁, s₂, ?hLenComm, ?hLenNull, ?hNe⟩
  · -- Both states have two commitments.
    simp [s₁, s₂]
  · -- Both states have zero nullifiers.
    simp [s₁, s₂]
  · -- The states are distinct because their commitment lists differ.
    intro hEq
    have hComm :=
      congrArg (fun (s : Model.MixerState) => s.commitments) hEq
    simp [s₁, s₂] at hComm

/-- A trace-level anonymity-set statement for mixers: there exist two
    well-formed traces starting from the same initial state whose
    public views (counts of commitments and nullifiers along the
    trace) coincide, while the final mixer states differ. This
    refines `MixerAnonymityStatement` from snapshot-level anonymity
    to a simple trace-level indistinguishability property. -/
def MixerTraceAnonymityStatement : Prop :=
  ∃ s₀ : Model.MixerState,
    ∃ ops₁ ops₂ : List Model.MixerOp,
      Model.MixerTraceWellFormed s₀ ops₁ ∧
      Model.MixerTraceWellFormed s₀ ops₂ ∧
      Model.mixerTraceView s₀ ops₁ =
        Model.mixerTraceView s₀ ops₂ ∧
      Model.runMixerOps s₀ ops₁ ≠ Model.runMixerOps s₀ ops₂

/-- `MixerTraceAnonymityStatement` holds via two deposit-only traces
    that have identical public views but differ in their concrete
    commitment lists. -/
theorem mixerTraceAnonymityStatement_holds :
    MixerTraceAnonymityStatement := by
  classical
  let s₀ : Model.MixerState :=
    { commitments := [], nullifiers := [] }
  let ops₁ : List Model.MixerOp :=
    [Model.MixerOp.deposit "c₁", Model.MixerOp.deposit "c₂"]
  let ops₂ : List Model.MixerOp :=
    [Model.MixerOp.deposit "d₁", Model.MixerOp.deposit "d₂"]
  refine ⟨s₀, ops₁, ops₂, ?hWF₁, ?hWF₂, ?hView, ?hNe⟩
  · -- Both traces are well formed: they contain only deposits.
    simp [Model.MixerTraceWellFormed, ops₁]
  · simp [Model.MixerTraceWellFormed, ops₂]
  · -- Public views coincide: both traces yield the same sequence of
    -- (commitments, nullifiers) counts.
    simp [Model.mixerTraceView, Model.MixerState.publicView,
          Model.applyMixerOp,
          Model.deposit, s₀, ops₁, ops₂]
  · -- Final states differ because their commitment lists differ.
    intro hEq
    have hComm :=
      congrArg (fun (s : Model.MixerState) => s.commitments) hEq
    simp [Model.runMixerOps, Model.applyMixerOp, Model.deposit,
          s₀, ops₁, ops₂] at hComm

/-- A minimal example amount-hiding statement for confidential transactions:
    there exist two distinct confidential-transaction states with the
    same total signed value and the same number of balances. This
    expresses, at the current level of modelling, that observing only
    the aggregate total and balance count does not determine the
    underlying value distribution. -/
def AmountHidingStatement : Prop :=
  ∃ s₁ s₂ : Model.CTState,
    s₁.totalValue = s₂.totalValue ∧
    s₁.balances.length = s₂.balances.length ∧
    s₁ ≠ s₂

/-- `AmountHidingStatement` holds via a simple pair of two-balance
    states that both sum to zero but differ in their individual
    entries. -/
theorem amountHidingStatement_holds :
    AmountHidingStatement := by
  classical
  let s₁ : Model.CTState :=
    { balances :=
        [ { commitment := "a", asset := "USD", value :=  1 }
        , { commitment := "b", asset := "USD", value := -1 } ] }
  let s₂ : Model.CTState :=
    { balances :=
        [ { commitment := "a", asset := "USD", value :=  2 }
        , { commitment := "b", asset := "USD", value := -2 } ] }
  refine ⟨s₁, s₂, ?hTotal, ?hLen, ?hNe⟩
  · -- Both states have total signed value zero.
    simp [Model.CTState.totalValue, s₁, s₂]
  · -- Both states have two balances.
    simp [s₁, s₂]
  · -- The states are distinct, since their value assignments differ.
    intro hEq
    have hVals :=
      congrArg (fun (s : Model.CTState) =>
        s.balances.map (fun b => b.value)) hEq
    -- Extract a contradiction from differing value lists.
    simp [s₁, s₂] at hVals

/-- A trace-level amount-hiding statement for confidential
    transactions: there exist two well-formed sequences of
    confidential-transaction deltas starting from the same initial
    state such that the sequence of aggregate totals along each trace
    coincides, while the final states differ. This is the
    trace-refinement of `AmountHidingStatement` at the level of
    `runDeltas`. -/
def CTTraceAmountHidingStatement : Prop :=
  ∃ s₀ : Model.CTState,
    ∃ ds₁ ds₂ : List Model.CTDelta,
      Model.DeltasWellFormed ds₁ ∧
      Model.DeltasWellFormed ds₂ ∧
      Model.ctTraceTotalsView s₀ ds₁ =
        Model.ctTraceTotalsView s₀ ds₂ ∧
      Model.runDeltas s₀ ds₁ ≠ Model.runDeltas s₀ ds₂

/-- `CTTraceAmountHidingStatement` holds via two single-step traces
    whose deltas have the same aggregate effect on total value but
    different internal value distributions. -/
theorem ctTraceAmountHidingStatement_holds :
    CTTraceAmountHidingStatement := by
  classical
  let s₀ : Model.CTState :=
    { balances := [] }
  let d₁ : Model.CTDelta :=
    { balances :=
        [ { commitment := "a", asset := "USD", value :=  1 }
        , { commitment := "b", asset := "USD", value := -1 } ]
      sumZero := by
        simp }
  let d₂ : Model.CTDelta :=
    { balances :=
        [ { commitment := "a", asset := "USD", value :=  2 }
        , { commitment := "b", asset := "USD", value := -2 } ]
      sumZero := by
        simp }
  let ds₁ : List Model.CTDelta := [d₁]
  let ds₂ : List Model.CTDelta := [d₂]
  refine ⟨s₀, ds₁, ds₂, ?hWF₁, ?hWF₂, ?hTotals, ?hNe⟩
  · -- `ds₁` is well formed: its sole delta has zero total value.
    intro d hd
    have : d = d₁ := by
      simpa [ds₁] using hd
    subst this
    simpa using d₁.sumZero
  · -- `ds₂` is well formed for the same reason.
    intro d hd
    have : d = d₂ := by
      simpa [ds₂] using hd
    subst this
    simpa using d₂.sumZero
  · -- Aggregate totals along both traces coincide.
    simp [Model.ctTraceTotalsView, Model.CTState.totalValue,
          Model.applyDelta,
          s₀, ds₁, ds₂, d₁, d₂]
  · -- Final states differ because their underlying value lists differ.
    intro hEq
    have hVals :=
      congrArg
        (fun (s : Model.CTState) =>
          s.balances.map (fun b => b.value)) hEq
    simp [Model.runDeltas, Model.applyDelta,
          s₀, ds₁, ds₂, d₁, d₂] at hVals

/-- A minimal asset-type-hiding statement for confidential transactions:
    there exist two distinct confidential-transaction states that have
    the same public projection (commitments and signed values) but
    different asset-type assignments. This expresses that, at the
    current modelling level, observing only commitments and values does
    not determine the underlying asset types. -/
def AssetTypeHidingStatement : Prop :=
  ∃ s₁ s₂ : Model.CTState,
    s₁.eraseAssets = s₂.eraseAssets ∧
    (s₁.balances.map (fun b => b.asset)) ≠
      (s₂.balances.map (fun b => b.asset))

/-- `AssetTypeHidingStatement` holds via two states that share the same
    commitments and signed values but differ in their asset-type tags. -/
theorem assetTypeHidingStatement_holds :
    AssetTypeHidingStatement := by
  classical
  let s₁ : Model.CTState :=
    { balances :=
        [ { commitment := "c1", asset := "USD",  value := 10 }
        , { commitment := "c2", asset := "EUR",  value := -10 } ] }
  let s₂ : Model.CTState :=
    { balances :=
        [ { commitment := "c1", asset := "BTC",  value := 10 }
        , { commitment := "c2", asset := "ETH",  value := -10 } ] }
  refine ⟨s₁, s₂, ?hErase, ?hAssetsNe⟩
  · -- Public projections coincide (same commitments and values).
    simp [Model.CTState.eraseAssets, s₁, s₂]
  · -- Asset-type tags differ.
    intro hEq
    have hAssets :=
      congrArg (fun (xs : List String) => xs) hEq
    -- This forces equality of the asset lists, contradicting the choices.
    simp [s₁, s₂] at hAssets

/-- A trace-level asset-type-hiding statement for confidential
    transactions: there exist two well-formed sequences of
    confidential-transaction deltas starting from the same initial
    state whose public trace views (obtained via `CTState.eraseAssets`
    along the trace) coincide, while the final states differ. This
    mirrors `MixerTraceAnonymityStatement` for the confidential
    transactions model. -/
def CTTraceAssetTypeHidingStatement : Prop :=
  ∃ s₀ : Model.CTState,
    ∃ ds₁ ds₂ : List Model.CTDelta,
      Model.DeltasWellFormed ds₁ ∧
      Model.DeltasWellFormed ds₂ ∧
      Model.ctTraceView s₀ ds₁ =
        Model.ctTraceView s₀ ds₂ ∧
      Model.runDeltas s₀ ds₁ ≠ Model.runDeltas s₀ ds₂

/-- `CTTraceAssetTypeHidingStatement` holds via two single-step traces
    whose deltas share the same public commitments and values but
    differ in their asset-type tags. -/
theorem ctTraceAssetTypeHidingStatement_holds :
    CTTraceAssetTypeHidingStatement := by
  classical
  let s₀ : Model.CTState :=
    { balances := [] }
  let d₁ : Model.CTDelta :=
    { balances :=
        [ { commitment := "c1", asset := "USD", value := 10 }
        , { commitment := "c2", asset := "EUR", value := -10 } ]
      sumZero := by
        simp }
  let d₂ : Model.CTDelta :=
    { balances :=
        [ { commitment := "c1", asset := "BTC", value := 10 }
        , { commitment := "c2", asset := "ETH", value := -10 } ]
      sumZero := by
        simp }
  let ds₁ : List Model.CTDelta := [d₁]
  let ds₂ : List Model.CTDelta := [d₂]
  refine ⟨s₀, ds₁, ds₂, ?hWF₁, ?hWF₂, ?hView, ?hNe⟩
  · -- `ds₁` is well formed: its sole delta has zero total value.
    intro d hd
    have : d = d₁ := by
      simpa [ds₁] using hd
    subst this
    simpa using d₁.sumZero
  · -- `ds₂` is well formed for the same reason.
    intro d hd
    have : d = d₂ := by
      simpa [ds₂] using hd
    subst this
    simpa using d₂.sumZero
  · -- Public trace views coincide: both traces yield the same sequence
    -- of public projections when asset types are erased.
    simp [Model.ctTraceView, Model.CTState.eraseAssets,
          Model.applyDelta,
          ds₁, ds₂, s₀, d₁, d₂]
  · -- Final states differ because their asset-type tags differ.
    intro hEq
    have hAssets :=
      congrArg
        (fun (s : Model.CTState) =>
          s.balances.map (fun b => b.asset)) hEq
    simp [Model.runDeltas, Model.applyDelta,
          s₀, ds₁, ds₂, d₁, d₂] at hAssets

/-- A stronger, adversary-quantified trace-level amount-hiding
    statement: for every deterministic analysis function on the public
    totals view `ctTraceTotalsView`, there exist two well-formed
    traces with identical totals view but different final value
    distributions on which the analysis produces the same output. -/
def CTTraceAmountHidingIdealStatement : Prop :=
  ∀ (analyze : List Int → List String),
    ∃ s₀ : Model.CTState,
      ∃ ds₁ ds₂ : List Model.CTDelta,
        Model.DeltasWellFormed ds₁ ∧
        Model.DeltasWellFormed ds₂ ∧
        Model.ctTraceTotalsView s₀ ds₁ =
          Model.ctTraceTotalsView s₀ ds₂ ∧
        analyze (Model.ctTraceTotalsView s₀ ds₁) =
          analyze (Model.ctTraceTotalsView s₀ ds₂) ∧
        Model.runDeltas s₀ ds₁ ≠ Model.runDeltas s₀ ds₂

/-- `CTTraceAmountHidingIdealStatement` holds by reusing the concrete
    witness traces from `ctTraceAmountHidingStatement_holds`: any
    analysis function sees the same totals view on these traces, but
    the final value distributions still differ. -/
theorem ctTraceAmountHidingIdealStatement_holds :
    CTTraceAmountHidingIdealStatement := by
  classical
  intro analyze
  rcases ctTraceAmountHidingStatement_holds with
    ⟨s₀, ds₁, ds₂, hWF₁, hWF₂, hTotals, hNe⟩
  refine ⟨s₀, ds₁, ds₂, hWF₁, hWF₂, hTotals, ?_, hNe⟩
  have hAnalyze :
      analyze (Model.ctTraceTotalsView s₀ ds₁) =
        analyze (Model.ctTraceTotalsView s₀ ds₂) :=
    congrArg analyze hTotals
  simpa using hAnalyze

/-- A stronger, adversary-quantified trace-level asset-type-hiding
    statement: for every deterministic analysis function on the public
    trace view `ctTraceView`, there exist two traces with the same
    public view but different final asset-type tags on which the
    analysis produces the same output. -/
def CTTraceAssetTypeHidingIdealStatement : Prop :=
  ∀ (analyze : List (List (String × Int)) → List String),
    ∃ s₀ : Model.CTState,
      ∃ ds₁ ds₂ : List Model.CTDelta,
        Model.DeltasWellFormed ds₁ ∧
        Model.DeltasWellFormed ds₂ ∧
        Model.ctTraceView s₀ ds₁ =
          Model.ctTraceView s₀ ds₂ ∧
        analyze (Model.ctTraceView s₀ ds₁) =
          analyze (Model.ctTraceView s₀ ds₂) ∧
        Model.runDeltas s₀ ds₁ ≠ Model.runDeltas s₀ ds₂

/-- `CTTraceAssetTypeHidingIdealStatement` holds by reusing the
    concrete witness traces from `ctTraceAssetTypeHidingStatement_holds`:
    any analysis function sees the same public trace view on these
    traces, but the final asset-type tags still differ. -/
theorem ctTraceAssetTypeHidingIdealStatement_holds :
    CTTraceAssetTypeHidingIdealStatement := by
  classical
  intro analyze
  rcases ctTraceAssetTypeHidingStatement_holds with
    ⟨s₀, ds₁, ds₂, hWF₁, hWF₂, hView, hNe⟩
  refine ⟨s₀, ds₁, ds₂, hWF₁, hWF₂, hView, ?_, hNe⟩
  have hAnalyze :
      analyze (Model.ctTraceView s₀ ds₁) =
        analyze (Model.ctTraceView s₀ ds₂) :=
    congrArg analyze hView
  simpa using hAnalyze

/-- A stronger, adversary-quantified asset-type-hiding statement: for
    every deterministic analysis function on the public projection
    `eraseAssets`, there exist two states with the same public
    projection but different asset-type lists on which the analysis
    produces the same output. This expresses that asset types are not
    determined even up to any (pure) postprocessing of the observable
    view. -/
def AssetTypeHidingIdealStatement : Prop :=
  ∀ (analyze : List (String × Int) → List String),
    ∃ s₁ s₂ : Model.CTState,
      s₁.eraseAssets = s₂.eraseAssets ∧
      analyze (s₁.eraseAssets) = analyze (s₂.eraseAssets) ∧
      (s₁.balances.map (fun b => b.asset)) ≠
        (s₂.balances.map (fun b => b.asset))

/-- `AssetTypeHidingIdealStatement` holds by reusing the concrete
    witness states from `assetTypeHidingStatement_holds`: any analysis
    function sees the same public projection on these states, but the
    asset-type lists still differ. -/
theorem assetTypeHidingIdealStatement_holds :
    AssetTypeHidingIdealStatement := by
  classical
  intro analyze
  rcases assetTypeHidingStatement_holds with
    ⟨s₁, s₂, hErase, hAssetsNe⟩
  refine ⟨s₁, s₂, hErase, ?_, hAssetsNe⟩
  -- Analysis depends only on the public projection, which coincides.
  have hAnalyze :
      analyze s₁.eraseAssets = analyze s₂.eraseAssets :=
    congrArg analyze hErase
  simpa [Model.CTState.eraseAssets] using hAnalyze

/-- Cryptographic asset-type-hiding assumption: there exists a vector
    commitment scheme together with security properties whose
    `computationalHidingAt` field holds. This is the primitives-level
    counterpart of asset-type hiding, phrased purely in terms of an
    abstract vector-commitment interface. The weaker
    `verificationConsistencyAt` field is not enough for this assumption. -/
def AssetTypeHidingCryptoAssumption : Prop :=
  ∃ (S : Commit.Spec.Vec.Scheme)
    (sec : Commit.Spec.Vec.Scheme.SecurityProps S),
    sec.computationalHidingAt

/-- Bridging shape from a cryptographic asset-type-hiding assumption to
    the idealised state-level statement: given a suitable vector
    commitment scheme with a hiding property, the ideal
    `AssetTypeHidingIdealStatement` should follow. This is kept as a
    bare `Prop` (no proof yet); future work will supply a concrete
    reduction for specific schemes and encodings of `CTState`. -/
def AssetTypeHidingReductionStatement : Prop :=
  AssetTypeHidingCryptoAssumption → AssetTypeHidingIdealStatement

/-- Cryptographic amount-hiding assumption: there exists a vector
    commitment scheme together with security properties whose
    `computationalHidingAt` field holds, intended to capture hiding of
    committed amounts. This reuses the same abstract interface as
    `AssetTypeHidingCryptoAssumption`, but is conceptually tied to the
    `AmountHiding` rows. -/
def AmountHidingCryptoAssumption : Prop :=
  ∃ (S : Commit.Spec.Vec.Scheme)
    (sec : Commit.Spec.Vec.Scheme.SecurityProps S),
    sec.computationalHidingAt

/-- Bridging shape from a cryptographic amount-hiding assumption to
    the idealised trace-level amount-hiding statement: given a
    suitable vector commitment scheme with a hiding property, the
    ideal `CTTraceAmountHidingIdealStatement` should follow. As with
    `AssetTypeHidingReductionStatement`, this is kept as a bare
    `Prop`; future work will provide concrete reductions for specific
    schemes and encodings of `CTState` and its deltas. -/
def CTTraceAmountHidingReductionStatement : Prop :=
  AmountHidingCryptoAssumption → CTTraceAmountHidingIdealStatement

/-- Bridging shape from a cryptographic asset-type-hiding assumption
    to the idealised trace-level asset-type-hiding statement: given a
    suitable vector commitment scheme with a hiding property, the
    ideal `CTTraceAssetTypeHidingIdealStatement` should follow. This
    mirrors `AssetTypeHidingReductionStatement` at the trace level and
    is likewise left as a target for future concrete reductions. -/
def CTTraceAssetTypeHidingReductionStatement : Prop :=
  AssetTypeHidingCryptoAssumption → CTTraceAssetTypeHidingIdealStatement

/-- The existential `AssetTypeHidingStatement` is equivalent to the
    existence of a state satisfying the model-level `AssetTypeHiding`
    predicate. This connects the spec-level row for asset-type hiding
    to the per-state notion from `Privacy.Model`. -/
theorem assetTypeHidingStatement_iff_exists_modelAssetTypeHiding :
    AssetTypeHidingStatement ↔
      ∃ s : Model.CTState, Model.AssetTypeHiding s := by
  constructor
  · intro h
    classical
    rcases h with ⟨s₁, s₂, hErase, hNe⟩
    refine ⟨s₁, ?_⟩
    -- Exhibit `s₂` as a witness for `AssetTypeHiding s₁`.
    refine ⟨s₂, ?_, ?_⟩
    · -- Public projections coincide up to symmetry of equality.
      simpa [Model.CTState.eraseAssets] using hErase.symm
    · -- Asset-type tags differ in the required direction.
      intro hEq
      have hEq' : (s₁.balances.map (fun b => b.asset)) =
          (s₂.balances.map (fun b => b.asset)) := by
        simpa using hEq.symm
      exact hNe hEq'
  · intro h
    classical
    rcases h with ⟨s, hHide⟩
    rcases hHide with ⟨s', hErase, hNe⟩
    -- Repackage the model-level witness as a pair of states.
    refine ⟨s, s', ?_, ?_⟩
    · exact hErase.symm
    · -- Asset-type tags differ (in the original direction).
      intro hEq
      have hEq' : (s'.balances.map (fun b => b.asset)) =
          (s.balances.map (fun b => b.asset)) := by
        simpa using hEq.symm
      exact hNe hEq'

/-- Interpretation of privacy `PropertyId`s in terms of the current
    mixer and confidential-transaction models. -/
def propertyHolds (p : PropertyId) : Prop :=
  match p with
  | .tornadoCashLogic   => TornadoCashLogicStatement
  | .mixerAnonymitySet  =>
      MixerAnonymityStatement ∧ MixerTraceAnonymityStatement
  | .nullifierUniqueness => NullifierUniquenessStatement
  | .amountHiding       =>
      AmountHidingStatement ∧ CTTraceAmountHidingStatement
  | .balanceProofs      => BalanceInvariantStatement ∧ BalanceFormStatement
  | .assetTypeHiding    =>
      AssetTypeHidingStatement ∧ CTTraceAssetTypeHidingStatement

/-- Bridge lemma: the `tornadoCashLogic` registry row holds for the
    current mixer model. -/
theorem propertyHolds_tornadoCashLogic :
    propertyHolds PropertyId.tornadoCashLogic := by
  simpa [propertyHolds] using tornadoCashLogicStatement_holds

/-- Bridge lemma: the `nullifierUniqueness` registry row holds for the
    current mixer model. -/
theorem propertyHolds_nullifierUniqueness :
    propertyHolds PropertyId.nullifierUniqueness := by
  simpa [propertyHolds] using nullifierUniquenessStatement_holds

/-- Bridge lemma: the `balanceProofs` registry row holds for the
    current confidential-transaction model. -/
theorem propertyHolds_balanceProofs :
    propertyHolds PropertyId.balanceProofs := by
  refine And.intro ?hInv ?hForm
  · simpa using balanceInvariantStatement_holds
  · simpa using balanceFormStatement_holds

/-- Bridge lemma: the `mixerAnonymitySet` registry row holds for the
    current mixer model, via both snapshot-level and trace-level
    anonymity statements. -/
theorem propertyHolds_mixerAnonymitySet :
    propertyHolds PropertyId.mixerAnonymitySet := by
  refine And.intro ?hSnap ?hTrace
  · simpa [propertyHolds] using mixerAnonymityStatement_holds
  · simpa [propertyHolds] using mixerTraceAnonymityStatement_holds

/-- Bridge lemma: the `amountHiding` registry row holds for the current
    confidential-transaction model, via both snapshot-level and
    trace-level amount-hiding statements. -/
theorem propertyHolds_amountHiding :
    propertyHolds PropertyId.amountHiding := by
  dsimp [propertyHolds]
  refine And.intro ?hSnap ?hTrace
  · simpa using amountHidingStatement_holds
  · simpa using ctTraceAmountHidingStatement_holds

/-- Bridge lemma: the `assetTypeHiding` registry row holds for the
    current confidential-transaction model, via both snapshot-level
    and trace-level asset-type-hiding statements. -/
theorem propertyHolds_assetTypeHiding :
    propertyHolds PropertyId.assetTypeHiding := by
  dsimp [propertyHolds]
  refine And.intro ?hSnap ?hTrace
  · simpa using assetTypeHidingStatement_holds
  · simpa using ctTraceAssetTypeHidingStatement_holds

end Spec
end Privacy
end HeytingLean
