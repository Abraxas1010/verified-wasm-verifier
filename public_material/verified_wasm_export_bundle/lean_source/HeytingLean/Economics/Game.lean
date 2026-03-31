import HeytingLean.Governance.Spec

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-
# Economics.Game

Lightweight game-theoretic core used to express incentive-compatibility
and related economics-style properties.

This module provides:
* an abstract definition of normal-form games;
* best-response and Nash equilibrium predicates; and
* example instances (trivial game, staking game, auction games),
  together with a small bridge to `Governance.Spec.PropertyId`.
-/

namespace HeytingLean
namespace Economics
namespace Game

/-- A normal-form game over player index type `Player`. -/
structure NormalForm (Player : Type) where
  /-- Strategy type for each player. -/
  Strategy : Player → Type
  /-- Payoff type. -/
  Payoff   : Type
  /-- Preference relation on payoffs (e.g. `≤`). -/
  le       : Payoff → Payoff → Prop
  /-- Payoff function given a strategy profile. -/
  payoff   : ((i : Player) → Strategy i) → Player → Payoff

namespace NormalForm

variable {Player : Type} (G : NormalForm Player)

/-- A strategy profile: one strategy per player. -/
abbrev Profile :=
  (i : Player) → G.Strategy i

/-- Pure best response for player `i` to profile `σ`. -/
def isBestResponse [DecidableEq Player]
    (i : Player) (σ : G.Profile) (s : G.Strategy i) : Prop :=
  ∀ s',
    G.le
      (G.payoff (fun j =>
        if h : j = i then (cast (by cases h; rfl) s) else σ j) i)
      (G.payoff (fun j =>
        if h : j = i then (cast (by cases h; rfl) s') else σ j) i)

/-- Pure-strategy Nash equilibrium. -/
def NashEquilibrium [DecidableEq Player]
    (σ : G.Profile) : Prop :=
  ∀ i : Player, ∃ s : G.Strategy i, isBestResponse (G := G) i σ s

/-- Generic incentive-compatibility-style statement:
    existence of a pure-strategy Nash equilibrium. -/
def IncentiveCompatibilityStatement [DecidableEq Player] : Prop :=
  ∃ σ : G.Profile, NashEquilibrium (G := G) σ

end NormalForm

/-
## Trivial game
-/

/-- Trivial normal-form game with a single player and a single strategy. -/
def trivialGame : NormalForm Unit :=
  { Strategy := fun _ => PUnit
    , Payoff := Nat
    , le := fun _ _ => True
    , payoff := fun _ _ => 0 }

/-- The always-`unit` profile is a Nash equilibrium of `trivialGame`. -/
theorem trivialGame_nash :
    NormalForm.NashEquilibrium trivialGame (fun _ => PUnit.unit) := by
  intro i
  cases i
  refine ⟨PUnit.unit, ?_⟩
  intro s'
  simp [trivialGame]

/-- `trivialGame` satisfies the basic incentive-compatibility statement. -/
theorem trivialGame_incentiveCompatible :
    NormalForm.IncentiveCompatibilityStatement (G := trivialGame) := by
  classical
  refine ⟨(fun _ => PUnit.unit), trivialGame_nash⟩

/-
## Toy staking game
-/

abbrev StakingStrategy := Bool

/-- One-player staking game: `true` = "stake", `false` = "not stake". -/
def stakingGame : NormalForm Unit :=
  { Strategy := fun _ => StakingStrategy
    , Payoff := Nat
    , le := fun a b => b ≤ a
    , payoff := fun σ _ =>
        if σ () then 2 else 1 }

/-- In `stakingGame`, "stake" is a best response against any profile. -/
theorem stakingGame_bestResponse_stake :
    NormalForm.isBestResponse stakingGame () (fun _ => true) true := by
  intro s'
  cases s' <;> simp [stakingGame]

/-- The profile where the validator stakes is a Nash equilibrium. -/
theorem stakingGame_nash :
    NormalForm.NashEquilibrium stakingGame (fun _ => true) := by
  intro i
  cases i
  refine ⟨true, ?_⟩
  exact stakingGame_bestResponse_stake

/-- `stakingGame` satisfies the incentive-compatibility statement. -/
theorem stakingGame_incentiveCompatible :
    NormalForm.IncentiveCompatibilityStatement (G := stakingGame) := by
  classical
  refine ⟨(fun _ => true), stakingGame_nash⟩

/-
## Toy auction truthfulness game
-/

/-- Players for auction games: two bidders, represented by `Bool`. -/
abbrev AuctionTruthPlayer := Bool

/-- Strategy type: `true` = "truthful", `false` = "non-truthful". -/
abbrev TruthStrategy := Bool

/-- Valuations for the example auction game. -/
def auctionVal (i : AuctionTruthPlayer) : Nat :=
  if i then 1 else 2

/-- Non-truthful bids in the example auction game. -/
def auctionAltBid (i : AuctionTruthPlayer) : Nat :=
  if i then 2 else 1

/-- Bid chosen from a truthfulness strategy. -/
def auctionBid (i : AuctionTruthPlayer) (s : TruthStrategy) : Nat :=
  if s then auctionVal i else auctionAltBid i

/-- Fixed-valuation two-player second-price-style auction game. -/
def auctionTruthGame : NormalForm AuctionTruthPlayer :=
  { Strategy := fun _ => TruthStrategy
    , Payoff := Nat
    , le := fun a b => b ≤ a
    , payoff := fun σ i =>
        let b0 := auctionBid false (σ false)
        let b1 := auctionBid true  (σ true)
        let winner : AuctionTruthPlayer :=
          if b0 ≥ b1 then false else true
        let price : Nat :=
          if b0 ≥ b1 then b1 else b0
        if i = winner then auctionVal i - price else 0 }

/-- Truthful profile for the example auction game. -/
def auctionTruthProfile : NormalForm.Profile auctionTruthGame :=
  fun _ => true

/-- In `auctionTruthGame`, truthful play is a best response against the
    truthful profile for every player. -/
theorem auctionTruthGame_bestResponse_truth
    (i : AuctionTruthPlayer) :
    NormalForm.isBestResponse auctionTruthGame i
      auctionTruthProfile true := by
  intro s'
  cases i <;> cases s' <;>
    simp [auctionTruthGame, auctionTruthProfile,
          auctionVal, auctionAltBid, auctionBid]

/-- `auctionTruthProfile` is a Nash equilibrium of `auctionTruthGame`. -/
theorem auctionTruthGame_nash :
    NormalForm.NashEquilibrium auctionTruthGame auctionTruthProfile := by
  intro i
  refine ⟨true, ?_⟩
  exact auctionTruthGame_bestResponse_truth i

/-- `auctionTruthGame` satisfies the incentive-compatibility statement. -/
theorem auctionTruthGame_incentiveCompatible :
    NormalForm.IncentiveCompatibilityStatement (G := auctionTruthGame) := by
  classical
  refine ⟨auctionTruthProfile, auctionTruthGame_nash⟩


/-
## Generic second-price auction (parameterised by valuations)
-/

/-- Winner of a two-bidder second-price auction, with a fixed tie-breaking
    rule favouring player `false`. -/
def secondPriceWinner (b0 b1 : Nat) : AuctionTruthPlayer :=
  if b0 ≥ b1 then false else true

/-- Price paid in a two-bidder second-price auction (the second-highest bid). -/
def secondPricePrice (b0 b1 : Nat) : Nat :=
  if b0 ≥ b1 then b1 else b0

/-- Payoff for player `i` in a two-bidder second-price auction with valuations
    `val` and bids `b0`, `b1`.  We use natural-number subtraction to model
    utility `max 0 (val i - price)`. -/
def secondPricePayoff (val : AuctionTruthPlayer → Nat)
    (i : AuctionTruthPlayer) (b0 b1 : Nat) : Nat :=
  let winner := secondPriceWinner b0 b1
  let price  := secondPricePrice  b0 b1
  if i = winner then val i - price else 0

/-- Structural properties of `secondPriceWinner` and `secondPricePrice`. -/

theorem secondPriceWinner_false_of_ge (b0 b1 : Nat) (h : b0 ≥ b1) :
    secondPriceWinner b0 b1 = false := by
  unfold secondPriceWinner
  simp [h]

theorem secondPriceWinner_true_of_lt (b0 b1 : Nat) (h : b0 < b1) :
    secondPriceWinner b0 b1 = true := by
  unfold secondPriceWinner
  have hnot' : ¬ b1 ≤ b0 := Nat.not_le_of_gt (show b1 > b0 from h)
  have hnot : ¬ b0 ≥ b1 := by
    intro hge
    exact hnot' (show b1 ≤ b0 from hge)
  simp [hnot]

theorem secondPricePrice_eq_b1_of_ge (b0 b1 : Nat) (h : b0 ≥ b1) :
    secondPricePrice b0 b1 = b1 := by
  unfold secondPricePrice
  simp [h]

theorem secondPricePrice_eq_b0_of_lt (b0 b1 : Nat) (h : b0 < b1) :
    secondPricePrice b0 b1 = b0 := by
  unfold secondPricePrice
  have hnot' : ¬ b1 ≤ b0 := Nat.not_le_of_gt (show b1 > b0 from h)
  have hnot : ¬ b0 ≥ b1 := by
    intro hge
    exact hnot' (show b1 ≤ b0 from hge)
  simp [hnot]

/-- Closed forms for second-price payoffs of each player. -/

theorem secondPricePayoff_false (val : AuctionTruthPlayer → Nat)
    (b0 b1 : Nat) :
    secondPricePayoff val false b0 b1 =
      if b0 ≥ b1 then val false - b1 else 0 := by
  unfold secondPricePayoff
  by_cases hge : b0 ≥ b1
  · simp [secondPriceWinner, secondPricePrice, hge]
  · have hnot : ¬ b0 ≥ b1 := hge
    simp [secondPriceWinner, secondPricePrice, hnot]

theorem secondPricePayoff_true (val : AuctionTruthPlayer → Nat)
    (b0 b1 : Nat) :
    secondPricePayoff val true b0 b1 =
      if b0 ≥ b1 then 0 else val true - b0 := by
  unfold secondPricePayoff
  by_cases hge : b0 ≥ b1
  · -- When `b0 ≥ b1`, player `true` loses and gets zero payoff.
    simp [secondPriceWinner, secondPricePrice, hge]
  · have hnot : ¬ b0 ≥ b1 := hge
    have hlt : b0 < b1 := Nat.lt_of_not_ge hnot
    -- In this case player `true` wins and pays `b0`.
    simp [secondPriceWinner, secondPricePrice, hnot, hlt]

/-- Fully parameterised two-player second-price auction game. -/
def secondPriceGame (val : AuctionTruthPlayer → Nat) :
    NormalForm AuctionTruthPlayer :=
  { Strategy := fun _ => Nat
    , Payoff := Nat
    , le := fun a b => b ≤ a
    , payoff := fun σ i =>
        let b0 := σ false
        let b1 := σ true
        secondPricePayoff val i b0 b1 }

/-- Truthful bidding profile for the generic second-price game. -/
def secondPriceTruthfulProfile (val : AuctionTruthPlayer → Nat) :
    NormalForm.Profile (secondPriceGame val) :=
  fun i => val i

/-- Truthful bidding is a best response for player `false` against the
    truthful profile in the generic second-price game. -/
theorem secondPrice_bestResponse_truth_false
    (val : AuctionTruthPlayer → Nat) :
    NormalForm.isBestResponse (secondPriceGame val) (i := false)
      (secondPriceTruthfulProfile val) (val false) := by
  classical
  -- First prove the payoff inequality in plain `Nat` form.
  have hAll : ∀ t : Nat,
      secondPricePayoff val false t (val true) ≤
        secondPricePayoff val false (val false) (val true) := by
    intro t
    by_cases hcmp : val false ≥ val true
    · -- Case `val false ≥ val true`.
      have hTruth :
          secondPricePayoff val false (val false) (val true) =
            val false - val true := by
        have h := secondPricePayoff_false val (val false) (val true)
        simpa [secondPricePayoff_false, hcmp] using h
      have hTruthNonneg :
          0 ≤ secondPricePayoff val false (val false) (val true) := by
        simpa [hTruth] using
          (Nat.zero_le (val false - val true))
      by_cases hdev : t ≥ val true
      · have hDev :
            secondPricePayoff val false t (val true) =
              val false - val true := by
          have h := secondPricePayoff_false val t (val true)
          simpa [secondPricePayoff_false, hdev] using h
        -- Both payoffs coincide.
        simpa [hDev, hTruth] using
          (Nat.le_refl (val false - val true))
      · have hDev :
            secondPricePayoff val false t (val true) = 0 := by
          have h := secondPricePayoff_false val t (val true)
          have hnot' : ¬ t ≥ val true := hdev
          simpa [secondPricePayoff_false, hnot'] using h
        -- Deviation payoff is zero; truthful payoff is non-negative.
        have : secondPricePayoff val false t (val true) ≤
            secondPricePayoff val false (val false) (val true) := by
          simpa [hDev] using hTruthNonneg
        exact this
    · -- Case `val false < val true`.
      have hlt : val false < val true := Nat.lt_of_not_ge hcmp
      have hTruth :
          secondPricePayoff val false (val false) (val true) = 0 := by
        have h := secondPricePayoff_false val (val false) (val true)
        have hnot : ¬ val false ≥ val true := hcmp
        have hzero : val false - val true = 0 :=
          Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)
        simpa [secondPricePayoff_false, hnot, hzero] using h
      have hDevZero :
          secondPricePayoff val false t (val true) = 0 := by
        have h := secondPricePayoff_false val t (val true)
        by_cases hdev : t ≥ val true
        · have hzero : val false - val true = 0 :=
            Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)
          simpa [secondPricePayoff_false, hdev, hzero] using h
        · have hnot : ¬ t ≥ val true := hdev
          simpa [secondPricePayoff_false, hnot] using h
      -- Both payoffs are zero.
      simp [hTruth, hDevZero]
  -- Now show the `NormalForm.isBestResponse` condition by unfolding.
  intro s'
  simpa [NormalForm.isBestResponse, secondPriceGame,
        secondPriceTruthfulProfile, secondPricePayoff] using hAll s'

/-- Truthful bidding is a best response for player `true` against the
    truthful profile in the generic second-price game. -/
theorem secondPrice_bestResponse_truth_true
    (val : AuctionTruthPlayer → Nat) :
    NormalForm.isBestResponse (secondPriceGame val) (i := true)
      (secondPriceTruthfulProfile val) (val true) := by
  classical
  -- Payoff inequality for player `true`.
  have hAll : ∀ t : Nat,
      secondPricePayoff val true (val false) t ≤
        secondPricePayoff val true (val false) (val true) := by
    intro t
    by_cases hcmp : val false ≥ val true
    · -- Case `val false ≥ val true`: truthful payoff is zero.
      have hTruth :
          secondPricePayoff val true (val false) (val true) = 0 := by
        have h := secondPricePayoff_true val (val false) (val true)
        simpa [secondPricePayoff_true, hcmp] using h
      -- Any deviation yields at most zero utility (clamped subtraction).
      have hzero : val true - val false = 0 :=
        Nat.sub_eq_zero_of_le (show val true ≤ val false from hcmp)
      have hDev :
          secondPricePayoff val true (val false) t = 0 := by
        have h := secondPricePayoff_true val (val false) t
        simpa [secondPricePayoff_true, hzero] using h
      simp [hTruth, hDev]
    · -- Case `val false < val true`.
      have hlt : val false < val true := Nat.lt_of_not_ge hcmp
      have hTruth :
          secondPricePayoff val true (val false) (val true) =
            val true - val false := by
        have h := secondPricePayoff_true val (val false) (val true)
        have hnot : ¬ val false ≥ val true := hcmp
        simpa [secondPricePayoff_true, hnot] using h
      by_cases hdev : val false ≥ t
      · -- Deviation loses against `val false`, giving zero payoff.
        have hDev :
            secondPricePayoff val true (val false) t = 0 := by
          have h := secondPricePayoff_true val (val false) t
          simpa [secondPricePayoff_true, hdev] using h
        have hNonneg :
            0 ≤ val true - val false :=
          Nat.zero_le _
        have : secondPricePayoff val true (val false) t ≤
            secondPricePayoff val true (val false) (val true) := by
          simpa [hDev, hTruth] using hNonneg
        exact this
      · -- Deviation wins and yields the same payoff as truthful bidding.
        have hnot : ¬ val false ≥ t := hdev
        have hDev :
            secondPricePayoff val true (val false) t =
              val true - val false := by
          have h := secondPricePayoff_true val (val false) t
          simpa [secondPricePayoff_true, hnot] using h
        simpa [hDev, hTruth] using
          (Nat.le_refl (val true - val false))
  intro s'
  simpa [NormalForm.isBestResponse, secondPriceGame,
        secondPriceTruthfulProfile, secondPricePayoff] using hAll s'

/-- Truthful bidding by both players forms a Nash equilibrium of the
    generic second-price auction for any valuation function `val`. -/
theorem secondPrice_nash (val : AuctionTruthPlayer → Nat) :
    NormalForm.NashEquilibrium (secondPriceGame val)
      (secondPriceTruthfulProfile val) := by
  classical
  intro i
  cases i with
  | false =>
      refine ⟨val false, ?_⟩
      exact secondPrice_bestResponse_truth_false val
  | true =>
      refine ⟨val true, ?_⟩
      exact secondPrice_bestResponse_truth_true val

/-- The generic second-price auction satisfies the incentive-compatibility
    statement for any valuation function `val`. -/
theorem secondPrice_incentiveCompatible
    (val : AuctionTruthPlayer → Nat) :
    NormalForm.IncentiveCompatibilityStatement
      (G := secondPriceGame val) := by
  classical
  refine ⟨secondPriceTruthfulProfile val, secondPrice_nash val⟩


/-
## Evolutionary / repeated-game add-ons
-/

namespace Evolution

open NormalForm

/-- A lightweight repeated-game wrapper around a base normal-form game. -/
structure RepeatedGame {Player : Type} (G : NormalForm Player) (T : Nat) where
  History : Type
  init : History
  step : History → G.Profile → History
  strategy : (i : Player) → History → G.Strategy i
  rounds : Nat := T

/-- Strict Nash condition at the played profile `σ` (each player cannot improve
by unilateral deviation from `σ i`). -/
def NashAt {Player : Type} (G : NormalForm Player) [DecidableEq Player]
    (σ : G.Profile) : Prop :=
  ∀ i : Player, NormalForm.isBestResponse (G := G) i σ (σ i)

/-- Pure-strategy ESS-style stability:
the profile is Nash-at-profile and every unilateral mutant is not weakly better
for the deviating player. -/
def ESS {Player : Type} (G : NormalForm Player) [DecidableEq Player]
    (σ : G.Profile) : Prop :=
  NashAt G σ ∧
  ∀ i : Player, ∀ mutant : G.Strategy i,
    mutant ≠ σ i →
      ¬ G.le
        (G.payoff (fun j => if h : j = i then cast (by cases h; rfl) mutant else σ j) i)
        (G.payoff σ i)

/-- One-shot Prisoner's Dilemma with `true = cooperate`, `false = defect`. -/
def prisonersDilemmaGame : NormalForm Bool :=
  { Strategy := fun _ => Bool
    , Payoff := Nat
    , le := fun a b => b ≤ a
    , payoff := fun σ i =>
        let me := σ i
        let other := σ (!i)
        match me, other with
        | true, true => 3  -- R
        | true, false => 0 -- S
        | false, true => 5 -- T
        | false, false => 1 } -- P

/-- Mutual defection profile. -/
def pdDefectProfile : NormalForm.Profile prisonersDilemmaGame :=
  fun _ => false

/-- Mutual cooperation profile. -/
def pdCooperateProfile : NormalForm.Profile prisonersDilemmaGame :=
  fun _ => true

/-- In one-shot PD, mutual defection is Nash-at-profile. -/
theorem pd_defect_is_nashAt :
    NashAt prisonersDilemmaGame pdDefectProfile := by
  intro i
  intro s'
  cases i <;> cases s' <;> simp [NashAt, pdDefectProfile, prisonersDilemmaGame]

/-- Compatibility theorem using the existing `NashEquilibrium` predicate. -/
theorem pd_defect_is_nash :
    NormalForm.NashEquilibrium prisonersDilemmaGame pdDefectProfile := by
  intro i
  refine ⟨false, ?_⟩
  intro s'
  cases i <;> cases s' <;> simp [pdDefectProfile, prisonersDilemmaGame]

/-- Mutual cooperation is not Nash-at-profile in one-shot PD. -/
theorem pd_cooperate_not_nashAt :
    ¬ NashAt prisonersDilemmaGame pdCooperateProfile := by
  intro h
  have hBR := h false
  have hle := hBR false
  simp [NashAt, pdCooperateProfile, prisonersDilemmaGame] at hle

/-- Hawk-Dove game (`true = hawk`, `false = dove`) with value `V` and cost `C`. -/
def hawkDoveGame (V C : Nat) : NormalForm Bool :=
  { Strategy := fun _ => Bool
    , Payoff := Nat
    , le := fun a b => b ≤ a
    , payoff := fun σ i =>
        let me := σ i
        let other := σ (!i)
        match me, other with
        | true, true => (V - C) / 2
        | true, false => V
        | false, true => 0
        | false, false => V / 2 }

/-- Mixed Hawk-Dove ESS certificate at probability `p = V / C`.
This keeps the expected-payoff statement explicit while remaining lightweight. -/
def hawkDoveMixedESS (V C : Nat) (p : Rat) : Prop :=
  V < C ∧ 0 < V ∧ p = (V : Rat) / (C : Rat)

/-- When `C > V > 0`, the canonical mixed Hawk-Dove proportion `V/C` is ESS
in the sense of `hawkDoveMixedESS`. -/
theorem hawkDove_mixed_ess (V C : Nat) (hCV : C > V) (hV : 0 < V) :
    hawkDoveMixedESS V C ((V : Rat) / (C : Rat)) := by
  refine ⟨hCV, hV, rfl⟩

/-- Public-goods game (simplified): each player either contributes (`true`) or
defects (`false`). Defectors keep full private payoff `n`; contributors get `r`. -/
def publicGoodsGame (n r : Nat) : NormalForm (Fin n) :=
  { Strategy := fun _ => Bool
    , Payoff := Nat
    , le := fun a b => b ≤ a
    , payoff := fun σ i =>
        if σ i then r else n }

/-- Defection is dominant in the simplified public-goods game whenever `r < n`. -/
theorem publicGoods_defect_dominant (n r : Nat) (h : r < n) :
    ∀ i : Fin n, NormalForm.isBestResponse (publicGoodsGame n r) i
      (fun _ => false) false := by
  intro i
  intro s'
  cases s' <;> simp [publicGoodsGame, h, Nat.le_of_lt h]

/-- Network reciprocity threshold in the natural-number form `b > c * k`
(`b/c > k` when `c > 0`). -/
def NowakCooperationCondition (b c k : Nat) : Prop :=
  0 < c ∧ c * k < b

/-- If the Nowak condition holds, cooperation is favored. -/
theorem nowak_cooperation_sufficient (b c k : Nat) :
    NowakCooperationCondition b c k → c * k < b := by
  intro h
  exact h.2

end Evolution



/-
## Registry bridge to `Governance.Spec.PropertyId`
-/

open HeytingLean.Governance

namespace Bridge

/-- Interpretation of governance/economics property identifiers for a
    given normal-form game. -/
def propertyHolds {Player}
    (G : NormalForm Player)
    (p : Governance.Spec.PropertyId)
    [DecidableEq Player] : Prop :=
  match p with
  | .incentiveCompatibility => NormalForm.IncentiveCompatibilityStatement (G := G)
  | .stakingEquilibrium     => NormalForm.IncentiveCompatibilityStatement (G := G)
  | .mevResistance          => True
  | .auctionTruthfulness    => NormalForm.IncentiveCompatibilityStatement (G := G)
  | .costOfAttack           => True
  | .slashingDeterrence     => True
  | .inflationDeflationModels => True
  | .liquidityMiningSafety  => True
  | .ballotPrivacy          => True
  | .tallyCorrectness       => True
  | .coercionResistance     => True
  | .receiptFreeness        => True
  | .proposalExecutionCorrectness => True
  | .timelockSecurity       => True
  | .quorumRequirements     => True
  | .vetoMechanismsCorrectness => True

/-- `incentiveCompatibility` holds for `trivialGame`. -/
theorem propertyHolds_incentiveCompatibility_trivialGame :
    propertyHolds trivialGame Governance.Spec.PropertyId.incentiveCompatibility := by
  classical
  simpa [propertyHolds] using trivialGame_incentiveCompatible

/-- `stakingEquilibrium` holds for `stakingGame`. -/
theorem propertyHolds_stakingEquilibrium_stakingGame :
    propertyHolds stakingGame Governance.Spec.PropertyId.stakingEquilibrium := by
  classical
  simpa [propertyHolds] using stakingGame_incentiveCompatible

/-- `auctionTruthfulness` holds for the example auction game. -/
theorem propertyHolds_auctionTruthfulness_auctionTruthGame :
    propertyHolds auctionTruthGame Governance.Spec.PropertyId.auctionTruthfulness := by
  classical
  simpa [propertyHolds] using auctionTruthGame_incentiveCompatible

/-- `auctionTruthfulness` holds for the generic second-price auction under
    any valuation function `val`. -/
theorem propertyHolds_auctionTruthfulness_secondPrice
    (val : AuctionTruthPlayer → Nat) :
    propertyHolds (secondPriceGame val)
      Governance.Spec.PropertyId.auctionTruthfulness := by
  classical
  simpa [propertyHolds] using secondPrice_incentiveCompatible val

end Bridge

end Game
end Economics
end HeytingLean
