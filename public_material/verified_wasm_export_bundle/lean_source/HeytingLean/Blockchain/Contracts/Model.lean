import HeytingLean.Blockchain.Contracts.Spec
import Mathlib.Logic.Basic

/-
# Blockchain.Contracts.Model

Abstract contract semantics and a minimal ERC20-style model.

This module provides:
* a generic `ContractModel` record with a step function;
* a `run` helper to execute finite call traces; and
* a lightweight ERC20-like model and invariant statement shape.

The focus is on exposing stable types and names; detailed correctness
proofs are deferred to later dedicated developments.
-/

namespace HeytingLean
namespace Blockchain
namespace Contracts
namespace Model

/-- Generic single-contract execution model. -/
structure ContractModel (State Call Error : Type) where
  init : State
  step : State → Call → Except Error State

namespace ContractModel

/-- Generic lemma: folding an `Except`-based step function from an
    initial error accumulator stays in that error state. -/
lemma foldl_bind_from_error
    {E β α : Type} (f : β → α → Except E β)
    (e : E) (xs : List α) :
    List.foldl
      (fun (acc : Except E β) (x : α) =>
        match acc with
        | .error err => .error err
        | .ok v => f v x)
      (.error e : Except E β) xs =
    (.error e : Except E β) := by
  classical
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [List.foldl, ih]

/-- Execute a finite call trace starting from state `s`. -/
def runFrom {State Call Error}
    (M : ContractModel State Call Error)
    (s : State) (calls : List Call) : Except Error State :=
  calls.foldl
    (fun acc c =>
      acc.bind (fun st => M.step st c))
    (.ok s)

/-- Execute a finite call trace from the model’s initial state. -/
def run {State Call Error}
    (M : ContractModel State Call Error)
    (calls : List Call) : Except Error State :=
  runFrom M M.init calls

/-- Specialisation of `runFrom` to an empty trace. -/
lemma runFrom_nil {State Call Error}
    (M : ContractModel State Call Error) (s : State) :
    runFrom M s [] = (.ok s : Except Error State) := by
  simp [runFrom, ContractModel.runFrom]

/-- Decomposition of `runFrom` over a non-empty trace. -/
lemma runFrom_cons {State Call Error}
    (M : ContractModel State Call Error)
    (s : State) (c : Call) (cs : List Call) :
    runFrom M s (c :: cs) =
      match M.step s c with
      | .ok s1 => runFrom M s1 cs
      | .error e => .error e := by
  classical
  -- Case split on the first step and simplify both sides.
  cases hStep : M.step s c with
  | ok s1 =>
      simp [runFrom, ContractModel.runFrom, List.foldl,
            Except.bind, hStep]
  | error e =>
      -- From an error accumulator, the fold stays in the same error.
      simp [runFrom, ContractModel.runFrom, List.foldl,
            Except.bind, hStep]
      exact
        foldl_bind_from_error
          (f := fun (v : State) (c : Call) => M.step v c)
          (e := e) (xs := cs)

end ContractModel

/-- Abstract address type for the ERC20-style model. -/
abbrev Address := String

/-- Minimal ERC20-style state:
* `balances` for token balances;
* `allowances` for authorised spending; and
* `totalSupply` for the total token supply.

This is intentionally abstract and not tied to any particular VM. -/
structure ERC20State where
  balances    : Address → Nat
  allowances  : Address → Address → Nat
  totalSupply : Nat

/-- ERC20-style calls. This is a minimal subset sufficient for
specification and small demos. -/
inductive ERC20Call where
  | transfer (fromAddr toAddr : Address) (amount : Nat)
  | approve (owner spender : Address) (amount : Nat)
  | transferFrom (spender fromAddr toAddr : Address) (amount : Nat)

/-- Simple ERC20 error taxonomy. -/
inductive ERC20Error where
  | insufficientBalance
  | insufficientAllowance

namespace ERC20State

/-- Update the balance for a single address using a modifier `f`. -/
def updateBalance (s : ERC20State) (addr : Address)
    (f : Nat → Nat) : ERC20State :=
  { s with
    balances := fun a =>
      if a = addr then
        f (s.balances addr)
      else
        s.balances a }

/-- Update the allowance for a given owner/spender pair using `f`. -/
def updateAllowance (s : ERC20State) (owner spender : Address)
    (f : Nat → Nat) : ERC20State :=
  { s with
    allowances := fun o =>
      if o = owner then
        fun sp =>
          if sp = spender then
            f (s.allowances owner spender)
          else
            s.allowances o sp
      else
        s.allowances o }

end ERC20State

open ERC20State

/-- Naive ERC20-style transition function.

This is a deliberately lightweight model:
* `transfer` checks balance and debits/credits accounts;
* `approve` adjusts allowances; and
* `transferFrom` checks both allowance and balance.

It is intended as a target for future correctness proofs rather than a
complete production semantics. -/
def erc20Step (s : ERC20State) (c : ERC20Call) :
    Except ERC20Error ERC20State :=
  match c with
  | ERC20Call.transfer fromAddr toAddr amount =>
      let balFrom := s.balances fromAddr
      if amount ≤ balFrom then
        let s' := s.updateBalance fromAddr (fun b => b - amount)
        let s'' := s'.updateBalance toAddr (fun b => b + amount)
        .ok s''
      else
        .error .insufficientBalance
  | ERC20Call.approve owner spender amount =>
      let s' := s.updateAllowance owner spender (fun _ => amount)
      .ok s'
  | ERC20Call.transferFrom spender fromAddr toAddr amount =>
      let balFrom := s.balances fromAddr
      let allow := s.allowances fromAddr spender
      if amount ≤ balFrom then
        if amount ≤ allow then
          let s₁ := s.updateBalance fromAddr (fun b => b - amount)
          let s₂ := s₁.updateBalance toAddr (fun b => b + amount)
          let s₃ := s₂.updateAllowance fromAddr spender (fun a => a - amount)
          .ok s₃
        else
          .error .insufficientAllowance
      else
        .error .insufficientBalance

/-- Default initial ERC20 state used by the demo model. -/
def erc20Init : ERC20State :=
  { balances := fun _ => 0
    , allowances := fun _ _ => 0
    , totalSupply := 0 }

/-- ERC20 contract model instance. -/
def erc20Model : ContractModel ERC20State ERC20Call ERC20Error :=
  { init := erc20Init
    , step := erc20Step }

/-- ERC20 invariants: in this minimal model, the total supply is a
    fixed constant equal to the initial supply. Since `erc20Step` never
    updates `totalSupply`, any successful execution from the initial
    state preserves this value. -/
def ERC20Invariants (s : ERC20State) : Prop :=
  s.totalSupply = erc20Init.totalSupply

/-- Statement shape for ERC20 invariants: all successful runs of the
    model from the initial state satisfy `ERC20Invariants`. -/
def ERC20InvariantStatement : Prop :=
  ∀ calls s',
    ContractModel.run erc20Model calls = .ok s' →
    ERC20Invariants s'

open ContractModel

/-- A concrete successful (non-empty) ERC20 run: `approve` always succeeds and updates allowances. -/
theorem erc20_run_single_approve_ok (owner spender : Address) (amount : Nat) :
    ContractModel.run erc20Model [ERC20Call.approve owner spender amount] =
      .ok (erc20Init.updateAllowance owner spender (fun _ => amount)) := by
  simp [ContractModel.run, ContractModel.runFrom_cons, ContractModel.runFrom_nil,
    erc20Model, erc20Init, erc20Step]

/-- The `approve` transition sets the owner/spender allowance to the requested amount. -/
theorem erc20Init_updateAllowance_self (owner spender : Address) (amount : Nat) :
    (erc20Init.updateAllowance owner spender (fun _ => amount)).allowances owner spender = amount := by
  simp [erc20Init, ERC20State.updateAllowance]

/-- Existence of a nontrivial successful trace (useful to preempt “vacuity” concerns in reviews). -/
theorem erc20_nontrivial_success_example :
    ∃ s' : ERC20State,
      ContractModel.run erc20Model [ERC20Call.approve "alice" "bob" 7] = .ok s' ∧
        s'.allowances "alice" "bob" = 7 := by
  refine ⟨erc20Init.updateAllowance "alice" "bob" (fun _ => 7), ?_, ?_⟩
  · simpa using (erc20_run_single_approve_ok (owner := "alice") (spender := "bob") (amount := 7))
  · simpa using (erc20Init_updateAllowance_self (owner := "alice") (spender := "bob") (amount := 7))

/-- If `erc20Step` succeeds, it does not change `totalSupply`. -/
theorem erc20Step_preserves_totalSupply
    (s s' : ERC20State) (c : ERC20Call)
    (h : erc20Step s c = .ok s') :
    s'.totalSupply = s.totalSupply := by
  classical
  cases c with
  | transfer fromAddr toAddr amount =>
      by_cases hle : amount ≤ s.balances fromAddr
      ·
        simp [erc20Step, hle] at h
        cases h
        simp [ERC20State.updateBalance]
      ·
        have : False := by
          simp [erc20Step, hle] at h
        exact False.elim this
  | approve owner spender amount =>
      simp [erc20Step] at h
      cases h
      simp [ERC20State.updateAllowance]
  | transferFrom spender fromAddr toAddr amount =>
      by_cases hb : amount ≤ s.balances fromAddr
      ·
        by_cases ha : amount ≤ s.allowances fromAddr spender
        ·
          simp [erc20Step, hb, ha] at h
          cases h
          simp [ERC20State.updateBalance, ERC20State.updateAllowance]
        ·
          have : False := by
            simp [erc20Step, hb, ha] at h
          exact False.elim this
      ·
        have : False := by
          simp [erc20Step, hb] at h
        exact False.elim this

/-- The initial ERC20 state satisfies the invariant. -/
theorem erc20Init_invariants : ERC20Invariants erc20Init := by
  simp [ERC20Invariants, erc20Init]

/-- Single-step preservation of `ERC20Invariants` along successful
    `erc20Step` transitions. -/
theorem erc20Step_preserves_invariants
    (s s' : ERC20State) (c : ERC20Call)
    (hInv : ERC20Invariants s)
    (hStep : erc20Step s c = .ok s') :
    ERC20Invariants s' := by
  unfold ERC20Invariants at hInv ⊢
  have hTotal := erc20Step_preserves_totalSupply s s' c hStep
  exact hTotal.trans hInv

/-- Run-level preservation of `ERC20Invariants` along successful
    `ContractModel.runFrom` executions of the ERC20 model. -/
theorem erc20_runFrom_preserves_invariants
    (calls : List ERC20Call) :
    ∀ (s s' : ERC20State),
      ERC20Invariants s →
      runFrom erc20Model s calls = .ok s' →
      ERC20Invariants s' := by
  classical
  induction calls with
  | nil =>
      intro s s' hInv hRun
      -- No calls: `runFrom` returns the input state unchanged.
      simp [ContractModel.runFrom, runFrom] at hRun
      cases hRun
      simpa using hInv
  | cons c cs ih =>
      intro s s' hInv hRun
      -- Decompose the first step of the run.
      have hCons := ContractModel.runFrom_cons (M := erc20Model) s c cs
      -- Case split on the first ERC20 step.
      cases hStep : erc20Step s c with
      | ok s1 =>
          -- From `runFrom_cons` and `hStep` we learn that the whole run
          -- is just `runFrom` from the intermediate state `s1`.
          have hCons' :
              runFrom erc20Model s (c :: cs) =
              runFrom erc20Model s1 cs := by
            simpa [erc20Model, hStep] using hCons
          have hRun₁ : runFrom erc20Model s1 cs = .ok s' := by
            simpa [hCons'] using hRun
          -- Step-level invariants from `s` to `s1`.
          have hInv₁ : ERC20Invariants s1 :=
            erc20Step_preserves_invariants s s1 c hInv hStep
          -- Apply the induction hypothesis to the tail.
          exact ih s1 s' hInv₁ hRun₁
      | error e =>
          -- In this branch `runFrom` cannot succeed.
          have hCons_err :
              runFrom erc20Model s (c :: cs) =
              (.error e : Except ERC20Error ERC20State) := by
            simpa [erc20Model, hStep] using hCons
          have : False := by
            -- Combine `hRun` with the error equation.
            have hRun' := hRun
            simp [hCons_err] at hRun'
          exact False.elim this

/-- From the ERC20 initial state, all successful runs satisfy the
    invariant `ERC20Invariants`. -/
theorem erc20InvariantStatement_holds : ERC20InvariantStatement := by
  intro calls s' hRun
  -- Initial state satisfies the invariant.
  have hInv0 : ERC20Invariants erc20Init := erc20Init_invariants
  -- `ContractModel.run` is `runFrom` from the initial state.
  have hRunFrom :
      runFrom erc20Model erc20Init calls = .ok s' := by
    simpa [ContractModel.run, ContractModel.runFrom, runFrom] using hRun
  -- Apply the run-level preservation lemma.
  exact erc20_runFrom_preserves_invariants calls erc20Init s' hInv0 hRunFrom

end Model
end Contracts
end Blockchain
end HeytingLean
