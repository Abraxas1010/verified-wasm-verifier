import Mathlib.Data.Fintype.Basic

/-!
# HeytingLean.Blockchain.Contracts.LeanYulDSL.BankModel

A tiny "financial contract" model used as the *spec/proof* side for a
Lean→Yul pipeline.

This is intentionally minimal:
- balances are indexed by a finite set of users `Fin n`;
- `deposit` and `withdraw` are the only state transitions; and
- we prove basic local invariants about balance updates.

The code generator targets Yul/EVM, but the proof is about this abstract model.
-/

namespace HeytingLean.Blockchain.Contracts.LeanYulDSL

structure BankState (n : Nat) where
  /-- The contract ETH balance (abstract). -/
  eth : Nat
  /-- Per-user balances (abstract). -/
  bal : Fin n → Nat

namespace BankState

def deposit {n : Nat} (s : BankState n) (who : Fin n) (v : Nat) : BankState n :=
  {
    eth := s.eth + v
    bal := Function.update s.bal who (s.bal who + v)
  }

def withdraw {n : Nat} (s : BankState n) (who : Fin n) (v : Nat) : BankState n :=
  {
    eth := s.eth - v
    bal := Function.update s.bal who (s.bal who - v)
  }

@[simp] lemma deposit_eth {n : Nat} (s : BankState n) (who : Fin n) (v : Nat) :
    (deposit s who v).eth = s.eth + v := by rfl

@[simp] lemma withdraw_eth {n : Nat} (s : BankState n) (who : Fin n) (v : Nat) :
    (withdraw s who v).eth = s.eth - v := by rfl

@[simp] lemma deposit_bal_self {n : Nat} (s : BankState n) (who : Fin n) (v : Nat) :
    (deposit s who v).bal who = s.bal who + v := by
  simp [BankState.deposit]

lemma deposit_bal_other {n : Nat} (s : BankState n) (who other : Fin n) (v : Nat)
    (h : other ≠ who) :
    (deposit s who v).bal other = s.bal other := by
  simp [BankState.deposit, Function.update, h]

@[simp] lemma withdraw_bal_self {n : Nat} (s : BankState n) (who : Fin n) (v : Nat) :
    (withdraw s who v).bal who = s.bal who - v := by
  simp [BankState.withdraw]

lemma withdraw_bal_other {n : Nat} (s : BankState n) (who other : Fin n) (v : Nat)
    (h : other ≠ who) :
    (withdraw s who v).bal other = s.bal other := by
  simp [BankState.withdraw, Function.update, h]

end BankState

end HeytingLean.Blockchain.Contracts.LeanYulDSL
