import HeytingLean.LeanSP.Verify.VCDischarge

/-!
# LeanSP.RealWorld.SimpleVaultVerified

Verified properties of a SimpleVault ETH vault contract.

## Contract specification
- Users deposit ETH, tracked in per-user balance mapping
- Users withdraw ETH up to their balance
- Total deposited tracks sum of all user balances
- Balance conservation: deposit/withdraw preserve accounting invariant

## What is verified here
- **Balance conservation**: deposit adds, withdraw subtracts, sum preserved
- **Withdrawal safety**: checked subtraction reverts on insufficient balance
- **Storage non-interference**: writing one user's balance doesn't affect another's
- **Deposit overflow safety**: checked addition reverts on overflow
- **Concrete pipeline tests**: Yul AST for checked_add deposit and checked_sub
  withdraw, executed through `execSimpleBlock`

## Honest boundary
Yul ASTs are manually transcribed from solc output. The keccak256-based
mapping slot addressing used by real Solidity `mapping(address => uint256)`
is modeled abstractly via distinct Word256 slot addresses. The mapping layout
formula `keccak256(abi.encode(key, slot))` is NOT verified here — that would
require Phase 6 cross-contract + ABI reasoning.
-/

namespace LeanSP.RealWorld

open LeanSP.Arith
open LeanSP.Yul
open LeanSP.EVM
open LeanSP.Verify
open LeanSP.Memory

-- ==========================================
-- Property 1: Deposit/withdraw balance conservation
-- ==========================================

/-- After depositing `amount`, the user's balance increases by exactly `amount`,
    provided no overflow. -/
theorem vault_deposit_balance (oldBalance amount : Word256)
    (hNoOverflow : oldBalance.toNat + amount.toNat < 2^256) :
    (add oldBalance amount).toNat = oldBalance.toNat + amount.toNat := by
  unfold add; rw [BitVec.toNat_add]; omega

/-- After withdrawing `amount`, the user's balance decreases by exactly `amount`,
    provided sufficient balance. -/
theorem vault_withdraw_balance (oldBalance amount : Word256)
    (hSufficient : oldBalance.toNat ≥ amount.toNat) :
    (sub oldBalance amount).toNat = oldBalance.toNat - amount.toNat := by
  unfold sub; simp [BitVec.toNat_sub]; omega

/-- Deposit then withdraw same amount: balance is unchanged.
    The key two-party conservation property. -/
theorem vault_deposit_withdraw_roundtrip (balance amount : Word256)
    (hNoOverflow : balance.toNat + amount.toNat < 2^256) :
    (sub (add balance amount) amount).toNat = balance.toNat := by
  have h1 := vault_deposit_balance balance amount hNoOverflow
  have h2 : (add balance amount).toNat ≥ amount.toNat := by omega
  rw [vault_withdraw_balance (add balance amount) amount h2]
  omega

-- ==========================================
-- Property 2: Withdrawal safety — underflow detection
-- ==========================================

/-- If balance < amount, subtraction wraps (Solidity's checked_sub reverts). -/
theorem vault_withdraw_underflow_wraps (balance amount : Word256)
    (hInsufficient : balance.toNat < amount.toNat) :
    (sub balance amount).toNat ≠ balance.toNat - amount.toNat := by
  unfold sub; simp [BitVec.toNat_sub]; omega

-- ==========================================
-- Property 3: Storage non-interference for user balances
-- ==========================================

/-- Writing to one user's balance slot does not affect another user's balance.
    Models the fact that keccak256(addr1, 0) ≠ keccak256(addr2, 0) for addr1 ≠ addr2
    (collision resistance). -/
theorem vault_user_isolation (storage : EVMStorage) (slotA slotB : Word256)
    (newBalB : Word256) (hNe : (slotA == slotB) = false) :
    (storage.sstore slotB newBalB).sload slotA = storage.sload slotA :=
  EVMStorage.sload_sstore_ne storage slotA slotB newBalB hNe

/-- Read-after-write: updating a user's balance is immediately visible. -/
theorem vault_user_update (storage : EVMStorage) (slot newBal : Word256) :
    (storage.sstore slot newBal).sload slot = newBal :=
  EVMStorage.sload_sstore_same storage slot newBal

-- ==========================================
-- Property 4: Deposit overflow detection
-- ==========================================

/-- Deposit overflow criterion: checked_add's gt guard fires exactly when
    the deposit would overflow. (Reuses SafeMathVerified.add_overflow_iff.) -/
theorem vault_deposit_overflow_iff (balance amount : Word256) :
    balance.toNat > (add balance amount).toNat ↔
    balance.toNat + amount.toNat ≥ 2^256 := by
  constructor
  · intro h; unfold add at h; rw [BitVec.toNat_add] at h; omega
  · intro h; unfold add; rw [BitVec.toNat_add]; omega

-- ==========================================
-- Property 5: Total deposited tracking
-- ==========================================

/-- Two-user deposit conservation: totalDeposited = balanceA + balanceB
    is preserved through individual deposits, given no overflow. -/
theorem vault_total_conservation (balA balB totalDep depositAmt : Word256)
    (hInvariant : totalDep.toNat = balA.toNat + balB.toNat)
    (hNoOverflowBal : balA.toNat + depositAmt.toNat < 2^256)
    (hNoOverflowTotal : totalDep.toNat + depositAmt.toNat < 2^256) :
    (add totalDep depositAmt).toNat =
    (add balA depositAmt).toNat + balB.toNat := by
  rw [vault_deposit_balance totalDep depositAmt hNoOverflowTotal]
  rw [vault_deposit_balance balA depositAmt hNoOverflowBal]
  omega

-- ==========================================
-- Yul AST: Checked deposit (add with overflow revert)
-- ==========================================
-- This is the checked_add pattern from SafeMath, applied to deposit:
-- sum = add(balance, amount)
-- if gt(balance, sum) { revert(0, 0) }
-- (i.e., if the old balance exceeds the new sum, overflow occurred)

def checkedDepositBody : List Stmt :=
  [ .assign "newBalance" (.call "add" #[.ident "balance", .ident "amount"]),
    .if_ (.call "gt" #[.ident "balance", .ident "newBalance"])
      #[.revert #[.nat 0, .nat 0]] ]

-- Concrete test: deposit 3 into balance 7 = 10
#guard (match execSimpleBlock checkedDepositBody
    (mkYulState [("balance", BitVec.ofNat 256 7),
                 ("amount", BitVec.ofNat 256 3),
                 ("newBalance", BitVec.ofNat 256 0)]) with
  | .ok st => VarStore.get? st.vars "newBalance" == some (BitVec.ofNat 256 10)
  | _ => false) == true

-- Concrete test: deposit MAX into balance 1 reverts (overflow)
#guard (match execSimpleBlock checkedDepositBody
    (mkYulState [("balance", Word256.maxVal),
                 ("amount", BitVec.ofNat 256 1),
                 ("newBalance", BitVec.ofNat 256 0)]) with
  | .revert _ => true
  | _ => false) == true

-- Concrete test: deposit 0 into balance 0 = 0
#guard (match execSimpleBlock checkedDepositBody
    (mkYulState [("balance", BitVec.ofNat 256 0),
                 ("amount", BitVec.ofNat 256 0),
                 ("newBalance", BitVec.ofNat 256 0)]) with
  | .ok st => VarStore.get? st.vars "newBalance" == some (BitVec.ofNat 256 0)
  | _ => false) == true

-- ==========================================
-- Yul AST: Checked withdrawal (sub with underflow revert)
-- ==========================================

def checkedWithdrawBody : List Stmt :=
  [ .if_ (.call "gt" #[.ident "amount", .ident "balance"])
      #[.revert #[.nat 0, .nat 0]],
    .assign "newBalance" (.call "sub" #[.ident "balance", .ident "amount"]) ]

-- Concrete test: withdraw 3 from balance 10 = 7
#guard (match execSimpleBlock checkedWithdrawBody
    (mkYulState [("balance", BitVec.ofNat 256 10),
                 ("amount", BitVec.ofNat 256 3),
                 ("newBalance", BitVec.ofNat 256 0)]) with
  | .ok st => VarStore.get? st.vars "newBalance" == some (BitVec.ofNat 256 7)
  | _ => false) == true

-- Concrete test: withdraw 10 from balance 3 reverts (underflow)
#guard (match execSimpleBlock checkedWithdrawBody
    (mkYulState [("balance", BitVec.ofNat 256 3),
                 ("amount", BitVec.ofNat 256 10),
                 ("newBalance", BitVec.ofNat 256 0)]) with
  | .revert _ => true
  | _ => false) == true

-- Concrete test: withdraw all
#guard (match execSimpleBlock checkedWithdrawBody
    (mkYulState [("balance", BitVec.ofNat 256 100),
                 ("amount", BitVec.ofNat 256 100),
                 ("newBalance", BitVec.ofNat 256 0)]) with
  | .ok st => VarStore.get? st.vars "newBalance" == some (BitVec.ofNat 256 0)
  | _ => false) == true

-- ==========================================
-- VC discharge integration tests
-- ==========================================

#guard (dischargeVC "vault_deposit_ok"
    checkedDepositBody
    (mkYulState [("balance", BitVec.ofNat 256 50),
                 ("amount", BitVec.ofNat 256 25),
                 ("newBalance", BitVec.ofNat 256 0)])
    (fun st => VarStore.get? st.vars "newBalance" == some (BitVec.ofNat 256 75))
  matches .discharged _) == true

#guard (dischargeVC "vault_deposit_overflow"
    checkedDepositBody
    (mkYulState [("balance", Word256.maxVal),
                 ("amount", BitVec.ofNat 256 1),
                 ("newBalance", BitVec.ofNat 256 0)])
    (fun _ => true)
  matches .reverted _) == true

#guard (dischargeVC "vault_withdraw_ok"
    checkedWithdrawBody
    (mkYulState [("balance", BitVec.ofNat 256 100),
                 ("amount", BitVec.ofNat 256 40),
                 ("newBalance", BitVec.ofNat 256 0)])
    (fun st => VarStore.get? st.vars "newBalance" == some (BitVec.ofNat 256 60))
  matches .discharged _) == true

#guard (dischargeVC "vault_withdraw_underflow"
    checkedWithdrawBody
    (mkYulState [("balance", BitVec.ofNat 256 5),
                 ("amount", BitVec.ofNat 256 10),
                 ("newBalance", BitVec.ofNat 256 0)])
    (fun _ => true)
  matches .reverted _) == true

end LeanSP.RealWorld
