import HeytingLean.LeanSP.Verify.VCDischarge

/-!
# LeanSP.RealWorld.TokenVestingVerified

Verified properties of a linear token vesting contract.

## Contract specification
- Beneficiary receives tokens linearly over [start, start + duration]
- `vestedAmount = totalAmount * elapsed / duration` (clamped to [0, totalAmount])
- `claimable = vestedAmount - claimed`
- `claim()` transfers claimable amount and updates `claimed`

## What is verified here
- **Vesting monotonicity**: vestedAmount(t1) ≤ vestedAmount(t2) for t1 ≤ t2
- **Vesting bounds**: 0 ≤ vestedAmount ≤ totalAmount always
- **Claim conservation**: claimed never exceeds totalAmount
- **Division safety**: duration > 0 prevents division by zero
- **Multiplication overflow**: totalAmount * elapsed overflow detection
- **Concrete pipeline tests**: Yul AST for the vesting calculation,
  executed through `execSimpleBlock`

## Honest boundary
Yul ASTs are manually transcribed from solc output. The full claim() function
includes msg.sender checks and ERC-20 token transfers — only the vesting
arithmetic is formalized here.
-/

namespace LeanSP.RealWorld

open LeanSP.Arith
open LeanSP.Yul
open LeanSP.EVM
open LeanSP.Verify
open LeanSP.Memory

-- ==========================================
-- Property 1: Vesting monotonicity
-- ==========================================

/-- Linear vesting is monotone: more elapsed time means more vested.
    If t1 ≤ t2 and totalAmount * t / duration doesn't overflow,
    then vested(t1) ≤ vested(t2).
    Models: vestedAmount = (totalAmount * elapsed) / duration -/
theorem vesting_monotone (totalAmount duration t1 t2 : Nat)
    (_ : duration > 0)
    (hT1 : t1 ≤ t2)
    (_ : t2 ≤ duration) :
    totalAmount * t1 / duration ≤ totalAmount * t2 / duration := by
  apply Nat.div_le_div_right
  exact Nat.mul_le_mul_left totalAmount hT1

-- ==========================================
-- Property 2: Vesting bounds
-- ==========================================

/-- Vested amount never exceeds totalAmount. -/
theorem vesting_upper_bound (totalAmount duration elapsed : Nat)
    (hDur : duration > 0)
    (hElapsed : elapsed ≤ duration) :
    totalAmount * elapsed / duration ≤ totalAmount := by
  calc totalAmount * elapsed / duration
      ≤ totalAmount * duration / duration := by
        apply Nat.div_le_div_right
        exact Nat.mul_le_mul_left totalAmount hElapsed
    _ = totalAmount := by
        rw [Nat.mul_div_cancel _ hDur]

/-- Vested amount at the start (elapsed = 0) is 0. -/
theorem vesting_at_start (totalAmount duration : Nat) (_hDur : duration > 0) :
    totalAmount * 0 / duration = 0 := by
  simp

/-- Vested amount at the end (elapsed = duration) is totalAmount. -/
theorem vesting_at_end (totalAmount duration : Nat) (hDur : duration > 0) :
    totalAmount * duration / duration = totalAmount := by
  exact Nat.mul_div_cancel totalAmount hDur

-- ==========================================
-- Property 3: Claim conservation
-- ==========================================

/-- After claiming, the cumulative claimed amount is correct:
    newClaimed = oldClaimed + claimable
    where claimable = vested - oldClaimed -/
theorem claim_conservation (_totalAmount vested oldClaimed : Nat)
    (_hVested : vested ≤ _totalAmount)
    (hClaimed : oldClaimed ≤ vested) :
    oldClaimed + (vested - oldClaimed) = vested := by
  omega

/-- Cumulative claimed never exceeds totalAmount. -/
theorem claimed_bounded (totalAmount vested oldClaimed : Nat)
    (hVested : vested ≤ totalAmount)
    (hClaimed : oldClaimed ≤ vested) :
    oldClaimed + (vested - oldClaimed) ≤ totalAmount := by
  omega

-- ==========================================
-- Property 4: Division safety
-- ==========================================

/-- EVM div(a, 0) = 0 (not undefined). The Solidity require(duration > 0)
    prevents this case, but even without it, EVM semantics are safe. -/
theorem evm_div_zero_safe (a : Word256) :
    div a Word256.zero = Word256.zero :=
  div_zero a

-- ==========================================
-- Property 5: Multiplication overflow detection
-- ==========================================

/-- When totalAmount * elapsed fits in 256 bits, the product is exact.
    When it doesn't, Solidity 0.8+ reverts via checked_mul. -/
theorem vesting_mul_no_overflow (totalAmount elapsed : Word256)
    (hFits : totalAmount.toNat * elapsed.toNat < 2^256) :
    (mul totalAmount elapsed).toNat = totalAmount.toNat * elapsed.toNat := by
  unfold mul; rw [BitVec.toNat_mul]; omega

/-- Overflow detection: if product ≥ 2^256, result wraps. -/
theorem vesting_mul_wraps (totalAmount elapsed : Word256)
    (_hOverflow : totalAmount.toNat * elapsed.toNat ≥ 2^256) :
    (mul totalAmount elapsed).toNat =
    (totalAmount.toNat * elapsed.toNat) % 2^256 := by
  unfold mul; exact BitVec.toNat_mul totalAmount elapsed

-- ==========================================
-- Yul AST: Linear vesting calculation (core arithmetic)
-- ==========================================
-- Models: vested = (totalAmount * elapsed) / duration
-- where elapsed = timestamp - start (computed before this block)

def vestingCalcBody : List Stmt :=
  [ .assign "product" (.call "mul" #[.ident "totalAmount", .ident "elapsed"]),
    .assign "vested" (.call "div" #[.ident "product", .ident "duration"]) ]

-- Concrete test: 1000 tokens, 50% elapsed (500/1000 = 500 vested)
#guard (match execSimpleBlock vestingCalcBody
    (mkYulState [("totalAmount", BitVec.ofNat 256 1000),
                 ("elapsed", BitVec.ofNat 256 500),
                 ("duration", BitVec.ofNat 256 1000),
                 ("product", BitVec.ofNat 256 0),
                 ("vested", BitVec.ofNat 256 0)]) with
  | .ok st => VarStore.get? st.vars "vested" == some (BitVec.ofNat 256 500)
  | _ => false) == true

-- Concrete test: 1000 tokens, 25% elapsed = 250 vested
#guard (match execSimpleBlock vestingCalcBody
    (mkYulState [("totalAmount", BitVec.ofNat 256 1000),
                 ("elapsed", BitVec.ofNat 256 250),
                 ("duration", BitVec.ofNat 256 1000),
                 ("product", BitVec.ofNat 256 0),
                 ("vested", BitVec.ofNat 256 0)]) with
  | .ok st => VarStore.get? st.vars "vested" == some (BitVec.ofNat 256 250)
  | _ => false) == true

-- Concrete test: 1000 tokens, 100% elapsed = 1000 vested
#guard (match execSimpleBlock vestingCalcBody
    (mkYulState [("totalAmount", BitVec.ofNat 256 1000),
                 ("elapsed", BitVec.ofNat 256 1000),
                 ("duration", BitVec.ofNat 256 1000),
                 ("product", BitVec.ofNat 256 0),
                 ("vested", BitVec.ofNat 256 0)]) with
  | .ok st => VarStore.get? st.vars "vested" == some (BitVec.ofNat 256 1000)
  | _ => false) == true

-- Concrete test: 0 tokens elapsed = 0 vested
#guard (match execSimpleBlock vestingCalcBody
    (mkYulState [("totalAmount", BitVec.ofNat 256 1000),
                 ("elapsed", BitVec.ofNat 256 0),
                 ("duration", BitVec.ofNat 256 1000),
                 ("product", BitVec.ofNat 256 0),
                 ("vested", BitVec.ofNat 256 0)]) with
  | .ok st => VarStore.get? st.vars "vested" == some (BitVec.ofNat 256 0)
  | _ => false) == true

-- Concrete test: 1_000_000 tokens, 365 days vesting, 182 days elapsed
-- Expected: 1000000 * 182 / 365 = 498630 (integer division)
#guard (match execSimpleBlock vestingCalcBody
    (mkYulState [("totalAmount", BitVec.ofNat 256 1000000),
                 ("elapsed", BitVec.ofNat 256 182),
                 ("duration", BitVec.ofNat 256 365),
                 ("product", BitVec.ofNat 256 0),
                 ("vested", BitVec.ofNat 256 0)]) with
  | .ok st => VarStore.get? st.vars "vested" == some (BitVec.ofNat 256 498630)
  | _ => false) == true

-- ==========================================
-- Yul AST: Claimable calculation
-- ==========================================

def claimableCalcBody : List Stmt :=
  [ .assign "claimable" (.call "sub" #[.ident "vested", .ident "claimed"]) ]

-- Concrete test: 500 vested, 200 claimed = 300 claimable
#guard (match execSimpleBlock claimableCalcBody
    (mkYulState [("vested", BitVec.ofNat 256 500),
                 ("claimed", BitVec.ofNat 256 200),
                 ("claimable", BitVec.ofNat 256 0)]) with
  | .ok st => VarStore.get? st.vars "claimable" == some (BitVec.ofNat 256 300)
  | _ => false) == true

-- ==========================================
-- VC discharge integration tests
-- ==========================================

#guard (dischargeVC "vesting_50pct"
    vestingCalcBody
    (mkYulState [("totalAmount", BitVec.ofNat 256 1000),
                 ("elapsed", BitVec.ofNat 256 500),
                 ("duration", BitVec.ofNat 256 1000),
                 ("product", BitVec.ofNat 256 0),
                 ("vested", BitVec.ofNat 256 0)])
    (fun st => VarStore.get? st.vars "vested" == some (BitVec.ofNat 256 500))
  matches .discharged _) == true

#guard (dischargeVC "vesting_full"
    vestingCalcBody
    (mkYulState [("totalAmount", BitVec.ofNat 256 1000),
                 ("elapsed", BitVec.ofNat 256 1000),
                 ("duration", BitVec.ofNat 256 1000),
                 ("product", BitVec.ofNat 256 0),
                 ("vested", BitVec.ofNat 256 0)])
    (fun st => VarStore.get? st.vars "vested" == some (BitVec.ofNat 256 1000))
  matches .discharged _) == true

#guard (dischargeVC "claimable_calc"
    claimableCalcBody
    (mkYulState [("vested", BitVec.ofNat 256 750),
                 ("claimed", BitVec.ofNat 256 250),
                 ("claimable", BitVec.ofNat 256 0)])
    (fun st => VarStore.get? st.vars "claimable" == some (BitVec.ofNat 256 500))
  matches .discharged _) == true

end LeanSP.RealWorld
