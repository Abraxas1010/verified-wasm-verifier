import HeytingLean.LeanSP.Arith.Word256
import HeytingLean.LeanSP.Arith.SignedArith

/-!
# LeanSP.Tests.Word256Tests

#eval tests for Word256 arithmetic (Phase 2 gate: ≥8 tests).
Constraint H8: primop semantics must be testable via #eval.
-/

namespace LeanSP.Tests

open LeanSP.Arith

-- Test 1: Basic addition
#eval (add (BitVec.ofNat 256 7) (BitVec.ofNat 256 3)).toNat  -- expect 10

-- Test 2: Addition overflow (wraps mod 2^256)
#eval (add Word256.maxVal Word256.one).toNat  -- expect 0

-- Test 3: Subtraction
#eval (sub (BitVec.ofNat 256 10) (BitVec.ofNat 256 3)).toNat  -- expect 7

-- Test 4: Division
#eval (div (BitVec.ofNat 256 10) (BitVec.ofNat 256 3)).toNat  -- expect 3

-- Test 5: Division by zero (EVM convention: returns 0)
#eval (div (BitVec.ofNat 256 7) Word256.zero).toNat  -- expect 0

-- Test 6: Modulo
#eval (mod (BitVec.ofNat 256 10) (BitVec.ofNat 256 3)).toNat  -- expect 1

-- Test 7: Modulo by zero (EVM convention: returns 0)
#eval (mod (BitVec.ofNat 256 7) Word256.zero).toNat  -- expect 0

-- Test 8: Comparison lt
#eval (lt (BitVec.ofNat 256 3) (BitVec.ofNat 256 7)).toNat  -- expect 1

-- Test 9: Comparison gt
#eval (gt (BitVec.ofNat 256 7) (BitVec.ofNat 256 3)).toNat  -- expect 1

-- Test 10: isZero
#eval (isZero Word256.zero).toNat  -- expect 1
#eval (isZero Word256.one).toNat   -- expect 0

-- Test 11: Bitwise and
#eval (and (BitVec.ofNat 256 0xFF) (BitVec.ofNat 256 0x0F)).toNat  -- expect 15

-- Test 12: Multiplication
#eval (mul (BitVec.ofNat 256 7) (BitVec.ofNat 256 6)).toNat  -- expect 42

end LeanSP.Tests
