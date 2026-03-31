import HeytingLean.LeanSP.Lang.EVMPrimops

/-!
# LeanSP.Tests.EVMPrimopTests

#eval tests for EVM primop dispatch (Phase 2 gate: ≥7 tests).
-/

namespace LeanSP.Tests

open LeanSP.Arith
open LeanSP.EVM

-- Helper: create a minimal YulState for testing
def testState : YulState :=
  YulState.init EVMState.default #[]

-- Test 1: add primop
#eval do
  match evalPurePrimop "add" [BitVec.ofNat 256 7, BitVec.ofNat 256 3] with
  | some [v] => return s!"add(7,3) = {v.toNat}"  -- expect 10
  | _ => return "FAIL"

-- Test 2: sub primop
#eval do
  match evalPurePrimop "sub" [BitVec.ofNat 256 10, BitVec.ofNat 256 3] with
  | some [v] => return s!"sub(10,3) = {v.toNat}"  -- expect 7
  | _ => return "FAIL"

-- Test 3: div primop (div by zero)
#eval do
  match evalPurePrimop "div" [BitVec.ofNat 256 7, BitVec.ofNat 256 0] with
  | some [v] => return s!"div(7,0) = {v.toNat}"  -- expect 0
  | _ => return "FAIL"

-- Test 4: gt primop
#eval do
  match evalPurePrimop "gt" [BitVec.ofNat 256 7, BitVec.ofNat 256 3] with
  | some [v] => return s!"gt(7,3) = {v.toNat}"  -- expect 1
  | _ => return "FAIL"

-- Test 5: iszero primop
#eval do
  match evalPurePrimop "iszero" [BitVec.ofNat 256 0] with
  | some [v] => return s!"iszero(0) = {v.toNat}"  -- expect 1
  | _ => return "FAIL"

-- Test 6: eq primop
#eval do
  match evalPurePrimop "eq" [BitVec.ofNat 256 42, BitVec.ofNat 256 42] with
  | some [v] => return s!"eq(42,42) = {v.toNat}"  -- expect 1
  | _ => return "FAIL"

-- Test 7: shl primop
#eval do
  match evalPurePrimop "shl" [BitVec.ofNat 256 4, BitVec.ofNat 256 1] with
  | some [v] => return s!"shl(4,1) = {v.toNat}"  -- expect 16
  | _ => return "FAIL"

-- Test 8: and primop
#eval do
  match evalPurePrimop "and" [BitVec.ofNat 256 0xFF, BitVec.ofNat 256 0x0F] with
  | some [v] => return s!"and(0xFF,0x0F) = {v.toNat}"  -- expect 15
  | _ => return "FAIL"

-- Test 9: caller read primop
#eval do
  let st := testState
  match evalReadPrimop "caller" [] st with
  | some [v] => return s!"caller() = {v.toNat}"  -- expect 0 (default)
  | _ => return "FAIL"

end LeanSP.Tests
