import HeytingLean.LeanSP.Lang.YulSemantics
import HeytingLean.LeanSP.Verify.VCDischarge
import HeytingLean.LeanSP.RealWorld.SafeMathVerified
import HeytingLean.BountyHunter.Solc.YulTextMini.EffectSemantics
import HeytingLean.BountyHunter.Solc.YulTextMini.Parse

/-!
# LeanSP.Tests.SemanticsParity

Assertive parity tests: value-level semantics vs expected results.
Uses `#guard` for fail-fast checking — wrong values fail the build.
Cross-validates with YulTextMini effect semantics (H9).
-/

namespace LeanSP.Tests

open LeanSP.Yul
open LeanSP.Arith
open LeanSP.EVM
open LeanSP.Verify
open HeytingLean.BountyHunter.Solc.YulTextMini

private def mkSt := YulState.init EVMState.default #[]
private abbrev S := HeytingLean.BountyHunter.Solc.YulTextMini.Stmt

-- ==========================================
-- Assertive tests (#guard fails build on mismatch)
-- ==========================================

-- Helper: extract variable value from execution result
private def evalAndGet (stmts : Array S) (varName : String) : Option Nat :=
  match execBlock 100 stmts mkSt with
  | .ok st' => (VarStore.get? st'.vars varName).map BitVec.toNat
  | .error _ => none

-- Test 1: Simple assignment
#guard evalAndGet #[.let_ "x" (.nat 42)] "x" == some 42

-- Test 2: Addition
#guard evalAndGet #[.let_ "a" (.nat 7), .let_ "b" (.nat 3),
                    .let_ "c" (.call "add" #[.ident "a", .ident "b"])] "c" == some 10

-- Test 3: Subtraction
#guard evalAndGet #[.let_ "a" (.nat 10), .let_ "b" (.nat 3),
                    .let_ "c" (.call "sub" #[.ident "a", .ident "b"])] "c" == some 7

-- Test 4: If true branch executes
#guard evalAndGet #[.let_ "x" (.nat 1), .let_ "y" (.nat 0),
                    .if_ (.ident "x") #[.assign "y" (.nat 42)]] "y" == some 42

-- Test 5: If false branch skips
#guard evalAndGet #[.let_ "x" (.nat 0), .let_ "y" (.nat 99),
                    .if_ (.ident "x") #[.assign "y" (.nat 42)]] "y" == some 99

-- Test 6: Storage write → read round-trip
#guard (match execBlock 100 (#[.expr (.call "sstore" #[.nat 0, .nat 42]),
                               .let_ "v" (.call "sload" #[.nat 0])] : Array S) mkSt with
       | .ok st' => (VarStore.get? st'.vars "v").map BitVec.toNat == some 42
       | _ => false) == true

-- Test 7: Revert terminates execution
#guard (match execBlock 100 (#[.let_ "x" (.nat 42),
                               .revert #[.nat 0, .nat 0]] : Array S) mkSt with
       | .error (.revert _ _) => true
       | _ => false) == true

-- Test 8: Switch dispatches correctly
#guard evalAndGet #[.let_ "x" (.nat 2), .let_ "y" (.nat 0),
                    .switch_ (.ident "x")
                      #[(.nat 1, #[.assign "y" (.nat 10)]),
                        (.nat 2, #[.assign "y" (.nat 20)])]
                      none] "y" == some 20

-- Test 9: For loop computes sum 0+1+2+3+4 = 10
#guard evalAndGet #[.let_ "i" (.nat 0), .let_ "sum" (.nat 0),
                    .for_ #[]
                      (.call "lt" #[.ident "i", .nat 5])
                      #[.assign "i" (.call "add" #[.ident "i", .nat 1])]
                      #[.assign "sum" (.call "add" #[.ident "sum", .ident "i"])]] "sum" == some 10

-- ==========================================
-- Cross-validation with YulTextMini effect semantics (H9)
-- ==========================================

-- Test 10: Effect ordering parity — both semantics agree on storage writes
-- Validates structural parity, not just existence:
-- (a) effect semantics produces exactly 2 storageWrite effects at correct slots
-- (b) value semantics produces storage state matching the written values
-- (c) both sides agree on operation count and slot ordering
#guard (match parseStmtsFromStringE "sstore(0, 1) sstore(1, 2)" with
       | .ok stmts =>
           let effSt : EffState := { env := default }
           let (_, effs) := evalStmts effSt stmts
           open HeytingLean.BountyHunter.AlgebraIR in
           -- Effect semantics: exactly 2 storage writes at slots 0 and 1
           let effectsOk := effs.size == 2
             && effs[0]! == Effect.storageWrite 0
             && effs[1]! == Effect.storageWrite 1
           -- Value semantics: storage state matches written values
           let valueOk := match execBlock 100 stmts mkSt with
             | .ok st' =>
                 st'.evm.storage.sload (BitVec.ofNat 256 0) == BitVec.ofNat 256 1
                 && st'.evm.storage.sload (BitVec.ofNat 256 1) == BitVec.ofNat 256 2
             | _ => false
           effectsOk && valueOk
       | .error _ => false) == true

-- ==========================================
-- VC discharge integration test
-- ==========================================

-- Test 11: VC discharge for checked_add on concrete inputs
#guard (dischargeVC "add_7_3"
    LeanSP.RealWorld.checkedAddBody
    (mkYulState [("x", BitVec.ofNat 256 7), ("y", BitVec.ofNat 256 3)])
    (fun st => VarStore.get? st.vars "sum" == some (BitVec.ofNat 256 10))
  matches .discharged _) == true

-- Test 12: VC discharge detects revert on overflow
#guard (dischargeVC "add_overflow"
    LeanSP.RealWorld.checkedAddBody
    (mkYulState [("x", Word256.maxVal), ("y", BitVec.ofNat 256 1)])
    (fun _ => true)
  matches .reverted _) == true

end LeanSP.Tests
