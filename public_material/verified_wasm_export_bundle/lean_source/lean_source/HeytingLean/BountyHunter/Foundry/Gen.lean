import Lean
import Lean.Data.Json
import HeytingLean.Util.JCS
import HeytingLean.BountyHunter.AlgebraIR.SlotRef

/-!
# HeytingLean.BountyHunter.Foundry.Gen

Best-effort generation of Foundry files from a CEI witness context:
- a `src/` Solidity file (the original input source),
- a `test/` file that uses Foundry cheatcodes (`vm.store`) via a small local interface
  (no `forge-std` dependency) to force a slot value before calling a target function.

This is a bridging artifact: it is intended to make the witness reproducible by
humans in standard tooling, even before a full CoreEVM replay exists.
-/

namespace HeytingLean.BountyHunter.Foundry

open Lean
open Lean.Json

structure Files where
  version : String := "foundry.files.v1"
  srcPath : String
  testPath : String
  oraclePath : String := "bh_oracle.json"
  src : String
  test : String
  deriving Repr, DecidableEq, Inhabited

def filesToJson (f : Files) : Json :=
  Json.mkObj
    [ ("version", Json.str f.version)
    , ("srcPath", Json.str f.srcPath)
    , ("testPath", Json.str f.testPath)
    , ("oraclePath", Json.str f.oraclePath)
    , ("src", Json.str f.src)
    , ("test", Json.str f.test)
    ]

def filesCanonicalString (f : Files) : String :=
  HeytingLean.Util.JCS.canonicalString (filesToJson f)

private def slotRefToSolidityExpr? (r : HeytingLean.BountyHunter.AlgebraIR.SlotRef) (callerVar : String) (targetVar : String) :
    Option String :=
  let callerExpr := s!"address({callerVar})"
  let rec keyToSolExpr? : HeytingLean.BountyHunter.AlgebraIR.SlotKey → Option String
    | .caller => some callerExpr
    | .this => some s!"address({targetVar})"
    | .nat n => some s!"uint256({n})"
    | .ident _ => none
    | .raw _ => none
  let rec offToUintExpr? : HeytingLean.BountyHunter.AlgebraIR.SlotOffset → Option String
    | .nat n => some s!"uint256({n})"
    | .key _ => none
  let rec slotToBytes32? : HeytingLean.BountyHunter.AlgebraIR.SlotRef → Option String
    | .literal n => some s!"bytes32(uint256({n}))"
    | .mapping base key => do
        let b ← slotToBytes32? base
        let k ← keyToSolExpr? key
        pure s!"keccak256(abi.encode({k}, uint256({b})))"
    | .keccak base => do
        let b ← slotToBytes32? base
        pure s!"keccak256(abi.encode(uint256({b})))"
    | .add base off => do
        let b ← slotToBytes32? base
        let o ← offToUintExpr? off
        pure s!"bytes32(uint256({b}) + {o})"
    | .packed base _ _ => slotToBytes32? base
    | .raw _ => none
  slotToBytes32? r

private def slotExprToSolidityExpr? (slotExpr : String) (callerVar : String) (targetVar : String) : Option String :=
  match HeytingLean.BountyHunter.AlgebraIR.slotRefParse? slotExpr with
  | none => none
  | some r => slotRefToSolidityExpr? r callerVar targetVar

private def slotExprToStoreLines? (slotExpr : String) (callerVar : String) (targetVar : String) : Option (Array String) :=
  match HeytingLean.BountyHunter.AlgebraIR.slotRefParse? slotExpr with
  | none => none
  | some r =>
      match r with
      | .packed base byteOffset byteSize => do
          let slot ← slotRefToSolidityExpr? base callerVar targetVar
          let shiftBits := byteOffset * 8
          let widthBits := byteSize * 8
          if widthBits = 0 || widthBits ≥ 256 then
            none
          else
            let lines : Array String :=
              #[ s!"    bytes32 __bh_slot = {slot};"
               , s!"    uint256 __bh_prev = uint256(vm.load(address({targetVar}), __bh_slot));"
               , s!"    uint256 __bh_mask = ((uint256(1) << {widthBits}) - 1) << {shiftBits};"
               , s!"    uint256 __bh_next = (__bh_prev & ~__bh_mask) | ((uint256(1) << {shiftBits}) & __bh_mask);"
               , s!"    vm.store(address({targetVar}), __bh_slot, bytes32(__bh_next));"
               ]
            some lines
      | _ => do
          let slot ← slotRefToSolidityExpr? r callerVar targetVar
          some #[s!"    vm.store(address({targetVar}), {slot}, bytes32(uint256(1)));"]

private def mkInitSlotMaskLines (slot : Nat) (slotExpr? : Option String) (callerVar : String) (targetVar : String)
    (slotVar : String) (maskVar : String) :
    String × String :=
  match slotExpr? with
  | none =>
      (s!"    {slotVar} = bytes32(uint256({slot}));", s!"    {maskVar} = type(uint256).max;")
  | some se =>
      match HeytingLean.BountyHunter.AlgebraIR.slotRefParse? se with
      | none => (s!"    revert(\"unsupported slotExpr for slot computation: {se}\");", "")
      | some r =>
          let slotS? := slotRefToSolidityExpr? r callerVar targetVar
          let slotAssign :=
            match slotS? with
            | some sol => s!"    {slotVar} = {sol};"
            | none => s!"    revert(\"unsupported slotExpr for slot computation: {se}\");"
          let maskAssign :=
            match r with
            | .packed _ byteOffset byteSize =>
                let shiftBits := byteOffset * 8
                let widthBits := byteSize * 8
                if widthBits = 0 || widthBits ≥ 256 then
                  s!"    revert(\"unsupported packed slotExpr mask: {se}\");"
                else
                  s!"    {maskVar} = ((uint256(1) << {widthBits}) - 1) << {shiftBits};"
            | _ =>
                s!"    {maskVar} = type(uint256).max;"
          (slotAssign, maskAssign)

private def mkStoreLine (slot : Nat) (slotExpr? : Option String) (callerVar : String) (targetVar : String) : String :=
  match slotExpr? with
  | none =>
      s!"    vm.store(address({targetVar}), bytes32(uint256({slot})), bytes32(uint256(1)));"
  | some se =>
      match slotExprToStoreLines? se callerVar targetVar with
      | none =>
          s!"    revert(\"unsupported slotExpr for vm.store: {se}\");"
      | some lines =>
          String.intercalate "\n" lines.toList

def gen (source : String) (contractName : String) (funcName : String) (slot : Nat)
    (slotExpr? : Option String := none) (callArgs : Array String := #[]) (expectVulnerable? : Option Bool := none)
    (decompiledCreationBytecode? : Option String := none) (algebraIR2CreationBytecode? : Option String := none) : Files :=
  let srcPath := "src/BountyHunterTarget.sol"
  let testPath := "test/BountyHunterReplay.t.sol"
  let callArgsS := String.intercalate ", " callArgs.toList
  let callArgsSuffix := if callArgsS = "" then "" else s!", {callArgsS}"
  let (initSlotLine, initMaskLine) := mkInitSlotMaskLines slot slotExpr? "attacker" "target" "__slot" "__mask"
  let (initSlotLine2, initMaskLine2) := mkInitSlotMaskLines slot slotExpr? "attacker2" "yulTarget" "__slot2" "__mask2"
  let (initSlotLine3, initMaskLine3) := mkInitSlotMaskLines slot slotExpr? "attacker3" "algTarget" "__slot3" "__mask3"
  let slotLine := mkStoreLine slot slotExpr? "attacker" "target"
  let expectationLines : Array String :=
    match expectVulnerable? with
    | none => #[]
    | some true =>
        #[
          "    require(__sawPreWrite, \"expected VULNERABLE ordering (call before write), but slot looked restored\");"
        ]
    | some false =>
        #[
          "    require(!__sawPreWrite, \"expected SAFE ordering (write before call), but slot looked un-restored at boundary\");"
        ]
  let test :=
    String.intercalate "\n"
      [ "// SPDX-License-Identifier: UNLICENSED"
      , "pragma solidity ^0.8.20;"
      , ""
      , "import \"../src/BountyHunterTarget.sol\";"
      , ""
      , "interface Vm {"
      , "  function store(address target, bytes32 slot, bytes32 value) external;"
      , "  function load(address target, bytes32 slot) external returns (bytes32);"
      , "  function deal(address who, uint256 newBalance) external;"
      , "  function writeFile(string calldata path, string calldata data) external;"
      , "  function toString(bytes calldata value) external returns (string memory);"
      , "  function toString(bytes32 value) external returns (string memory);"
      , "}"
      , ""
      , "contract BountyHunterAttacker {"
      , "  address constant HEVM_ADDRESS = address(uint160(uint256(keccak256(\"hevm cheat code\"))));"
      , "  Vm constant vm = Vm(HEVM_ADDRESS);"
      , "  bytes32 constant FLAG_SLOT = bytes32(uint256(0xB0B));"
      , ""
      , s!"  {contractName} public target;"
      , "  bytes32 public slot;"
      , "  uint256 public mask;"
      , "  bool public lastOk;"
      , "  bytes public lastRet;"
      , "  bool private initialized;"
      , ""
      , s!"  function init({contractName} _target, bytes32 _slot, uint256 _mask) external " ++ "{"
      , "    require(!initialized, \"already initialized\");"
      , "    target = _target;"
      , "    slot = _slot;"
      , "    mask = _mask;"
      , "    initialized = true;"
      , "  }"
      , ""
      , "  function attack() external {"
      , "    // Use a low-level call so we can capture return data deterministically for oracle output."
      , s!"    (lastOk, lastRet) = address(target).call(abi.encodeWithSelector(target.{funcName}.selector{callArgsSuffix}));"
      , "    require(lastOk, \"attack call failed\");"
      , "  }"
      , ""
      , "  receive() external payable {"
      , "    // Witness-level check: at the boundary, was the selected slot already restored?"
      , "    bytes32 v = vm.load(address(target), slot);"
      , "    if ((uint256(v) & mask) != 0) {"
      , "      // Use cheatcode storage writes to avoid gas-stipend failures (e.g. `.send`/`.transfer`)."
      , "      vm.store(address(this), FLAG_SLOT, bytes32(uint256(1)));"
      , "    }"
      , "  }"
      , "}"
      , ""
      , "contract BountyHunterReplayTest {"
      , "  address constant HEVM_ADDRESS = address(uint160(uint256(keccak256(\"hevm cheat code\"))));"
      , "  Vm constant vm = Vm(HEVM_ADDRESS);"
      , ""
      , "  function _boolJson(bool b) internal pure returns (string memory) {"
      , "    return b ? \"true\" : \"false\";"
      , "  }"
      , ""
      , "  function _emitOracle(bool ok, bytes memory ret, bytes32 slot, bytes32 val, bool same) internal {"
      , "    string memory j = string(abi.encodePacked("
      , "      \"{\\\"ok\\\":\", _boolJson(ok),"
      , "      \",\\\"returnData\\\":\\\"\", vm.toString(ret), \"\\\",\","
      , "      \"\\\"slot\\\":\\\"\", vm.toString(slot), \"\\\",\","
      , "      \"\\\"value\\\":\\\"\", vm.toString(val), \"\\\",\","
      , "      \"\\\"same\\\":\", _boolJson(same),"
      , "      \"}\""
      , "    ));"
      , "    vm.writeFile(\"bh_oracle.json\", j);"
      , "  }"
      , ""
      , (s!"  function test_CEISlot{slot}_ViaBountyHunterWitness() public " ++ "{")
      , s!"    {contractName} target = new {contractName}();"
      , "    BountyHunterAttacker attacker = new BountyHunterAttacker();"
      , "    // Provide balances so value transfers do not spuriously revert."
      , "    vm.deal(address(attacker), 10 ether);"
      , "    vm.deal(address(target), 10 ether);"
      , "    // Force the storage slot so the interesting branch executes."
      , "    bytes32 __slot = bytes32(0);"
      , "    uint256 __mask = type(uint256).max;"
      , "    // Compute slotExpr relative to `address(attacker)` (the caller during replay)."
      , initSlotLine
      , initMaskLine
      , "    attacker.init(target, __slot, __mask);"
      , "    // Clear the attacker-side witness flag."
      , "    vm.store(address(attacker), bytes32(uint256(0xB0B)), bytes32(uint256(0)));"
      , slotLine
      , "    attacker.attack();"
      , "    bool __sawPreWrite = (uint256(vm.load(address(attacker), bytes32(uint256(0xB0B)))) != 0);"
      , String.intercalate "\n" expectationLines.toList
      , "    // Semantics oracle: return bytes + final storage snapshot for the selected slot."
      , "    bool __ok = attacker.lastOk();"
      , "    bytes32 __val = vm.load(address(target), __slot);"
      , "    bool __same = true;"
      , "    // Optional decompiler checks: deploy alternative bytecodes and compare oracle outputs."
      , (match decompiledCreationBytecode? with
        | none => "    // (decompiler disabled)"
        | some hex =>
            String.intercalate "\n"
              [ s!"    bytes memory __yulCreation = hex\"{hex}\";"
              , "    address __yulAddr;"
              , "    assembly { __yulAddr := create(0, add(__yulCreation, 0x20), mload(__yulCreation)) }"
              , "    require(__yulAddr != address(0), \"yul deploy failed\");"
              , s!"    {contractName} yulTarget = {contractName}(payable(__yulAddr));"
              , "    BountyHunterAttacker attacker2 = new BountyHunterAttacker();"
              , "    vm.deal(address(attacker2), 10 ether);"
              , "    vm.deal(address(yulTarget), 10 ether);"
              , "    bytes32 __slot2 = bytes32(0);"
              , "    uint256 __mask2 = type(uint256).max;"
              , "    // Compute slotExpr relative to `address(attacker2)` (the caller during replay)."
              , initSlotLine2
              , initMaskLine2
              , "    attacker2.init(yulTarget, __slot2, __mask2);"
              , "    vm.store(address(attacker2), bytes32(uint256(0xB0B)), bytes32(uint256(0)));"
              , mkStoreLine slot slotExpr? "attacker2" "yulTarget"
              , "    attacker2.attack();"
              , "    bool __ok2 = attacker2.lastOk();"
              , "    bytes32 __val2 = vm.load(address(yulTarget), __slot2);"
              , "    __same = __same && (__ok == __ok2) && (keccak256(attacker.lastRet()) == keccak256(attacker2.lastRet())) && (__val == __val2);"
              , "    // The CEI witness flag should behave the same under decompiled execution."
              , "    bool __sawPreWrite2 = (uint256(vm.load(address(attacker2), bytes32(uint256(0xB0B)))) != 0);"
              , "    __same = __same && (__sawPreWrite == __sawPreWrite2);"
              ])
      , (match algebraIR2CreationBytecode? with
        | none => "    // (algebraIR2 decompiler disabled)"
        | some hex =>
            String.intercalate "\n"
              [ s!"    bytes memory __algCreation = hex\"{hex}\";"
              , "    address __algAddr;"
              , "    assembly { __algAddr := create(0, add(__algCreation, 0x20), mload(__algCreation)) }"
              , "    require(__algAddr != address(0), \"algebrair2 yul deploy failed\");"
              , s!"    {contractName} algTarget = {contractName}(payable(__algAddr));"
              , "    BountyHunterAttacker attacker3 = new BountyHunterAttacker();"
              , "    vm.deal(address(attacker3), 10 ether);"
              , "    vm.deal(address(algTarget), 10 ether);"
              , "    bytes32 __slot3 = bytes32(0);"
              , "    uint256 __mask3 = type(uint256).max;"
              , "    // Compute slotExpr relative to `address(attacker3)` (the caller during replay)."
              , initSlotLine3
              , initMaskLine3
              , "    attacker3.init(algTarget, __slot3, __mask3);"
              , "    vm.store(address(attacker3), bytes32(uint256(0xB0B)), bytes32(uint256(0)));"
              , mkStoreLine slot slotExpr? "attacker3" "algTarget"
              , "    attacker3.attack();"
              , "    bool __ok3 = attacker3.lastOk();"
              , "    bytes32 __val3 = vm.load(address(algTarget), __slot3);"
              , "    __same = __same && (__ok == __ok3) && (keccak256(attacker.lastRet()) == keccak256(attacker3.lastRet())) && (__val == __val3);"
              , "    bool __sawPreWrite3 = (uint256(vm.load(address(attacker3), bytes32(uint256(0xB0B)))) != 0);"
              , "    __same = __same && (__sawPreWrite == __sawPreWrite3);"
              ])
      , "    _emitOracle(__ok, attacker.lastRet(), __slot, __val, __same);"
      , "    require(__same, \"decompiler oracle mismatch\");"
      , "  }"
      , "}"
      ]
  { srcPath := srcPath
    testPath := testPath
    oraclePath := "bh_oracle.json"
    src := source
    test := test
  }

end HeytingLean.BountyHunter.Foundry
