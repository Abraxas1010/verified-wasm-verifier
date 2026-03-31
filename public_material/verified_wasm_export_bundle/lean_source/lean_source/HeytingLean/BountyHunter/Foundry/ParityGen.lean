import Lean
import Lean.Data.Json
import Std
import HeytingLean.Util.JCS

/-!
# HeytingLean.BountyHunter.Foundry.ParityGen

Generate a Foundry project that performs **differential semantic checks** between:
- the original Solidity contract, and
- a **decompiled Solidity artifact** whose runtime bytecode is embedded.

Oracle checks (per ABI-visible entry; functions + fallback/receive):
- ok/revert parity
- return bytes parity
- event/log parity (topics + data; emitter ignored)
- storage parity over a finite domain:
  - all static slots from `storageLayout` (when provided)
  - plus all slots observed via `vm.record()`/`vm.accesses()`

This is executable-first and intentionally conservative: callers should refuse
to generate this harness if ABI features are unsupported (so we don't silently
skip functions). Overloads are supported via full signatures.
-/

namespace HeytingLean.BountyHunter.Foundry.Parity

open Lean
open Lean.Json

structure Files where
  version : String := "foundry.files.v1"
  srcPath : String
  testPath : String
  oraclePath : String := "bh_parity_oracle.json"
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

structure AbiFn where
  kind : String := "function"
  signature : String
  inputs : Array Json := #[]
  deriving Inhabited

def decompiledContractSource (creationHex : String) : String :=
  String.intercalate "\n"
    [ ""
    , "contract __BHInitCodeHolder {"
    , "  constructor(bytes memory code) {"
    , "    assembly {"
    , "      return(add(code, 0x20), mload(code))"
    , "    }"
    , "  }"
    , "}"
    , ""
    , "contract BountyHunterDecompiled {"
    , "  constructor(bytes memory __ctorData) {"
    , s!"    bytes memory __init = bytes.concat(hex\"{creationHex}\", __ctorData);"
    , "    __BHInitCodeHolder h = new __BHInitCodeHolder(__init);"
    , "    (bool ok, bytes memory runtime) = address(h).delegatecall(\"\");"
    , "    require(ok, \"init delegatecall failed\");"
    , "    assembly { return(add(runtime, 0x20), mload(runtime)) }"
    , "  }"
    , "}"
    , ""
    ]

inductive AbiBaseKind where
  | uint (bits : Nat)
  | int (bits : Nat)
  | bool
  | address
  | bytesDyn
  | bytesFixed (n : Nat)
  | string
  deriving Repr, DecidableEq

inductive AbiTy where
  | base (b : AbiBaseKind)
  | tuple (components : Array AbiTy)
  | array (elem : AbiTy) (len : Option Nat)
  deriving Repr

instance : Inhabited AbiTy := ⟨.base (.uint 256)⟩

private def parseBits? (s : String) : Option Nat :=
  if s = "" then some 256 else s.toNat?

private def parseDimsE (rest : List String) : Except String (List (Option Nat)) := do
  rest.foldlM (init := ([] : List (Option Nat))) (fun dims p => do
    if !p.endsWith "]" then
      throw s!"malformed ABI type suffix: [{p}"
    let inner := p.dropRight 1
    if inner = "" then
      return dims.concat (none : Option Nat)
    match inner.toNat? with
    | some n => return dims.concat (some n)
    | none => throw s!"malformed ABI array dimension: '{inner}'")

private def parseTypeStringE (ty : String) : Except String (String × List (Option Nat)) := do
  let parts := ty.splitOn "["
  match parts with
  | [] => throw "empty ABI type"
  | baseS :: rest =>
      let dims ← parseDimsE rest
      return (baseS, dims)

private def baseKindFromStringE (baseS : String) : Except String AbiBaseKind := do
  if baseS.startsWith "uint" then
    match parseBits? (baseS.drop 4) with
    | some bits => return .uint bits
    | none => throw s!"unsupported uint bits: {baseS}"
  else if baseS.startsWith "int" then
    match parseBits? (baseS.drop 3) with
    | some bits => return .int bits
    | none => throw s!"unsupported int bits: {baseS}"
  else if baseS = "bool" then
    return .bool
  else if baseS = "address" then
    return .address
  else if baseS = "bytes" then
    return .bytesDyn
  else if baseS.startsWith "bytes" then
    match (baseS.drop 5).toNat? with
    | some n =>
        if n = 0 || n > 32 then
          throw s!"unsupported bytesN width: {baseS}"
        else
          return .bytesFixed n
    | none => throw s!"unsupported bytesN: {baseS}"
  else if baseS = "string" then
    return .string
  else
    throw s!"unsupported ABI base type: {baseS}"

private def jsonObjGet? (j : Json) (k : String) : Option Json :=
  match j with
  | .obj kvs => kvs.get? k
  | _ => none

private def jsonArr? (j : Json) : Option (Array Json) :=
  match j with
  | .arr xs => some xs
  | _ => none

private def jsonStr? (j : Json) : Option String :=
  match j with
  | .str s => some s
  | _ => none

partial def abiTyFromAbiParamJsonE (param : Json) : Except String AbiTy := do
  let tyStr ←
    match jsonObjGet? param "type" >>= jsonStr? with
    | some s => pure s
    | none => throw "abi param: missing string field 'type'"
  let (baseS, dims) ← parseTypeStringE tyStr
  let baseTy : AbiTy ←
    if baseS = "tuple" then
      match jsonObjGet? param "components" >>= jsonArr? with
      | none => throw "abi param: tuple missing components"
      | some compsJ =>
          let comps ← compsJ.mapM (fun c => abiTyFromAbiParamJsonE c)
          return .tuple comps
    else
      return .base (← baseKindFromStringE baseS)
  return dims.foldl (fun t d => AbiTy.array t d) baseTy

partial def canonicalTypeString : AbiTy → String
  | .base b =>
      match b with
      | .uint bits => if bits = 256 then "uint256" else s!"uint{bits}"
      | .int bits => if bits = 256 then "int256" else s!"int{bits}"
      | .bool => "bool"
      | .address => "address"
      | .bytesDyn => "bytes"
      | .bytesFixed n => s!"bytes{n}"
      | .string => "string"
  | .tuple cs =>
      "(" ++ String.intercalate "," (cs.toList.map canonicalTypeString) ++ ")"
  | .array t none =>
      canonicalTypeString t ++ "[]"
  | .array t (some n) =>
      canonicalTypeString t ++ s!"[{n}]"

def validateAbiTyE (t : AbiTy) : Except String Unit := do
  let maxFixed := 8
  let rec validate (depth : Nat) (t : AbiTy) : Except String Unit := do
    if depth > 10 then
      throw "ABI type nesting too deep"
    match t with
    | .base (.uint bits) =>
        if bits = 0 || bits > 256 || bits % 8 != 0 then throw s!"unsupported uint bits: {bits}" else pure ()
    | .base (.int bits) =>
        if bits = 0 || bits > 256 || bits % 8 != 0 then throw s!"unsupported int bits: {bits}" else pure ()
    | .base (.bytesFixed n) =>
        if n = 0 || n > 32 then throw s!"unsupported bytesN width: {n}" else pure ()
    | .base _ => pure ()
    | .tuple cs =>
        for c in cs do
          validate (depth + 1) c
    | .array elem (some n) =>
        if n > maxFixed then throw s!"unsupported fixed array length {n} (> {maxFixed})" else
        validate (depth + 1) elem
    | .array elem none =>
        validate (depth + 1) elem
  validate 0 t

def validateAbiParamE (param : Json) : Except String Unit := do
  validateAbiTyE (← abiTyFromAbiParamJsonE param)

private def baseSolTy (b : AbiBaseKind) : String :=
  match b with
  | .uint bits => if bits = 256 then "uint256" else s!"uint{bits}"
  | .int bits => if bits = 256 then "int256" else s!"int{bits}"
  | .bool => "bool"
  | .address => "address"
  | .bytesDyn => "bytes"
  | .bytesFixed n => s!"bytes{n}"
  | .string => "string"

private def mkScalarExpr (b : AbiBaseKind) (seedVar : String) : String :=
  match b with
  | .uint bits =>
      let ty := baseSolTy (.uint bits)
      s!"{ty}(uint256({seedVar}))"
  | .int bits =>
      let ty := baseSolTy (.int bits)
      s!"{ty}(int256(uint256({seedVar})))"
  | .bool =>
      s!"((uint256({seedVar}) & 1) == 1)"
  | .address =>
      s!"address(uint160(uint256({seedVar})))"
  | .bytesFixed n =>
      s!"bytes{n}({seedVar})"
  | .bytesDyn =>
      s!"_genBytes({seedVar}, __BH_MAX_BYTES_LEN)"
  | .string =>
      s!"_genString({seedVar}, __BH_MAX_STRING_LEN)"

private def collectTuples (t : AbiTy) (acc : Std.HashMap String (Array AbiTy)) : Std.HashMap String (Array AbiTy) :=
  match t with
  | .tuple cs =>
      let k := canonicalTypeString t
      let acc :=
        if acc.contains k then acc else acc.insert k cs
      cs.foldl (fun a c => collectTuples c a) acc
  | .array e _ => collectTuples e acc
  | .base _ => acc

private def tupleKeyOrder (m : Std.HashMap String (Array AbiTy)) : Array String :=
  let ks : Array String := m.toList.toArray.map (fun (k, _) => k)
  ks.qsort (fun a b => if a.length = b.length then a < b else a.length < b.length)

private def mkTupleNameMap (m : Std.HashMap String (Array AbiTy)) : Std.HashMap String String :=
  Id.run do
    let ks := tupleKeyOrder m
    let mut out : Std.HashMap String String := Std.HashMap.emptyWithCapacity (ks.size + 4)
    for i in [0:ks.size] do
      out := out.insert ks[i]! s!"BH_Tuple{i}"
    out

private def solTyString (t : AbiTy) (names : Std.HashMap String String) : Except String String := do
  match t with
  | .base b => return baseSolTy b
  | .tuple _ =>
      let k := canonicalTypeString t
      match names.get? k with
      | some n => return n
      | none => throw s!"internal: missing tuple name for {k}"
  | .array e none =>
      return (← solTyString e names) ++ "[]"
  | .array e (some n) =>
      return (← solTyString e names) ++ s!"[{n}]"

partial def mkValueE (t : AbiTy) (names : Std.HashMap String String) (seedVar : String) (varName : String) :
    Except String (Array String × String) := do
  match t with
  | .base b =>
      return (#[], mkScalarExpr b seedVar)
  | .tuple cs =>
      let k := canonicalTypeString t
      let structName :=
        match names.get? k with
        | some n => n
        | none => "__BH_MISSING_TUPLE"
      let mut lines : Array String := #[s!"{structName} memory {varName};"]
      for i in [0:cs.size] do
        let c := cs[i]!
        let sVar := s!"{varName}__s{i}"
        lines := lines.push s!"bytes32 {sVar} = keccak256(abi.encodePacked({seedVar}, uint256({i})));"
        let (ls, expr) ← mkValueE c names sVar s!"{varName}__v{i}"
        lines := lines ++ ls
        lines := lines.push s!"{varName}.f{i} = {expr};"
      return (lines, varName)
  | .array e (some n) =>
      let elemTy ← solTyString e names
      let mut lines : Array String := #[s!"{elemTy}[{n}] memory {varName};"]
      lines := lines.push ("for (uint256 __i = 0; __i < " ++ toString n ++ "; __i++) {")
      lines := lines.push s!"  bytes32 __s = keccak256(abi.encodePacked({seedVar}, __i));"
      let (ls, expr) ← mkValueE e names "__s" s!"{varName}__elem"
      lines := lines ++ (ls.map (fun l => "  " ++ l))
      lines := lines.push s!"  {varName}[__i] = {expr};"
      lines := lines.push "}"
      return (lines, varName)
  | .array e none =>
      let elemTy ← solTyString e names
      let lenVar := varName ++ "__len"
      let mut lines : Array String :=
        #[ s!"uint256 {lenVar} = uint256({seedVar}) % (__BH_MAX_ARR_LEN + 1);"
         , s!"{elemTy}[] memory {varName} = new {elemTy}[]({lenVar});"
         , "for (uint256 __i = 0; __i < " ++ lenVar ++ "; __i++) {"
         , s!"  bytes32 __s = keccak256(abi.encodePacked({seedVar}, __i));"
         ]
      let (ls, expr) ← mkValueE e names "__s" s!"{varName}__elem"
      lines := lines ++ (ls.map (fun l => "  " ++ l))
      lines := lines.push s!"  {varName}[__i] = {expr};"
      lines := lines.push "}"
      return (lines, varName)

private def indent (n : Nat) (s : String) : String :=
  String.mk (List.replicate n ' ') ++ s

private def indentLines (n : Nat) (xs : Array String) : Array String :=
  xs.map (indent n)

private def mkCallFromSeedBlockE (fn : AbiFn) (names : Std.HashMap String String) (seedVar : String) :
    Except String (Array String × String) := do
  let mut setup : Array String := #[]
  let mut argExprs : Array String := #[]
  for i in [0:fn.inputs.size] do
    let inp := fn.inputs[i]!
    let ty ← abiTyFromAbiParamJsonE inp
    validateAbiTyE ty
    let sVar := s!"__s{i}"
    setup := setup.push s!"bytes32 {sVar} = keccak256(abi.encodePacked({seedVar}, uint256({i})));"
    let (ls, expr) ← mkValueE ty names sVar (s!"__a{i}")
    setup := setup ++ ls
    argExprs := argExprs.push expr
  let argsSfx :=
    let s := String.intercalate ", " argExprs.toList
    if s = "" then "" else s!", {s}"
  let mkData :=
    if fn.kind = "function" then
      s!"bytes memory __data = abi.encodeWithSignature(\"{fn.signature}\"{argsSfx});"
    else if fn.kind = "receive" then
      "bytes memory __data = \"\";"
    else
      "bytes memory __data = hex\"DEADBEEF\";"
  return (setup, mkData)

private def mkCheckCallLines (dataLine : String) (valueExpr : String := "0") : Array String :=
  #[
    dataLine
  , "vm.recordLogs();"
  , "vm.record();"
  , s!"caller.invokeValue(orig, __data, {valueExpr});"
  , "bool ok1 = caller.lastOk();"
  , "bytes memory ret1 = caller.lastRet();"
  , "Vm.Log[] memory logs1 = vm.getRecordedLogs();"
  , "(bytes32[] memory reads1, bytes32[] memory writes1) = vm.accesses(orig);"
  , "vm.recordLogs();"
  , "vm.record();"
  , s!"caller.invokeValue(dec, __data, {valueExpr});"
  , "bool ok2 = caller.lastOk();"
  , "bytes memory ret2 = caller.lastRet();"
  , "Vm.Log[] memory logs2 = vm.getRecordedLogs();"
  , "(bytes32[] memory reads2, bytes32[] memory writes2) = vm.accesses(dec);"
  , "require(ok1 == ok2, \"parity: ok mismatch\");"
  , "require(keccak256(ret1) == keccak256(ret2), \"parity: return mismatch\");"
  , "require(_logsHash(logs1) == _logsHash(logs2), \"parity: logs mismatch\");"
  , "bytes32[] memory rw = _uniq(_uniq(reads1, writes1), _uniq(reads2, writes2));"
  , "bytes32[] memory slots = _uniq(staticSlots, rw);"
  , "require(_storageEqAddrInvariant(orig, dec, slots, __bh_thisMapBases), \"parity: storage mismatch\");"
  ]

private def mkFnCheckBlock (names : Std.HashMap String String) (fn : AbiFn) : String :=
  let header :=
    if fn.kind = "function" then s!"    // {fn.signature}" else s!"    // {fn.kind}"
  let (setup0, dataLine0) :=
    match mkCallFromSeedBlockE fn names "__seed" with
    | .ok p => p
    | .error e => (#["revert(\"" ++ e ++ "\");"], "bytes memory __data = \"\";")
  let valueExpr := if fn.kind = "receive" then "1" else "0"
  let bodyLines :=
    indentLines 8 setup0 ++ indentLines 8 (mkCheckCallLines dataLine0 valueExpr)
  String.intercalate "\n"
    ([ header
     , "    {"
     , "      // Sweep cases (deterministic)."
     , "      for (uint256 __k = 0; __k < __bh_sweepSeeds.length; __k++) {"
     , s!"        bytes32 __seed = keccak256(abi.encodePacked(__bh_sweepSeeds[__k], \"{fn.kind}\", \"{fn.signature}\"));"
     ]
     ++ bodyLines.toList
     ++ [ "      }"
        , "      // Pseudofuzz cases (deterministic)."
        , "      for (uint256 __k = 0; __k < __BH_FUZZ_RUNS; __k++) {"
        , s!"        bytes32 __seed = keccak256(abi.encodePacked(bytes32(uint256(__k)), \"{fn.kind}\", \"{fn.signature}\"));"
        ]
     ++ bodyLines.toList
     ++ [ "      }"
        , "    }"
        ])

private def staticSlotsInitLines (staticSlots : Array Nat) : Array String :=
  Id.run do
    let n := staticSlots.size
    let mut lines : Array String := #[s!"    bytes32[] memory staticSlots = new bytes32[]({n});"]
    for i in [0:n] do
      let slot := staticSlots[i]!
      lines := lines.push s!"    staticSlots[{i}] = bytes32(uint256({slot}));"
    return lines

private def mappingBasesInitLines (mappingBases : Array Nat) : Array String :=
  Id.run do
    let n := mappingBases.size
    let mut lines : Array String := #[s!"    bytes32[] memory __bh_thisMapBases = new bytes32[]({n});"]
    for i in [0:n] do
      let slot := mappingBases[i]!
      lines := lines.push s!"    __bh_thisMapBases[{i}] = bytes32(uint256({slot}));"
    return lines

private def structDefLines (tupleDefs : Std.HashMap String (Array AbiTy)) (names : Std.HashMap String String) : Array String :=
  Id.run do
    let ks := tupleKeyOrder tupleDefs
    let mut lines : Array String := #[]
    for k in ks do
      match tupleDefs.get? k, names.get? k with
      | some cs, some nm =>
          lines := lines.push ("  struct " ++ nm ++ " {")
          for i in [0:cs.size] do
            let c := cs[i]!
            let ty :=
              match solTyString c names with
              | .ok s => s
              | .error _ => "uint256"
            lines := lines.push s!"    {ty} f{i};"
          lines := lines.push "  }"
          lines := lines.push ""
      | _, _ => pure ()
    lines

def gen (source : String) (contractName : String) (abiFns : Array AbiFn) (staticSlots : Array Nat) (creationHex : String)
    (ctorInputs : Array Json := #[]) (mappingBases : Array Nat := #[]) : Files :=
  let srcPath := "src/BountyHunterTarget.sol"
  let testPath := "test/BountyHunterParity.t.sol"
  let src := source ++ "\n" ++ decompiledContractSource creationHex
  let tupleDefs :=
    Id.run do
      let mut m : Std.HashMap String (Array AbiTy) := Std.HashMap.emptyWithCapacity 32
      for fn in abiFns do
        for inp in fn.inputs do
          match abiTyFromAbiParamJsonE inp with
          | .ok t => m := collectTuples t m
          | .error _ => pure ()
      for inp in ctorInputs do
        match abiTyFromAbiParamJsonE inp with
        | .ok t => m := collectTuples t m
        | .error _ => pure ()
      m
  let tupleNames := mkTupleNameMap tupleDefs
  let tupleStructLines := structDefLines tupleDefs tupleNames
  let fnChecks := String.intercalate "\n\n" (abiFns.toList.map (mkFnCheckBlock tupleNames))
  let staticSlotLines := staticSlotsInitLines staticSlots
  let mappingBaseLines := mappingBasesInitLines mappingBases
  let ctorSetupE : Except String (Array String × String) := do
    let mut setup : Array String := #[]
    let mut args : Array String := #[]
    for i in [0:ctorInputs.size] do
      let inp := ctorInputs[i]!
      let ty ← abiTyFromAbiParamJsonE inp
      validateAbiTyE ty
      let sVar := s!"__cs{i}"
      setup := setup.push s!"bytes32 {sVar} = keccak256(abi.encodePacked(__ctorSeed, uint256({i})));"
      let (ls, expr) ← mkValueE ty tupleNames sVar (s!"__c{i}")
      setup := setup ++ ls
      args := args.push expr
    let argsS := String.intercalate ", " args.toList
    return (setup, argsS)
  let (ctorSetup, ctorArgsS) :=
    match ctorSetupE with
    | .ok p => p
    | .error e => (#["revert(\"" ++ e ++ "\");"], "")
  let test :=
    String.intercalate "\n"
      [ "// SPDX-License-Identifier: UNLICENSED"
      , "pragma solidity ^0.8.20;"
      , ""
      , "import \"../src/BountyHunterTarget.sol\";"
      , ""
      , "interface Vm {"
      , "  // Storage"
      , "  function load(address target, bytes32 slot) external returns (bytes32);"
      , "  function record() external;"
      , "  function accesses(address target) external returns (bytes32[] memory reads, bytes32[] memory writes);"
      , "  // Logs"
      , "  struct Log { bytes32[] topics; bytes data; address emitter; }"
      , "  function recordLogs() external;"
      , "  function getRecordedLogs() external returns (Log[] memory);"
      , "  // Balances"
      , "  function deal(address who, uint256 newBalance) external;"
      , "  // File output"
      , "  function writeFile(string calldata path, string calldata data) external;"
      , "}"
      , ""
      , "contract BountyHunterCaller {"
      , "  bool public lastOk;"
      , "  bytes public lastRet;"
      , "  function invokeValue(address target, bytes memory data, uint256 value) external {"
      , "    (lastOk, lastRet) = target.call{value: value}(data);"
      , "  }"
      , "  receive() external payable {}"
      , "}"
      , ""
      , "contract BountyHunterParityTest {"
      , "  address constant HEVM_ADDRESS = address(uint160(uint256(keccak256(\"hevm cheat code\"))));"
      , "  Vm constant vm = Vm(HEVM_ADDRESS);"
      , "  uint256 constant __BH_MAX_ARR_LEN = 3;"
      , "  uint256 constant __BH_MAX_BYTES_LEN = 32;"
      , "  uint256 constant __BH_MAX_STRING_LEN = 32;"
      , "  uint256 constant __BH_FUZZ_RUNS = 16;"
      , ""
      , String.intercalate "\n" tupleStructLines.toList
      , ""
      , "  function _boolJson(bool b) internal pure returns (string memory) {"
      , "    return b ? \"true\" : \"false\";"
      , "  }"
      , ""
      , "  function _genBytes(bytes32 seed, uint256 maxLen) internal pure returns (bytes memory) {"
      , "    uint256 len = uint256(seed) % (maxLen + 1);"
      , "    bytes memory out = new bytes(len);"
      , "    bytes32 h = keccak256(abi.encodePacked(seed));"
      , "    for (uint256 i = 0; i < len; i++) {"
      , "      out[i] = h[i % 32];"
      , "      if ((i % 32) == 31) h = keccak256(abi.encodePacked(h, i));"
      , "    }"
      , "    return out;"
      , "  }"
      , ""
      , "  function _genString(bytes32 seed, uint256 maxLen) internal pure returns (string memory) {"
      , "    return string(_genBytes(seed, maxLen));"
      , "  }"
      , ""
      , "  function _logsHash(Vm.Log[] memory logs) internal pure returns (bytes32) {"
      , "    bytes32 acc = bytes32(0);"
      , "    for (uint256 i = 0; i < logs.length; i++) {"
      , "      // Ignore emitter address (contracts are deployed at different addresses)."
      , "      bytes32 h = keccak256(abi.encode(logs[i].topics, logs[i].data));"
      , "      acc = keccak256(abi.encodePacked(acc, h));"
      , "    }"
      , "    return acc;"
      , "  }"
      , ""
      , "  function _uniq(bytes32[] memory a, bytes32[] memory b) internal pure returns (bytes32[] memory) {"
      , "    bytes32[] memory tmp = new bytes32[](a.length + b.length);"
      , "    uint256 k = 0;"
      , "    for (uint256 i = 0; i < a.length; i++) tmp[k++] = a[i];"
      , "    for (uint256 i = 0; i < b.length; i++) tmp[k++] = b[i];"
      , "    bytes32[] memory out = new bytes32[](k);"
      , "    uint256 n = 0;"
      , "    for (uint256 i = 0; i < k; i++) {"
      , "      bytes32 x = tmp[i];"
      , "      bool seen = false;"
      , "      for (uint256 j = 0; j < n; j++) {"
      , "        if (out[j] == x) { seen = true; break; }"
      , "      }"
      , "      if (!seen) out[n++] = x;"
      , "    }"
      , "    bytes32[] memory trimmed = new bytes32[](n);"
      , "    for (uint256 i = 0; i < n; i++) trimmed[i] = out[i];"
      , "    return trimmed;"
      , "  }"
      , ""
      , "  function _thisMapSlot(address a, bytes32 baseSlot) internal pure returns (bytes32) {"
      , "    return keccak256(abi.encode(a, uint256(baseSlot)));"
      , "  }"
      , ""
      , "  function _isThisMapSlot(bytes32 s, address orig, address dec, bytes32[] memory bases) internal pure returns (bool) {"
      , "    for (uint256 i = 0; i < bases.length; i++) {"
      , "      bytes32 b = bases[i];"
      , "      if (s == _thisMapSlot(orig, b) || s == _thisMapSlot(dec, b)) return true;"
      , "    }"
      , "    return false;"
      , "  }"
      , ""
      , "  function _storageEqAddrInvariant(address orig, address dec, bytes32[] memory slots, bytes32[] memory thisMapBases) internal returns (bool) {"
      , "    // Compare all slots, except those that look like mapping[address(this)] element slots."
      , "    for (uint256 i = 0; i < slots.length; i++) {"
      , "      bytes32 s = slots[i];"
      , "      if (_isThisMapSlot(s, orig, dec, thisMapBases)) continue;"
      , "      if (vm.load(orig, s) != vm.load(dec, s)) return false;"
      , "    }"
      , "    // Address-invariant mapping check: align mapping[address(this)] across differing contract addresses."
      , "    for (uint256 i = 0; i < thisMapBases.length; i++) {"
      , "      bytes32 b = thisMapBases[i];"
      , "      bytes32 so = _thisMapSlot(orig, b);"
      , "      bytes32 sd = _thisMapSlot(dec, b);"
      , "      if (vm.load(orig, so) != vm.load(dec, sd)) return false;"
      , "    }"
      , "    return true;"
      , "  }"
      , ""
      , "  function _emitOracle(bool ok) internal {"
      , "    string memory j = string(abi.encodePacked(\"{\\\"ok\\\":\", _boolJson(ok), \"}\"));"
      , "    vm.writeFile(\"bh_parity_oracle.json\", j);"
      , "  }"
      , ""
      , "  function test_Parity_AllAbiFunctions() public {"
      , "    BountyHunterCaller caller = new BountyHunterCaller();"
      , "    vm.deal(address(caller), 100 ether);"
      , "    bytes32 __ctorSeed = keccak256(\"bh_ctor\");"
      , String.intercalate "\n" (indentLines 4 ctorSetup).toList
      , s!"    {contractName} __orig = new {contractName}({ctorArgsS});"
      , s!"    BountyHunterDecompiled __dec = new BountyHunterDecompiled(abi.encode({ctorArgsS}));"
      , "    address orig = address(__orig);"
      , "    address dec = address(__dec);"
      , String.intercalate "\n" mappingBaseLines.toList
      , "    bytes32[] memory __bh_sweepSeeds = new bytes32[](4);"
      , "    __bh_sweepSeeds[0] = bytes32(uint256(0));"
      , "    __bh_sweepSeeds[1] = bytes32(uint256(1));"
      , "    __bh_sweepSeeds[2] = bytes32(type(uint256).max);"
      , "    __bh_sweepSeeds[3] = keccak256(\"bh_sweep\");"
      , ""
      , String.intercalate "\n" staticSlotLines.toList
      , ""
      , fnChecks
      , ""
      , "    _emitOracle(true);"
      , "  }"
      , "}"
      ]
  { srcPath := srcPath
    testPath := testPath
    oraclePath := "bh_parity_oracle.json"
    src := src
    test := test
  }

end HeytingLean.BountyHunter.Foundry.Parity
