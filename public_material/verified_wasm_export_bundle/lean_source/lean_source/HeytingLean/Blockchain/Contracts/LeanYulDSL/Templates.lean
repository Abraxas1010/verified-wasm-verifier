import Std
import HeytingLean.Blockchain.Contracts.LeanYulDSL.Emit

/-!
# HeytingLean.Blockchain.Contracts.LeanYulDSL.Templates

Concrete, Lean-authored contract templates in the Lean→(Yul object / Solidity inline-Yul) lane.

These are currently **string templates** (Yul source), but they are kept as structured
`YulParts` so:
- the Solidity wrapper emission does not need to parse Yul object text, and
- downstream tools can attach certificates/hashes cleanly.
-/

namespace HeytingLean.Blockchain.Contracts.LeanYulDSL

open HeytingLean.Blockchain.Contracts.LeanYulDSL

private def lines (xs : List String) : String :=
  String.intercalate "\n" xs

def ownerParts : YulParts :=
  let initBare :=
    lines
      [
        "sstore(0, caller())",
      ]
  let runtime :=
    lines
      [
        "mstore(0, sload(0))",
        "return(0, 32)",
      ]
  { objectName := "Owner", initBare := initBare, runtime := runtime }

def bankParts (allowReceive : Bool := true) : YulParts :=
  let receiveBlock : List String :=
    if allowReceive then
      [
        "// receive() / deposit()",
        "if iszero(calldatasize()) {",
        "  deposit()",
        "  return(0, 0)",
        "}",
        "",
      ]
    else
      []
  let runtimeLines : List String :=
    [
      "function selector() -> s {",
      "  s := shr(224, calldataload(0))",
      "}",
      "",
      "function addr_at(pos) -> a {",
      "  a := and(calldataload(pos), 0xffffffffffffffffffffffffffffffffffffffff)",
      "}",
      "",
      "function u256_at(pos) -> v {",
      "  v := calldataload(pos)",
      "}",
      "",
      "function balance_slot(owner) -> slot {",
      "  mstore(0, owner)",
      "  mstore(32, 0)",
      "  slot := keccak256(0, 64)",
      "}",
      "",
      "function deposit() {",
      "  let owner := caller()",
      "  let v := callvalue()",
      "  let slot := balance_slot(owner)",
      "  let b := sload(slot)",
      "  sstore(slot, add(b, v))",
      "}",
      "",
      "function withdraw(amount) {",
      "  let owner := caller()",
      "  let slot := balance_slot(owner)",
      "  let b := sload(slot)",
      "  if lt(b, amount) { revert(0, 0) }",
      "  // CEI: update before the external call",
      "  sstore(slot, sub(b, amount))",
      "  if iszero(call(gas(), owner, amount, 0, 0, 0, 0)) { revert(0, 0) }",
      "}",
      "",
      "function ret_u256(x) {",
      "  mstore(0, x)",
      "  return(0, 32)",
      "}",
      "",
    ]
    ++ receiveBlock ++
    [
      "switch selector()",
      "case 0xd0e30db0 {",
      "  deposit()",
      "  return(0, 0)",
      "}",
      "case 0x70a08231 {",
      "  let a := addr_at(4)",
      "  let slot := balance_slot(a)",
      "  ret_u256(sload(slot))",
      "}",
      "case 0x2e1a7d4d {",
      "  let amt := u256_at(4)",
      "  withdraw(amt)",
      "  return(0, 0)",
      "}",
      "default {",
      "  revert(0, 0)",
      "}",
    ]
  { objectName := "Bank", initBare := "", runtime := lines runtimeLines }

def erc20MiniParts (totalSupply : Nat := 1000000) : YulParts :=
  let initBare :=
    lines
      [
        s!"let supply := {totalSupply}",
        "sstore(0, supply)",
        "function balance_slot(owner) -> slot {",
        "  mstore(0, owner)",
        "  mstore(32, 1)",
        "  slot := keccak256(0, 64)",
        "}",
        "function allowance_slot(owner, spender) -> slot {",
        "  // allowances[owner][spender] with base slot 2",
        "  mstore(0, owner)",
        "  mstore(32, 2)",
        "  let inner := keccak256(0, 64)",
        "  mstore(0, spender)",
        "  mstore(32, inner)",
        "  slot := keccak256(0, 64)",
        "}",
        "sstore(balance_slot(caller()), supply)",
      ]
  let runtime :=
    lines
      [
        "function selector() -> s {",
        "  s := shr(224, calldataload(0))",
        "}",
        "",
        "function addr_at(pos) -> a {",
        "  a := and(calldataload(pos), 0xffffffffffffffffffffffffffffffffffffffff)",
        "}",
        "",
        "function u256_at(pos) -> v {",
        "  v := calldataload(pos)",
        "}",
        "",
        "function balance_slot(owner) -> slot {",
        "  mstore(0, owner)",
        "  mstore(32, 1)",
        "  slot := keccak256(0, 64)",
        "}",
        "",
        "function allowance_slot(owner, spender) -> slot {",
        "  // allowances[owner][spender] with base slot 2",
        "  mstore(0, owner)",
        "  mstore(32, 2)",
        "  let inner := keccak256(0, 64)",
        "  mstore(0, spender)",
        "  mstore(32, inner)",
        "  slot := keccak256(0, 64)",
        "}",
        "",
        "function ret_u256(x) {",
        "  mstore(0, x)",
        "  return(0, 32)",
        "}",
        "",
        "function ret_bool(b) {",
        "  mstore(0, b)",
        "  return(0, 32)",
        "}",
        "",
        "function transfer(to, amount) {",
        "  let from := caller()",
        "  let slotFrom := balance_slot(from)",
        "  let b := sload(slotFrom)",
        "  if lt(b, amount) { revert(0, 0) }",
        "  sstore(slotFrom, sub(b, amount))",
        "  let slotTo := balance_slot(to)",
        "  sstore(slotTo, add(sload(slotTo), amount))",
        "  ret_bool(1)",
        "}",
        "",
        "function approve(spender, amount) {",
        "  let owner := caller()",
        "  let slot := allowance_slot(owner, spender)",
        "  sstore(slot, amount)",
        "  ret_bool(1)",
        "}",
        "",
        "function transferFrom(from, to, amount) {",
        "  let spender := caller()",
        "  let slotAllow := allowance_slot(from, spender)",
        "  let allow := sload(slotAllow)",
        "  if lt(allow, amount) { revert(0, 0) }",
        "  sstore(slotAllow, sub(allow, amount))",
        "  let slotFrom := balance_slot(from)",
        "  let b := sload(slotFrom)",
        "  if lt(b, amount) { revert(0, 0) }",
        "  sstore(slotFrom, sub(b, amount))",
        "  let slotTo := balance_slot(to)",
        "  sstore(slotTo, add(sload(slotTo), amount))",
        "  ret_bool(1)",
        "}",
        "",
        "switch selector()",
        "case 0x18160ddd {",
        "  ret_u256(sload(0))",
        "}",
        "case 0x70a08231 {",
        "  let a := addr_at(4)",
        "  let slot := balance_slot(a)",
        "  ret_u256(sload(slot))",
        "}",
        "case 0xa9059cbb {",
        "  let to := addr_at(4)",
        "  let amt := u256_at(36)",
        "  transfer(to, amt)",
        "}",
        "case 0xdd62ed3e {",
        "  let owner := addr_at(4)",
        "  let spender := addr_at(36)",
        "  let slot := allowance_slot(owner, spender)",
        "  ret_u256(sload(slot))",
        "}",
        "case 0x095ea7b3 {",
        "  let spender := addr_at(4)",
        "  let amt := u256_at(36)",
        "  approve(spender, amt)",
        "}",
        "case 0x23b872dd {",
        "  let from := addr_at(4)",
        "  let to := addr_at(36)",
        "  let amt := u256_at(68)",
        "  transferFrom(from, to, amt)",
        "}",
        "default {",
        "  revert(0, 0)",
        "}",
      ]
  { objectName := "ERC20Mini", initBare := initBare, runtime := runtime }

end HeytingLean.Blockchain.Contracts.LeanYulDSL
