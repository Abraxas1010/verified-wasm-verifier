import HeytingLean.LeanSP.Lang.EVMState
import HeytingLean.LeanSP.Arith.SignedArith

/-!
# LeanSP.Lang.EVMPrimops

EVM dialect primop dispatch for Yul operational semantics.
Maps primop names (from Yul's EVM dialect) to their implementations
using Word256 arithmetic and EVM state operations.

Reference: https://docs.soliditylang.org/en/latest/yul.html#evm-dialect
-/

namespace LeanSP.EVM

open LeanSP.Arith
open LeanSP.Memory

-- Since we can't compute keccak256, we model it as an opaque function.
-- For verification, we reason about it using the collision-resistance axiom.
opaque keccak256Hash (data : ByteArray) : Word256

/-- The ONE allowed axiom (constraint H1): keccak256 is collision-resistant.
    This is the standard cryptographic assumption underpinning all EVM storage addressing. -/
axiom keccak256_collision_resistant :
  ∀ (data1 data2 : ByteArray),
    data1 ≠ data2 → keccak256Hash data1 ≠ keccak256Hash data2

/-- Evaluate a pure arithmetic primop (no state modification).
    Returns `some values` if the primop is recognized, `none` otherwise. -/
def evalPurePrimop (name : String) (args : List Word256) : Option (List Word256) :=
  match name, args with
  -- Arithmetic
  | "add",        [a, b] => some [add a b]
  | "mul",        [a, b] => some [mul a b]
  | "sub",        [a, b] => some [sub a b]
  | "div",        [a, b] => some [div a b]
  | "mod",        [a, b] => some [mod a b]
  | "addmod",     [a, b, n] => some [addmod a b n]
  | "mulmod",     [a, b, n] => some [mulmod a b n]
  | "exp",        [a, b] => some [exp a b]
  | "signextend", [b, x] => some [signextend b x]
  -- Signed arithmetic
  | "sdiv",       [a, b] => some [sdiv a b]
  | "smod",       [a, b] => some [smod a b]
  -- Comparison
  | "lt",         [a, b] => some [lt a b]
  | "gt",         [a, b] => some [gt a b]
  | "slt",        [a, b] => some [slt a b]
  | "sgt",        [a, b] => some [sgt a b]
  | "eq",         [a, b] => some [eq a b]
  | "iszero",     [a]    => some [isZero a]
  -- Bitwise
  | "and",        [a, b] => some [and a b]
  | "or",         [a, b] => some [or a b]
  | "xor",        [a, b] => some [xor a b]
  | "not",        [a]    => some [not a]
  | "shl",        [s, v] => some [shl s v]
  | "shr",        [s, v] => some [shr s v]
  | "sar",        [s, v] => some [sar s v]
  | "byte",       [i, x] => some [byte_ i x]
  | _, _ => none

/-- Evaluate a state-reading primop (reads state but doesn't modify it). -/
def evalReadPrimop (name : String) (args : List Word256) (st : YulState) :
    Option (List Word256) :=
  match name, args with
  -- Memory
  | "mload",        [off]  =>
      let (val, _) := st.evm.memory.mload off.toNat
      some [val]
  | "msize",        []     => some [st.evm.memory.msize]
  -- Storage
  | "sload",        [key]  => some [st.evm.storage.sload key]
  -- Calldata
  | "calldataload", [off]  => some [calldataLoad st.evm.calldata off.toNat]
  | "calldatasize", []     => some [BitVec.ofNat 256 st.evm.calldata.size]
  | "returndatasize", []   => some [BitVec.ofNat 256 st.evm.returnData.size]
  -- Block context
  | "caller",       []     => some [st.evm.caller]
  | "callvalue",    []     => some [st.evm.callValue]
  | "address",      []     => some [st.evm.address]
  | "selfbalance",  []     => some [st.evm.selfBalance]
  | "number",       []     => some [st.evm.blockNumber]
  | "timestamp",    []     => some [st.evm.timestamp]
  | "chainid",      []     => some [st.evm.chainId]
  | "basefee",      []     => some [st.evm.baseFee]
  | "gasprice",     []     => some [st.evm.gasPrice]
  | "origin",       []     => some [st.evm.origin]
  | "coinbase",     []     => some [st.evm.coinbase]
  | "gaslimit",     []     => some [st.evm.gasLimit]
  | "gas",          []     => some [BitVec.ofNat 256 st.evm.gas]
  | "codesize",     []     => some [Word256.zero]  -- simplified
  | _, _ => none

/-- Evaluate a state-modifying primop.
    Returns the new YulState with modified EVM state. -/
def evalWritePrimop (name : String) (args : List Word256) (st : YulState) :
    Option (List Word256 × YulState) :=
  match name, args with
  -- Memory writes
  | "mstore",   [off, val] =>
      let mem := st.evm.memory.mstore off.toNat val
      some ([], { st with evm := { st.evm with memory := mem } })
  | "mstore8",  [off, val] =>
      let mem := st.evm.memory.mstore8 off.toNat val
      some ([], { st with evm := { st.evm with memory := mem } })
  -- Storage writes
  | "sstore",   [key, val] =>
      let stor := st.evm.storage.sstore key val
      some ([], { st with evm := { st.evm with storage := stor } })
  -- Transient storage (EIP-1153)
  | "tload",    [key] =>
      some ([st.evm.transientStorage.sload key], st)
  | "tstore",   [key, val] =>
      let tstor := st.evm.transientStorage.sstore key val
      some ([], { st with evm := { st.evm with transientStorage := tstor } })
  -- Calldata copy
  | "calldatacopy", [destOff, cdOff, size] =>
      let mem := st.evm.memory.calldatacopy destOff.toNat cdOff.toNat size.toNat st.evm.calldata
      some ([], { st with evm := { st.evm with memory := mem } })
  -- Logging (no-ops for verification — events don't affect execution)
  | "log0", _ => some ([], st)
  | "log1", _ => some ([], st)
  | "log2", _ => some ([], st)
  | "log3", _ => some ([], st)
  | "log4", _ => some ([], st)
  -- External calls (Phase 6 — return 0 = failure for now)
  | "call",         _ => some ([Word256.zero], st)
  | "staticcall",   _ => some ([Word256.zero], st)
  | "delegatecall", _ => some ([Word256.zero], st)
  -- Keccak256
  | "keccak256", [off, len] =>
      let (_, mem) := st.evm.memory.mload off.toNat  -- expand memory
      some ([keccak256Hash (st.evm.memory.data.extract off.toNat (off.toNat + len.toNat))],
            { st with evm := { st.evm with memory := mem } })
  | _, _ => none

/-- Master primop dispatcher: tries pure → read → write in order.
    Returns `(returnValues, newState)`.
    `none` means the primop is not recognized (invalid opcode). -/
def evalPrimop (name : String) (args : List Word256) (st : YulState) :
    Option (List Word256 × YulState) :=
  match evalPurePrimop name args with
  | some vals => some (vals, st)
  | none =>
    match evalReadPrimop name args st with
    | some vals => some (vals, st)
    | none => evalWritePrimop name args st

end LeanSP.EVM
