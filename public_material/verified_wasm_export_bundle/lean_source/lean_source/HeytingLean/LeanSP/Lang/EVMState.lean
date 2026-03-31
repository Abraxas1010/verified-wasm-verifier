import Std
import HeytingLean.LeanSP.Lang.YulSyntax
import HeytingLean.LeanSP.Arith.Word256
import HeytingLean.LeanSP.Memory.EVMMemory
import HeytingLean.LeanSP.Memory.EVMStorage
import HeytingLean.LeanSP.Memory.EVMStack

/-!
# LeanSP.Lang.EVMState

Complete EVM machine state for Yul operational semantics.

`VarStore` uses association lists (not HashMap) for proof-friendly reasoning:
`get?_insert_same`, `get?_insert_ne` are trivially provable.
-/

namespace LeanSP.EVM

open LeanSP.Arith
open LeanSP.Memory

/-- Full EVM execution environment state. -/
structure EVMState where
  memory           : EVMMemory
  storage          : EVMStorage
  transientStorage : EVMStorage
  calldata         : ByteArray
  returnData       : ByteArray
  caller           : Word256
  address          : Word256
  callValue        : Word256
  selfBalance      : Word256
  blockNumber      : Word256
  timestamp        : Word256
  chainId          : Word256
  baseFee          : Word256
  gasPrice         : Word256
  origin           : Word256
  coinbase         : Word256
  gasLimit         : Word256
  gas              : Nat
  deriving Inhabited

def EVMState.default : EVMState where
  memory := EVMMemory.empty
  storage := EVMStorage.empty
  transientStorage := EVMStorage.empty
  calldata := ByteArray.empty
  returnData := ByteArray.empty
  caller := Word256.zero
  address := Word256.zero
  callValue := Word256.zero
  selfBalance := Word256.zero
  blockNumber := Word256.zero
  timestamp := Word256.zero
  chainId := BitVec.ofNat 256 1
  baseFee := Word256.zero
  gasPrice := Word256.zero
  origin := Word256.zero
  coinbase := Word256.zero
  gasLimit := Word256.zero
  gas := 1000000

-- ==========================================
-- Proof-friendly variable store (association list)
-- ==========================================

/-- Variable store: association list mapping names to Word256 values.
    Uses cons-based insert (new bindings shadow old ones). -/
def VarStore := List (String × Word256)
  deriving Inhabited

/-- Lookup a variable by name. Returns the FIRST matching entry (most recent). -/
def VarStore.get? (store : VarStore) (key : String) : Option Word256 :=
  match store with
  | [] => none
  | (k, v) :: rest => if k == key then some v else VarStore.get? rest key

/-- Lookup with default. -/
def VarStore.getD (store : VarStore) (key : String) (default : Word256) : Word256 :=
  (store.get? key).getD default

/-- Insert a binding (prepend — shadows any previous binding). -/
def VarStore.insert (store : VarStore) (key : String) (val : Word256) : VarStore :=
  (key, val) :: store

/-- Empty variable store. -/
def VarStore.empty : VarStore := []

-- Variable store lemmas (all proved)

@[simp] theorem VarStore.get?_insert_same (store : VarStore) (key : String) (val : Word256) :
    (store.insert key val).get? key = some val := by
  simp [insert, get?, BEq.beq]

@[simp] theorem VarStore.get?_insert_ne (store : VarStore) (k1 k2 : String) (val : Word256)
    (hne : (k2 == k1) = false) :
    (store.insert k2 val).get? k1 = store.get? k1 := by
  simp [insert, get?, hne]

@[simp] theorem VarStore.get?_empty (key : String) :
    VarStore.empty.get? key = none := by
  simp [empty, get?]

-- ==========================================
-- Function store (also association list)
-- ==========================================

def FuncStore := List (String × Yul.FuncDef)
  deriving Inhabited

def FuncStore.get? (store : FuncStore) (key : String) : Option Yul.FuncDef :=
  match store with
  | [] => none
  | (k, v) :: rest => if k == key then some v else FuncStore.get? rest key

def FuncStore.insert (store : FuncStore) (key : String) (val : Yul.FuncDef) : FuncStore :=
  (key, val) :: store

def FuncStore.empty : FuncStore := []

-- ==========================================
-- Combined Yul execution state
-- ==========================================

/-- Combined Yul execution state: EVM state + variable bindings + function table. -/
structure YulState where
  evm   : EVMState
  vars  : VarStore
  funcs : FuncStore
  deriving Inhabited

def YulState.init (evmState : EVMState) (funcs : Array Yul.FuncDef) : YulState :=
  let funcList := funcs.toList.map (fun f => (f.name, f))
  { evm := evmState, vars := VarStore.empty, funcs := funcList }

/-- Execution result. -/
inductive ExecResult where
  | continue_ : YulState → ExecResult
  | return_   : ByteArray → YulState → ExecResult
  | revert    : ByteArray → YulState → ExecResult
  | stop      : YulState → ExecResult
  | break_    : YulState → ExecResult
  | continue' : YulState → ExecResult
  | leave     : YulState → ExecResult
  | outOfFuel : ExecResult
  | invalid   : String → ExecResult
  deriving Inhabited

end LeanSP.EVM
