import Lean
import Lean.Data.Json
import HeytingLean.Blockchain.Contracts.Model
import HeytingLean.Blockchain.Contracts.Spec

/-
# erc_demo CLI

Tiny CLI that exercises the abstract ERC20 model by constructing the
default initial state, running a small hard-coded call trace, and
printing the resulting state together with the total-supply invariant
from `Blockchain.Contracts.Model`.

This can be extended in future to parse JSON call traces and to surface
more detailed invariant checks, but for now it provides a lightweight
smoke test for `erc20Model` and `ERC20Invariants`.
-/

namespace HeytingLean
namespace CLI
namespace ERCDemo

open Lean
open HeytingLean.Blockchain.Contracts.Model
open HeytingLean.Blockchain.Contracts.Model.ContractModel
open HeytingLean.Blockchain.Contracts.Spec

-- Decode helpers for JSON-encoded ERC20 calls.
namespace JsonDecode

/-- Parse a single JSON object into an `ERC20Call`. -/
def parseERC20Call (j : Json) : Except String ERC20Call := do
  -- Use the helpers from `Lean.Data.Json.Basic` to decode fields.
  let opJson ← Json.getObjVal? j "op"
  let op ← Json.getStr? opJson
  if op = "transfer" then
    do
      let fromJson ← Json.getObjVal? j "from"
      let fromAddr ← Json.getStr? fromJson
      let toJson ← Json.getObjVal? j "to"
      let toAddr ← Json.getStr? toJson
      let amtJ ← Json.getObjVal? j "amount"
      let amount ← Json.getNat? amtJ
      pure (ERC20Call.transfer fromAddr toAddr amount)
  else if op = "approve" then
    do
      let ownerJson ← Json.getObjVal? j "owner"
      let owner ← Json.getStr? ownerJson
      let spenderJson ← Json.getObjVal? j "spender"
      let spender ← Json.getStr? spenderJson
      let amtJ ← Json.getObjVal? j "amount"
      let amount ← Json.getNat? amtJ
      pure (ERC20Call.approve owner spender amount)
  else if op = "transferFrom" then
    do
      let spenderJson ← Json.getObjVal? j "spender"
      let spenderAddr ← Json.getStr? spenderJson
      let fromJson ← Json.getObjVal? j "from"
      let fromAddr ← Json.getStr? fromJson
      let toJson ← Json.getObjVal? j "to"
      let toAddr ← Json.getStr? toJson
      let amtJ ← Json.getObjVal? j "amount"
      let amount ← Json.getNat? amtJ
      pure (ERC20Call.transferFrom spenderAddr fromAddr toAddr amount)
  else
    .error s!"unknown op '{op}' (expected 'transfer', 'approve', or 'transferFrom')"

/-- Parse a JSON value representing a list of ERC20 calls. -/
def parseCallList (j : Json) : Except String (List ERC20Call) := do
  let arr ← Json.getArr? j
  -- Traverse the array, accumulating decoded calls.
  let rec loop (i : Nat) (acc : List ERC20Call) : Except String (List ERC20Call) := do
    if i < arr.size then
      match arr[i]? with
      | some ji =>
          match parseERC20Call ji with
          | .ok c => loop (i+1) (c :: acc)
          | .error msg => .error s!"at index {i}: {msg}"
      | none =>
          .error s!"index out of bounds: {i}"
    else
      .ok acc.reverse
  loop 0 []

end JsonDecode

/-- A tiny sample ERC20 call trace used by the CLI. -/
def sampleCalls : List ERC20Call :=
  [ ERC20Call.approve "alice" "bob" 100
  , ERC20Call.transferFrom "bob" "alice" "bob" 40 ]

/-- A nontrivial initial state so the demo trace succeeds. -/
def sampleInit : ERC20State :=
  { erc20Init with
    balances := fun a => if a = "alice" then 100 else 0
    totalSupply := 100 }

def main (argv : List String) : IO UInt32 := do
  let s0 := sampleInit
  -- Decide which call trace to run: either from a JSON file (if a path
  -- is provided) or the built-in `sampleCalls` otherwise.
  let calls ←
    match argv with
    | path :: _ =>
        -- Interpret the first CLI argument as a JSON file containing
        -- an array of ERC20 calls.
        try
          let contents ← IO.FS.readFile path
          match Json.parse contents with
          | .ok j =>
              match JsonDecode.parseCallList j with
              | .ok cs => pure cs
              | .error msg => do
                  IO.eprintln s!"erc_demo: error decoding calls from '{path}': {msg}"
                  pure sampleCalls
          | .error msg => do
              IO.eprintln s!"erc_demo: error parsing JSON from '{path}': {msg}"
              pure sampleCalls
        catch e =>
          IO.eprintln s!"erc_demo: error reading '{path}': {e.toString}"
          pure sampleCalls
    | [] =>
        pure sampleCalls

  IO.println s!"erc_demo: initial totalSupply = {s0.totalSupply}"
  IO.println s!"erc_demo: running call trace of length {calls.length}…"
  let res := runFrom erc20Model s0 calls
  match res with
  | .ok s' =>
      IO.println s!"erc_demo: run succeeded."
      IO.println s!"  final totalSupply = {s'.totalSupply}"
      IO.println s!"  initial totalSupply = {s0.totalSupply}"
      let invHolds : Bool := decide (s'.totalSupply = s0.totalSupply)
      IO.println s!"  ERC20Invariants (totalSupply = initial) holds? {invHolds}"
      let pid := PropertyId.erc20Correctness
      IO.println s!"  property touched: {pid.title} ({pid.slug})"
      pure 0
  | .error err =>
      let errMsg :=
        match err with
        | ERC20Error.insufficientBalance => "insufficientBalance"
        | ERC20Error.insufficientAllowance => "insufficientAllowance"
      IO.println s!"erc_demo: run failed with error: {errMsg}"
      IO.println "  (Invariants are only required to hold for successful runs starting from the initial state.)"
      pure 1

end ERCDemo
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.ERCDemo.main args
