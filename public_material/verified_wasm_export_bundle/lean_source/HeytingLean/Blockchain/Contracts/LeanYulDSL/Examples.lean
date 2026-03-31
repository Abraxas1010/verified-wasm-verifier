import Std
import HeytingLean.BountyHunter.Solc.YulObjectMini.Types
import HeytingLean.BountyHunter.Solc.YulObjectMini.Pretty
import HeytingLean.Blockchain.Contracts.LeanYulDSL.Emit
import HeytingLean.Blockchain.Contracts.LeanYulDSL.Templates

/-!
# HeytingLean.Blockchain.Contracts.LeanYulDSL.Examples

Lean-generated example contracts expressed as **Yul object AST** (then pretty-printed).

These are meant as:
- a seed for a future "Lean contract DSL → codegen" direction, and
- a practical smoke test: can we produce Yul that `solc` compiles to deployable bytecode?

This stays intentionally small and functional:
- `owner`: stores deployer address in slot 0 and returns it.
  - `bank`: a minimal ETH bank:
  - `deposit()` (selector `0xd0e30db0`) / receive(): credits `balances[msg.sender]`
  - `balanceOf(address)` (selector `0x70a08231`) reads mapping element
  - `withdraw(uint256)` (selector `0x2e1a7d4d`) CEI-style safe withdraw
- `erc20`: a minimal ERC20-like token:
  - totalSupply at slot 0, balances mapping at base slot 1
  - init mints a fixed supply to deployer
  - `totalSupply()` (selector `0x18160ddd`)
  - `balanceOf(address)` (selector `0x70a08231`)
  - `transfer(address,uint256)` (selector `0xa9059cbb`) returns `bool`
-/

namespace HeytingLean.Blockchain.Contracts.LeanYulDSL

open HeytingLean.BountyHunter.Solc.YulObjectMini

def ownerProgram : Program :=
  yulObjectOfParts ownerParts

def bankProgram : Program :=
  yulObjectOfParts (bankParts (allowReceive := true))

def erc20Program : Program :=
  yulObjectOfParts (erc20MiniParts 1000000)

inductive ExampleId where
  | owner
  | bank
  | erc20
  deriving Repr, DecidableEq

def ExampleId.slug : ExampleId → String
  | .owner => "owner"
  | .bank => "bank"
  | .erc20 => "erc20"

def exampleProgram : ExampleId → Program
  | .owner => ownerProgram
  | .bank => bankProgram
  | .erc20 => erc20Program

def exampleBySlug? (s : String) : Option (ExampleId × Program) :=
  if s = "owner" then some (.owner, ownerProgram)
  else if s = "bank" then some (.bank, bankProgram)
  else if s = "erc20" then some (.erc20, erc20Program)
  else none

def exampleToYul (p : Program) : String :=
  programToCanonicalString p ++ "\n"

end HeytingLean.Blockchain.Contracts.LeanYulDSL
