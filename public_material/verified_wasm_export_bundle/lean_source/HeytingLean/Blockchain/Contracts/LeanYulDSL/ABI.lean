import Lean
import Lean.Data.Json
import HeytingLean.Blockchain.Contracts.LeanYulDSL.Spec

/-!
# HeytingLean.Blockchain.Contracts.LeanYulDSL.ABI

Frontend-facing ABI emission for the restricted Lean contracts lane.

Important: ABI is an *interface*. The contract is still implemented via fallback
selector dispatch (inline Yul), but EVM clients (ethers/viem/etc.) can use the
ABI to encode calldata and decode return values.
-/

namespace HeytingLean.Blockchain.Contracts.LeanYulDSL

open Lean
open Lean.Json

structure AbiParam where
  name : String
  typ : String
  deriving Repr, DecidableEq, Inhabited

structure AbiFunction where
  name : String
  stateMutability : String
  inputs : Array AbiParam := #[]
  outputs : Array AbiParam := #[]
  deriving Repr, DecidableEq, Inhabited

private def paramToJson (p : AbiParam) : Json :=
  Json.mkObj [("name", Json.str p.name), ("type", Json.str p.typ)]

private def fnToJson (f : AbiFunction) : Json :=
  Json.mkObj
    [
      ("type", Json.str "function"),
      ("name", Json.str f.name),
      ("stateMutability", Json.str f.stateMutability),
      ("inputs", Json.arr (f.inputs.map paramToJson)),
      ("outputs", Json.arr (f.outputs.map paramToJson)),
    ]

def abiToJson (fs : Array AbiFunction) : Json :=
  Json.arr (fs.map fnToJson)

def abiOfTemplate : ContractTemplate → Array AbiFunction
  | .owner =>
      #[
        { name := "owner"
          stateMutability := "view"
          inputs := #[]
          outputs := #[{ name := "", typ := "address" }]
        }
      ]
  | .bank =>
      #[
        { name := "deposit"
          stateMutability := "payable"
          inputs := #[]
          outputs := #[]
        },
        { name := "withdraw"
          stateMutability := "nonpayable"
          inputs := #[{ name := "amount", typ := "uint256" }]
          outputs := #[]
        },
        { name := "balanceOf"
          stateMutability := "view"
          inputs := #[{ name := "account", typ := "address" }]
          outputs := #[{ name := "", typ := "uint256" }]
        }
      ]
  | .erc20Mini =>
      #[
        { name := "totalSupply"
          stateMutability := "view"
          inputs := #[]
          outputs := #[{ name := "", typ := "uint256" }]
        },
        { name := "balanceOf"
          stateMutability := "view"
          inputs := #[{ name := "account", typ := "address" }]
          outputs := #[{ name := "", typ := "uint256" }]
        },
        { name := "transfer"
          stateMutability := "nonpayable"
          inputs := #[{ name := "to", typ := "address" }, { name := "amount", typ := "uint256" }]
          outputs := #[{ name := "", typ := "bool" }]
        },
        { name := "allowance"
          stateMutability := "view"
          inputs := #[{ name := "owner", typ := "address" }, { name := "spender", typ := "address" }]
          outputs := #[{ name := "", typ := "uint256" }]
        },
        { name := "approve"
          stateMutability := "nonpayable"
          inputs := #[{ name := "spender", typ := "address" }, { name := "amount", typ := "uint256" }]
          outputs := #[{ name := "", typ := "bool" }]
        },
        { name := "transferFrom"
          stateMutability := "nonpayable"
          inputs := #[{ name := "from", typ := "address" }, { name := "to", typ := "address" }, { name := "amount", typ := "uint256" }]
          outputs := #[{ name := "", typ := "bool" }]
        }
      ]

end HeytingLean.Blockchain.Contracts.LeanYulDSL

