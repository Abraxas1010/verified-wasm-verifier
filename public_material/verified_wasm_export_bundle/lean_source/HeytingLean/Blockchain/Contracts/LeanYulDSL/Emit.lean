import Std
import HeytingLean.BountyHunter.Solc.YulObjectMini.Types
import HeytingLean.BountyHunter.Solc.YulObjectMini.Pretty

/-!
# HeytingLean.Blockchain.Contracts.LeanYulDSL.Emit

Lean-side emitters for a small "Lean contracts" lane:

- `YulParts` describes a contract as `(initBare, runtime)` code blocks.
- `yulObjectOfParts` packages parts into a Yul object.
- `solidityWrapperOfParts` emits Solidity source that inlines Yul in `assembly { ... }`.

This intentionally targets a **restricted subset** and prioritizes:
determinism, auditable artifacts (hashes), and compatibility with `solc`.
-/

namespace HeytingLean.Blockchain.Contracts.LeanYulDSL

open HeytingLean.BountyHunter.Solc.YulObjectMini

structure YulParts where
  objectName : String
  /-- Init code *excluding* the standard deploy tail (`datacopy`+`return runtime`). -/
  initBare : String
  /-- Runtime code executed by the deployed contract. -/
  runtime : String
  deriving Repr, DecidableEq, Inhabited

private def lines (xs : List String) : String :=
  String.intercalate "\n" xs

def yulDeployRuntime : String :=
  lines
    [
      "datacopy(0, dataoffset(\"runtime\"), datasize(\"runtime\"))",
      "return(0, datasize(\"runtime\"))",
    ]

private def joinNonEmptyLines (a b : String) : String :=
  let a := a.trim
  let b := b.trim
  match a.isEmpty, b.isEmpty with
  | true, true => ""
  | false, true => a
  | true, false => b
  | false, false => a ++ "\n" ++ b

def yulObjectOfParts (p : YulParts) : Program :=
  let init := joinNonEmptyLines p.initBare yulDeployRuntime
  {
    items :=
      #[
        .object p.objectName #[
          .code init,
          .object "runtime" #[
            .code p.runtime
          ]
        ]
      ]
  }

def yulObjectStringOfParts (p : YulParts) : String :=
  programToCanonicalString (yulObjectOfParts p) ++ "\n"

private def solidityLinesOfParts (pragma contractName initBare runtime : String) : List String :=
  let init := initBare.trim
  let runtime := runtime.trim
  let initAsmLines : List String :=
    if init.isEmpty then
      []
    else
      ["    assembly {"] ++
        (init.splitOn "\n" |>.map (fun ln => "      " ++ ln.trimRight) |>.filter (fun ln => ln.trim != "")) ++
        ["    }"]
  let runtimeAsmLines : List String :=
    (runtime.splitOn "\n" |>.map (fun ln => "      " ++ ln.trimRight) |>.filter (fun ln => ln.trim != ""))
  ["// SPDX-License-Identifier: UNLICENSED"]
    ++ [s!"pragma solidity {pragma};"]
    ++ [("contract " ++ contractName ++ " {")]
    ++ ["  constructor() payable {"]
    ++ initAsmLines
    ++ ["  }"]
    ++ ["  fallback() external payable {"]
    ++ ["    assembly {"]
    ++ runtimeAsmLines
    ++ ["    }"]
    ++ ["  }"]
    ++ ["}"]
    ++ [""]

def solidityWrapperOfParts (p : YulParts) (pragma contractName : String) : String :=
  String.intercalate "\n" (solidityLinesOfParts pragma contractName p.initBare p.runtime)

end HeytingLean.Blockchain.Contracts.LeanYulDSL
