import Lean
import Lean.Data.Json

/-!
# HeytingLean.Blockchain.Contracts.LeanYulDSL.Spec

Typed "user requirements" for the restricted Lean→Solidity lane.

This is intentionally **template-based** (v0):
- it is practical for a UI (stable JSON schema),
- it keeps the proof surface small (finite cases), and
- it allows us to certify security-relevant properties (trace/effect shape).
-/

namespace HeytingLean.Blockchain.Contracts.LeanYulDSL

open Lean
open Lean.Json

inductive ContractTemplate where
  | owner
  | bank
  | erc20Mini
  deriving Repr, DecidableEq, Inhabited

def ContractTemplate.slug : ContractTemplate → String
  | .owner => "owner"
  | .bank => "bank"
  | .erc20Mini => "erc20Mini"

def ContractTemplate.parse? (s : String) : Option ContractTemplate :=
  if s = "owner" then some .owner
  else if s = "bank" then some .bank
  else if s = "erc20Mini" || s = "erc20" then some .erc20Mini
  else none

structure BankParams where
  /-- Whether to enable the empty-calldata `receive()` deposit path. -/
  allowReceive : Bool := true
  /-- Whether the withdraw logic must be CEI-style (write-before-call). -/
  cei : Bool := true
  deriving Repr, DecidableEq, Inhabited

structure ERC20MiniParams where
  totalSupply : Nat := 1000000
  deriving Repr, DecidableEq, Inhabited

inductive TemplateParams where
  | owner
  | bank (p : BankParams)
  | erc20Mini (p : ERC20MiniParams)
  deriving Repr, DecidableEq, Inhabited

def TemplateParams.template : TemplateParams → ContractTemplate
  | .owner => .owner
  | .bank _ => .bank
  | .erc20Mini _ => .erc20Mini

structure ContractSpec where
  version : String := "heyting.contract_spec.v0"
  pragma : String := "^0.8.20"
  contractName? : Option String := none
  params : TemplateParams := .owner
  deriving Repr, DecidableEq, Inhabited

def ContractSpec.template (s : ContractSpec) : ContractTemplate :=
  s.params.template

namespace JsonIO

private def expectField (j : Json) (name : String) : Except String Json :=
  j.getObjVal? name

private def optString (j : Json) (name : String) : Option String :=
  match j.getObjValAs? String name with
  | .ok s => some s
  | .error _ => none

private def optBool (j : Json) (name : String) : Option Bool :=
  match j.getObjValAs? Bool name with
  | .ok b => some b
  | .error _ => none

private def optNat (j : Json) (name : String) : Option Nat :=
  match j.getObjValAs? Nat name with
  | .ok n => some n
  | .error _ => none

private def parseBankParams (j : Json) : Except String BankParams := do
  let allowReceive := optBool j "allowReceive" |>.getD true
  let cei := optBool j "cei" |>.getD true
  pure { allowReceive := allowReceive, cei := cei }

private def parseERC20MiniParams (j : Json) : Except String ERC20MiniParams := do
  let totalSupply := optNat j "totalSupply" |>.getD 1000000
  pure { totalSupply := totalSupply }

def parseContractSpec (j : Json) : Except String ContractSpec := do
  let version := optString j "version" |>.getD "heyting.contract_spec.v0"
  if version ≠ "heyting.contract_spec.v0" then
    throw s!"unsupported ContractSpec.version '{version}'"
  let pragma := optString j "pragma" |>.getD "^0.8.20"
  let contractName? := optString j "contractName"
  let templateStr ← j.getObjValAs? String "template"
  let template ←
    match ContractTemplate.parse? templateStr with
    | some t => pure t
    | none => throw s!"unknown template '{templateStr}' (expected owner|bank|erc20Mini)"
  let paramsJ? : Option Json :=
    match j.getObjVal? "params" with
    | .ok pj => some pj
    | .error _ => none
  let params ←
    match template with
    | .owner =>
        pure TemplateParams.owner
    | .bank =>
        match paramsJ? with
        | none => pure (TemplateParams.bank {})
        | some pj => pure (TemplateParams.bank (← parseBankParams pj))
    | .erc20Mini =>
        match paramsJ? with
        | none => pure (TemplateParams.erc20Mini {})
        | some pj => pure (TemplateParams.erc20Mini (← parseERC20MiniParams pj))
  pure { version := version, pragma := pragma, contractName? := contractName?, params := params }

def templateParamsToJson : TemplateParams → Json
  | .owner =>
      Json.mkObj []
  | .bank p =>
      Json.mkObj
        [
          ("allowReceive", Json.bool p.allowReceive),
          ("cei", Json.bool p.cei),
        ]
  | .erc20Mini p =>
      Json.mkObj
        [
          ("totalSupply", Json.num p.totalSupply),
        ]

def contractSpecToJson (s : ContractSpec) : Json :=
  let base : List (String × Json) :=
    [
      ("version", Json.str s.version),
      ("template", Json.str s.template.slug),
      ("pragma", Json.str s.pragma),
      ("params", templateParamsToJson s.params),
    ]
  let base :=
    match s.contractName? with
    | none => base
    | some nm => base ++ [("contractName", Json.str nm)]
  Json.mkObj base

end JsonIO

end HeytingLean.Blockchain.Contracts.LeanYulDSL
