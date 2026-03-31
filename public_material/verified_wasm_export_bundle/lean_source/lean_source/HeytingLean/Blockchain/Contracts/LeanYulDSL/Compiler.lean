import Std
import HeytingLean.Blockchain.Contracts.LeanYulDSL.Spec
import HeytingLean.Blockchain.Contracts.LeanYulDSL.Emit
import HeytingLean.Blockchain.Contracts.LeanYulDSL.Templates

/-!
# HeytingLean.Blockchain.Contracts.LeanYulDSL.Compiler

Template compiler:

`ContractSpec` (typed requirements) → `YulParts` (+ emit config).

The design here is deliberately small so we can later attach proofs/certificates
case-by-case per template.
-/

namespace HeytingLean.Blockchain.Contracts.LeanYulDSL

structure CompileResult where
  spec : ContractSpec
  contractName : String
  pragma : String
  parts : YulParts
  deriving Repr, DecidableEq

private def defaultName : ContractTemplate → String
  | .owner => "Owner"
  | .bank => "Bank"
  | .erc20Mini => "ERC20Mini"

def compile (spec : ContractSpec) : Except String CompileResult := do
  let tmpl := spec.template
  let contractName := spec.contractName?.getD (defaultName tmpl)
  let pragma := spec.pragma
  let parts ←
    match spec.params with
    | .owner =>
        pure ownerParts
    | .bank p =>
        if p.cei = false then
          throw "bank params requested cei=false, but v0 compiler only supports CEI-safe withdraw"
        else
          pure (bankParts (allowReceive := p.allowReceive))
    | .erc20Mini p =>
        pure (erc20MiniParts p.totalSupply)
  pure { spec := spec, contractName := contractName, pragma := pragma, parts := parts }

end HeytingLean.Blockchain.Contracts.LeanYulDSL

