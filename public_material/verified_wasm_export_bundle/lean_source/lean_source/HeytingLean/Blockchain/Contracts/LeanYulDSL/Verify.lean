import Lean
import Lean.Data.Json
import HeytingLean.Blockchain.Contracts.LeanYulDSL.Compiler
import HeytingLean.BountyHunter.Solc.YulTextMini.Parse
import HeytingLean.BountyHunter.Solc.YulTextMini.ToAlgebraIR
import HeytingLean.BountyHunter.Solc.YulTextMini.EffectSemantics
import HeytingLean.BountyHunter.AlgebraIR.Dominators
import HeytingLean.BountyHunter.AlgebraIR.Json

/-!
# HeytingLean.Blockchain.Contracts.LeanYulDSL.Verify

V0 verification for the Lean→Solidity lane.

This is **not** a full semantics-preservation theorem; it is an *evidence spine*
using the existing `YulTextMini` effect semantics:

- Parse selected runtime function bodies from the emitted Yul.
- Compute a deterministic effect trace (storage read/write + call boundaries).
- Check template-specific safety obligations (e.g. CEI ordering).

This gives us a stable "certificate check" that we can later connect to:
solc IR ↔ Yul ↔ EVM trace certificates and, eventually, formal theorems.
-/

namespace HeytingLean.Blockchain.Contracts.LeanYulDSL

open Lean
open HeytingLean.BountyHunter
open HeytingLean.BountyHunter.Solc.YulTextMini
open HeytingLean.BountyHunter.AlgebraIR

structure MethodEvidence where
  name : String
  effects : Array Effect := #[]
  deriving Repr, DecidableEq, Inhabited

structure VerificationReport where
  version : String := "lean.contract_verify.v0"
  template : String
  ok : Bool
  errors : Array String := #[]
  methods : Array MethodEvidence := #[]
  deriving Repr, DecidableEq, Inhabited

private def effectSeqCEIOk (effs : Array Effect) : Bool :=
  Id.run do
    let mut seenWrite := false
    for e in effs do
      match e with
      | .storageWrite _ => seenWrite := true
      | .storageWriteDyn _ => seenWrite := true
      | .boundaryCall _ =>
          if !seenWrite then
            return false
      | _ => pure ()
    return true

private def effectSeqHasNoBoundary (effs : Array Effect) : Bool :=
  !(effs.any (fun e => match e with | .boundaryCall _ => true | _ => false))

private def effectsOfFunctionBodyE (runtime : String) (fn : String) : Except String (Array Effect) := do
  let ss ← parseFunctionBodyE runtime fn
  let (_, effs) := evalStmts {} ss
  pure effs

private def graphOfFunctionBodyE (runtime : String) (fn : String) : Except String Graph := do
  let ss ← parseFunctionBodyE runtime fn
  pure (HeytingLean.BountyHunter.Solc.YulTextMini.toAlgebraIR ss)

private def nodeHasBoundary (n : Node) : Bool :=
  n.effects.any (fun e => match e with | .boundaryCall _ => true | _ => false)

private def nodeHasWrite (n : Node) : Bool :=
  n.effects.any (fun e =>
    match e with
    | .storageWrite _ => true
    | .storageWriteDyn _ => true
    | _ => false)

private def idxOfId? (ids : Array Nat) (n : Nat) : Option Nat :=
  Id.run do
    let mut i : Nat := 0
    while i < ids.size do
      if ids[i]! = n then
        return some i
      i := i + 1
    return none

private def ceiDominanceOk (g : Graph) : Bool :=
  let domInfo := HeytingLean.BountyHunter.AlgebraIR.dominators g
  let boundaryIds := g.nodes.foldl (fun acc n => if nodeHasBoundary n then acc.push n.id else acc) #[]
  let writeIds := g.nodes.foldl (fun acc n => if nodeHasWrite n then acc.push n.id else acc) #[]
  boundaryIds.all (fun b =>
    match idxOfId? domInfo.ids b with
    | none => false
    | some i =>
        let domSet := domInfo.dom[i]!
        writeIds.any (fun w => domSet.contains w))

private def methodEvidenceE (runtime : String) (fn : String) : Except String MethodEvidence := do
  let effs ← effectsOfFunctionBodyE runtime fn
  pure { name := fn, effects := effs }

private def verifyOwner (r : CompileResult) : Except String VerificationReport := do
  -- Owner template has no public methods; the runtime is a single read+return.
  let ss ← parseStmtsFromStringE r.parts.runtime
  let (_, effs) := evalStmts {} ss
  let ok := effectSeqHasNoBoundary effs
  let errors :=
    if ok then #[] else #["owner runtime unexpectedly contains a boundary call"]
  pure {
    template := r.spec.template.slug
    ok := ok
    errors := errors
    methods := #[{ name := "runtime", effects := effs }]
  }

private def verifyBank (r : CompileResult) : Except String VerificationReport := do
  let dep ← methodEvidenceE r.parts.runtime "deposit"
  let wdr ← methodEvidenceE r.parts.runtime "withdraw"
  let okDeposit := effectSeqHasNoBoundary dep.effects
  -- Use a path-sensitive dominator check over the extracted CFG:
  -- for each boundary call node, some storage write must dominate it.
  let wdrGraph ← graphOfFunctionBodyE r.parts.runtime "withdraw"
  let okWithdraw := ceiDominanceOk wdrGraph
  let ok := okDeposit && okWithdraw
  let mut errs : Array String := #[]
  if !okDeposit then
    errs := errs.push "bank.deposit: unexpected boundary call (should be storage-only)"
  if !okWithdraw then
    errs := errs.push "bank.withdraw: CEI dominance failed (some boundary call is not dominated by a storage write)"
  pure {
    template := r.spec.template.slug
    ok := ok
    errors := errs
    methods := #[dep, wdr]
  }

private def verifyERC20Mini (r : CompileResult) : Except String VerificationReport := do
  let tr ← methodEvidenceE r.parts.runtime "transfer"
  let ap ← methodEvidenceE r.parts.runtime "approve"
  let tf ← methodEvidenceE r.parts.runtime "transferFrom"
  let al ← methodEvidenceE r.parts.runtime "allowance_slot"
  let okTransferNoBoundary := effectSeqHasNoBoundary tr.effects
  let okApproveNoBoundary := effectSeqHasNoBoundary ap.effects
  let okTransferFromNoBoundary := effectSeqHasNoBoundary tf.effects
  let ok := okTransferNoBoundary && okApproveNoBoundary && okTransferFromNoBoundary
  let mut errs : Array String := #[]
  if !okTransferNoBoundary then
    errs := errs.push "erc20Mini.transfer: unexpected boundary call (should be pure storage updates)"
  if !okApproveNoBoundary then
    errs := errs.push "erc20Mini.approve: unexpected boundary call (should be pure storage updates)"
  if !okTransferFromNoBoundary then
    errs := errs.push "erc20Mini.transferFrom: unexpected boundary call (should be pure storage updates)"
  pure {
    template := r.spec.template.slug
    ok := ok
    errors := errs
    methods := #[tr, ap, tf, al]
  }

def verifyCompiled (r : CompileResult) : Except String VerificationReport := do
  match r.spec.template with
  | .owner => verifyOwner r
  | .bank => verifyBank r
  | .erc20Mini => verifyERC20Mini r

namespace JsonIO

private def methodEvidenceToJson (m : MethodEvidence) : Json :=
  Json.mkObj
    [
      ("name", Json.str m.name),
      ("effects", Json.arr (m.effects.map HeytingLean.BountyHunter.AlgebraIR.effectToJson)),
    ]

def verificationReportToJson (r : VerificationReport) : Json :=
  Json.mkObj
    [
      ("version", Json.str r.version),
      ("template", Json.str r.template),
      ("ok", Json.bool r.ok),
      ("errors", Json.arr (r.errors.map Json.str)),
      ("methods", Json.arr (r.methods.map methodEvidenceToJson)),
    ]

end JsonIO

end HeytingLean.Blockchain.Contracts.LeanYulDSL
