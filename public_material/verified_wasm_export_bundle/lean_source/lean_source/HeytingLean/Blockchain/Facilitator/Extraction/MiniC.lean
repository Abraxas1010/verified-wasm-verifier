import HeytingLean.Blockchain.Facilitator.Validation
import HeytingLean.Blockchain.Facilitator.Settlement
import HeytingLean.MiniC.ToCCorrectness
import Mathlib.Data.Bool.Basic

/-!
# Blockchain.Facilitator.Extraction.MiniC

Phase 3: “verified extraction” via the repo-local MiniC→tiny-C pipeline.

We define a small MiniC implementation of the computational kernel:

- `facilitator_verify` computes the validity predicate (returns `1`/`0`);
- `facilitator_settle_*_if_valid` compute the post-settlement balances/nonces,
  but *only* apply the update when the same validity predicate holds.

Then the existing theorems in `HeytingLean.MiniC.ToCCorrectness` transport correctness from MiniC
to the tiny-C semantics.  We subsequently emit readable C with `HeytingLean.C.Emit`.
-/

namespace HeytingLean
namespace Blockchain
namespace Facilitator
namespace Extraction

open HeytingLean
open HeytingLean.MiniC
open HeytingLean.MiniC.ToC
open HeytingLean.MiniC.ToC (storeToC)
open HeytingLean.C

namespace Names

def sender : String := "sender"
def recipient : String := "recipient"
def amount : String := "amount"
def nonce : String := "nonce"
def senderBal : String := "senderBal"
def senderNonce : String := "senderNonce"
def recipientBal : String := "recipientBal"
def sigOk : String := "sigOk"

end Names

/-! ## Lean spec (computational kernel) -/

def validCore (sender recipient amount nonce senderBal senderNonce sigOk : Nat) : Prop :=
  sigOk = 1 ∧ sender ≠ recipient ∧ senderNonce = nonce ∧ amount ≤ senderBal

instance (sender recipient amount nonce senderBal senderNonce sigOk : Nat) :
    Decidable (validCore sender recipient amount nonce senderBal senderNonce sigOk) := by
  unfold validCore
  infer_instance

def verifyCore (sender recipient amount nonce senderBal senderNonce sigOk : Nat) : Nat :=
  if validCore sender recipient amount nonce senderBal senderNonce sigOk then 1 else 0

def settleSenderBalIfValid (sender recipient amount nonce senderBal senderNonce sigOk : Nat) : Nat :=
  if validCore sender recipient amount nonce senderBal senderNonce sigOk then senderBal - amount else senderBal

def settleRecipientBalIfValid (sender recipient amount nonce recipientBal senderBal senderNonce sigOk : Nat) : Nat :=
  if validCore sender recipient amount nonce senderBal senderNonce sigOk then recipientBal + amount else recipientBal

def settleSenderNonceIfValid (sender recipient amount nonce senderNonce senderBal sigOk : Nat) : Nat :=
  if validCore sender recipient amount nonce senderBal senderNonce sigOk then senderNonce + 1 else senderNonce

/-! ## MiniC implementation -/

namespace MiniCImpl

open Names

private def condCore : Expr :=
  let sigOkTrue : Expr := Expr.eq (.var sigOk) (.intLit 1)
  let senderNe : Expr := Expr.not (Expr.eq (.var sender) (.var recipient))
  let nonceOk : Expr := Expr.eq (.var senderNonce) (.var nonce)
  let fundsOk : Expr := Expr.le (.var amount) (.var senderBal)
  Expr.and sigOkTrue (Expr.and senderNe (Expr.and nonceOk fundsOk))

def verifyFun : Fun :=
  { name := "facilitator_verify"
    params := [sender, recipient, amount, nonce, senderBal, senderNonce, sigOk]
    body := Stmt.if_ condCore (Stmt.return (.intLit 1)) (Stmt.return (.intLit 0)) }

def settleSenderBalIfValidFun : Fun :=
  { name := "facilitator_settle_senderBal_if_valid"
    params := [sender, recipient, amount, nonce, senderBal, senderNonce, sigOk]
    body :=
      Stmt.if_ condCore
        (Stmt.return (Expr.sub (.var senderBal) (.var amount)))
        (Stmt.return (.var senderBal)) }

def settleRecipientBalIfValidFun : Fun :=
  { name := "facilitator_settle_recipientBal_if_valid"
    params := [sender, recipient, amount, nonce, recipientBal, senderBal, senderNonce, sigOk]
    body :=
      Stmt.if_ condCore
        (Stmt.return (Expr.add (.var recipientBal) (.var amount)))
        (Stmt.return (.var recipientBal)) }

def settleSenderNonceIfValidFun : Fun :=
  { name := "facilitator_settle_senderNonce_if_valid"
    params := [sender, recipient, amount, nonce, senderNonce, senderBal, sigOk]
    body :=
      Stmt.if_ condCore
        (Stmt.return (Expr.add (.var senderNonce) (.intLit 1)))
        (Stmt.return (.var senderNonce)) }

end MiniCImpl

/-! ## Fragment runner + MiniC→C transport

We provide a small, local “n-ary” runner (nat args, nat result) and a correctness lemma
transporting successful MiniC runs to successful C runs.
-/

namespace FragRunner

open HeytingLean.MiniC.ToC (valToInt)

def runNatFunFragN (fn : Fun) (args : List Nat) : Option Nat := do
  let σ ← MiniC.bindParams fn.params (args.map natToVal)
  match MiniC.execFrag fn.body σ with
  | some (MiniC.ExecResult.returned v) => MiniC.Val.asNat? v
  | _ => none

private lemma storeToC_update (σ : MiniC.Store) (x : String) (v : MiniC.Val) :
    storeToC (MiniC.update σ x v) = fun y => if y = x then some (valToInt v) else storeToC σ y := by
  ext y
  by_cases hy : y = x
  · subst hy
    simp [MiniC.update, storeToC, valToInt]
  · simp [MiniC.update, storeToC, hy, valToInt]

private lemma bindParams_toC_nat :
    ∀ {ps : List String} {ns : List Nat} {σ : MiniC.Store},
      MiniC.bindParams ps (ns.map natToVal) = some σ →
        C.bindParams ps (ns.map Int.ofNat) = some (storeToC σ)
  | [], [], σ, h => by
      simp [MiniC.bindParams] at h
      subst h
      simp [C.bindParams]
      ext x
      simp [storeToC, MiniC.emptyStore]
  | p :: ps, n :: ns, σ, h => by
      cases hσ' : MiniC.bindParams ps (ns.map natToVal) with
      | none =>
          simp [MiniC.bindParams, hσ'] at h
      | some σ' =>
          have hσ : MiniC.update σ' p (natToVal n) = σ := by
            simpa [MiniC.bindParams, hσ'] using h
          subst hσ
          -- the recursive binding in MiniC corresponds to the recursive binding in C under `storeToC`
          -- (and the final update matches by `storeToC_update`).
          have hC : C.bindParams ps (ns.map Int.ofNat) = some (storeToC σ') :=
            bindParams_toC_nat (ps := ps) (ns := ns) (σ := σ') hσ'
          simp [C.bindParams, hC, storeToC_update, natToVal, valToInt]
  | [], _ :: _, _, h => by
      simp [MiniC.bindParams] at h
  | _ :: _, [], _, h => by
      simp [MiniC.bindParams] at h

theorem runNatFunFragN_correct_toC
    (fn : Fun) (args : List Nat) (out : Nat)
    (h : runNatFunFragN fn args = some out) :
    C.runCFunFrag (MiniC.ToC.compileFun fn) (args.map Int.ofNat) = some (Int.ofNat out) := by
  unfold runNatFunFragN at h
  -- expand the monadic structure
  cases hBind : MiniC.bindParams fn.params (List.map natToVal args) with
  | none =>
      simp [hBind] at h
  | some σ =>
      cases hExec : MiniC.execFrag fn.body σ with
      | none =>
          simp [hBind, hExec] at h
      | some res =>
          cases res with
          | normal _ =>
              simp [hBind, hExec] at h
          | returned v =>
              have hAsNat : MiniC.Val.asNat? v = some out := by
                simpa [hBind, hExec] using h
              have hVal : valToInt v = Int.ofNat out :=
                valToInt_of_asNat? (v := v) (n := out) hAsNat
              have hStmt := compileStmt_correct (s := fn.body) (σ := σ) (r := MiniC.ExecResult.returned v) hExec
              have hCExec :
                  C.execFragC (MiniC.ToC.compileStmt fn.body) (storeToC σ)
                    = some (C.ExecResult.returned (Int.ofNat out)) := by
                simpa [execResultToC, hVal] using hStmt
              have hBindC : C.bindParams fn.params (args.map Int.ofNat) = some (storeToC σ) :=
                bindParams_toC_nat (ps := fn.params) (ns := args) (σ := σ) hBind
              dsimp [C.runCFunFrag, MiniC.ToC.compileFun]
              simp [hBindC, hCExec]

end FragRunner

/-! ## Kernel correctness (Lean spec ↔ MiniC ↔ tiny-C) -/

def sigOkNat (b : Bool) : Nat :=
  if b then 1 else 0

private lemma sigOkNat_eq_one_iff (b : Bool) : sigOkNat b = 1 ↔ b = true := by
  cases b <;> simp [sigOkNat]

theorem validCore_iff_isValid (chain : ChainView) (sp : SignedPayload) :
    validCore sp.data.sender sp.data.recipient sp.data.amount sp.data.nonce
        (chain.balance sp.data.sender) (chain.nonce sp.data.sender) (sigOkNat sp.signatureOk)
      ↔ isValid chain sp := by
  classical
  unfold validCore isValid
  constructor
  · intro h
    rcases h with ⟨hSig, hNe, hNonce, hBal⟩
    have hSig' : sp.signatureOk = true := (sigOkNat_eq_one_iff sp.signatureOk).1 hSig
    exact ⟨hSig', hNonce, hBal, hNe⟩
  · intro h
    rcases h with ⟨hSig, hNonce, hBal, hNe⟩
    have hSig' : sigOkNat sp.signatureOk = 1 := by
      exact (sigOkNat_eq_one_iff sp.signatureOk).2 hSig
    exact ⟨hSig', hNe, hNonce, hBal⟩

theorem verifyCore_eq_one_iff_isValid (chain : ChainView) (sp : SignedPayload) :
    verifyCore sp.data.sender sp.data.recipient sp.data.amount sp.data.nonce
        (chain.balance sp.data.sender) (chain.nonce sp.data.sender) (sigOkNat sp.signatureOk) = 1
      ↔ isValid chain sp := by
  classical
  let sender := sp.data.sender
  let recipient := sp.data.recipient
  let amount := sp.data.amount
  let nonce := sp.data.nonce
  let senderBal := chain.balance sender
  let senderNonce := chain.nonce sender
  let sigOk := sigOkNat sp.signatureOk
  have hVerify : verifyCore sender recipient amount nonce senderBal senderNonce sigOk = 1 ↔
      validCore sender recipient amount nonce senderBal senderNonce sigOk := by
    by_cases h : validCore sender recipient amount nonce senderBal senderNonce sigOk <;>
      simp [verifyCore, h]
  simpa [sender, recipient, amount, nonce, senderBal, senderNonce, sigOk] using
    hVerify.trans (validCore_iff_isValid (chain := chain) (sp := sp))

namespace MiniCImplCorrectness

open Names
open HeytingLean.MiniC

private def store7
    (sender recipient amount nonce senderBal senderNonce sigOk : Nat) : MiniC.Store :=
  MiniC.update
    (MiniC.update
      (MiniC.update
        (MiniC.update
          (MiniC.update
            (MiniC.update
              (MiniC.update MiniC.emptyStore Names.sigOk (MiniC.natToVal sigOk))
              Names.senderNonce (MiniC.natToVal senderNonce))
            Names.senderBal (MiniC.natToVal senderBal))
          Names.nonce (MiniC.natToVal nonce))
        Names.amount (MiniC.natToVal amount))
      Names.recipient (MiniC.natToVal recipient))
    Names.sender (MiniC.natToVal sender)

private def store8
    (sender recipient amount nonce recipientBal senderBal senderNonce sigOk : Nat) : MiniC.Store :=
  MiniC.update
    (MiniC.update
      (MiniC.update
        (MiniC.update
          (MiniC.update
            (MiniC.update
              (MiniC.update
                (MiniC.update MiniC.emptyStore Names.sigOk (MiniC.natToVal sigOk))
                Names.senderNonce (MiniC.natToVal senderNonce))
              Names.senderBal (MiniC.natToVal senderBal))
            Names.recipientBal (MiniC.natToVal recipientBal))
          Names.nonce (MiniC.natToVal nonce))
        Names.amount (MiniC.natToVal amount))
      Names.recipient (MiniC.natToVal recipient))
    Names.sender (MiniC.natToVal sender)

private def store7Nonce
    (sender recipient amount nonce senderNonce senderBal sigOk : Nat) : MiniC.Store :=
  MiniC.update
    (MiniC.update
      (MiniC.update
        (MiniC.update
          (MiniC.update
            (MiniC.update
              (MiniC.update MiniC.emptyStore Names.sigOk (MiniC.natToVal sigOk))
              Names.senderBal (MiniC.natToVal senderBal))
            Names.senderNonce (MiniC.natToVal senderNonce))
          Names.nonce (MiniC.natToVal nonce))
        Names.amount (MiniC.natToVal amount))
      Names.recipient (MiniC.natToVal recipient))
    Names.sender (MiniC.natToVal sender)

private def validCoreBool (sender recipient amount nonce senderBal senderNonce sigOk : Nat) : Bool :=
  decide (sigOk = 1) &&
    (!decide (sender = recipient) &&
      (decide (senderNonce = nonce) && decide (amount ≤ senderBal)))

private lemma validCoreBool_eq_true_iff
    (sender recipient amount nonce senderBal senderNonce sigOk : Nat) :
    validCoreBool sender recipient amount nonce senderBal senderNonce sigOk = true ↔
      validCore sender recipient amount nonce senderBal senderNonce sigOk := by
  classical
  unfold validCoreBool validCore
  simp

private lemma decide_intEq_eq_decide_natEq (a b : Nat) :
    decide ((a : Int) = (b : Int)) = decide (a = b) := by
  apply Bool.decide_congr
  constructor
  · intro h
    exact Int.ofNat.inj h
  · intro h
    cases h
    rfl

private lemma decide_intEq_one_eq_decide_natEq_one (a : Nat) :
    decide ((a : Int) = (1 : Int)) = decide (a = 1) := by
  apply Bool.decide_congr
  constructor
  · intro h
    have : Int.ofNat a = Int.ofNat 1 := by
      simpa using h
    exact Int.ofNat.inj this
  · intro h
    cases h
    rfl

private lemma eval_condCore_store7
    (sender recipient amount nonce senderBal senderNonce sigOk : Nat) :
    MiniC.evalExpr MiniCImpl.condCore (store7 sender recipient amount nonce senderBal senderNonce sigOk)
      = some (MiniC.Val.bool (validCoreBool sender recipient amount nonce senderBal senderNonce sigOk)) := by
  unfold MiniCImpl.condCore store7 validCoreBool
  simp [MiniC.evalExpr, decide_intEq_eq_decide_natEq, decide_intEq_one_eq_decide_natEq_one,
    Names.sender, Names.recipient, Names.amount, Names.nonce, Names.senderBal, Names.senderNonce, Names.sigOk]

private lemma eval_condCore_store8
    (sender recipient amount nonce recipientBal senderBal senderNonce sigOk : Nat) :
    MiniC.evalExpr MiniCImpl.condCore (store8 sender recipient amount nonce recipientBal senderBal senderNonce sigOk)
      = some (MiniC.Val.bool (validCoreBool sender recipient amount nonce senderBal senderNonce sigOk)) := by
  unfold MiniCImpl.condCore store8 validCoreBool
  simp [MiniC.evalExpr, decide_intEq_eq_decide_natEq, decide_intEq_one_eq_decide_natEq_one,
    Names.sender, Names.recipient, Names.amount, Names.nonce, Names.recipientBal, Names.senderBal,
    Names.senderNonce, Names.sigOk]

private lemma eval_condCore_store7Nonce
    (sender recipient amount nonce senderNonce senderBal sigOk : Nat) :
    MiniC.evalExpr MiniCImpl.condCore (store7Nonce sender recipient amount nonce senderNonce senderBal sigOk)
      = some (MiniC.Val.bool (validCoreBool sender recipient amount nonce senderBal senderNonce sigOk)) := by
  unfold MiniCImpl.condCore store7Nonce validCoreBool
  simp [MiniC.evalExpr, decide_intEq_eq_decide_natEq, decide_intEq_one_eq_decide_natEq_one,
    Names.sender, Names.recipient, Names.amount, Names.nonce, Names.senderBal, Names.senderNonce, Names.sigOk]

private lemma asNat?_sub_ofNat_ofNat {a b : Nat} (h : b ≤ a) :
    MiniC.Val.asNat? (MiniC.Val.int ((a : Int) - (b : Int))) = some (a - b) := by
  rw [(Int.ofNat_sub h).symm]
  simp [MiniC.Val.asNat?]

private lemma asNat?_add_ofNat_ofNat (a b : Nat) :
    MiniC.Val.asNat? (MiniC.Val.int ((a : Int) + (b : Int))) = some (a + b) := by
  rw [(Int.natCast_add a b).symm]
  simp [MiniC.Val.asNat?, -Int.natCast_add]

theorem verifyFun_runNatFunFragN
    (sender recipient amount nonce senderBal senderNonce sigOk : Nat) :
    FragRunner.runNatFunFragN MiniCImpl.verifyFun
        [sender, recipient, amount, nonce, senderBal, senderNonce, sigOk]
      = some (verifyCore sender recipient amount nonce senderBal senderNonce sigOk) := by
  classical
  have hBind :
      MiniC.bindParams MiniCImpl.verifyFun.params
          ([sender, recipient, amount, nonce, senderBal, senderNonce, sigOk].map natToVal)
        = some (store7 sender recipient amount nonce senderBal senderNonce sigOk) := by
    simp [MiniCImpl.verifyFun, MiniC.bindParams, store7]
  by_cases hValid : validCore sender recipient amount nonce senderBal senderNonce sigOk
  · -- valid: condition is true, so return 1
    have hBool : validCoreBool sender recipient amount nonce senderBal senderNonce sigOk = true := by
      exact (validCoreBool_eq_true_iff _ _ _ _ _ _ _).2 hValid
    have hCond :
        MiniC.evalExpr MiniCImpl.condCore (store7 sender recipient amount nonce senderBal senderNonce sigOk)
          = some (MiniC.Val.bool true) := by
      simpa [hBool] using
        (eval_condCore_store7 sender recipient amount nonce senderBal senderNonce sigOk)
    unfold FragRunner.runNatFunFragN
    rw [hBind]
    simp [MiniC.execFrag, MiniC.evalExpr, hCond, MiniCImpl.verifyFun, verifyCore, hValid]
  · -- invalid: condition is false, so return 0
    have hBool : validCoreBool sender recipient amount nonce senderBal senderNonce sigOk = false := by
      rcases Bool.dichotomy (validCoreBool sender recipient amount nonce senderBal senderNonce sigOk) with hb | hb
      · exact hb
      · exfalso
        exact hValid ((validCoreBool_eq_true_iff _ _ _ _ _ _ _).1 hb)
    have hCond :
        MiniC.evalExpr MiniCImpl.condCore (store7 sender recipient amount nonce senderBal senderNonce sigOk)
          = some (MiniC.Val.bool false) := by
      simpa [hBool] using
        (eval_condCore_store7 sender recipient amount nonce senderBal senderNonce sigOk)
    unfold FragRunner.runNatFunFragN
    rw [hBind]
    simp [MiniC.execFrag, MiniC.evalExpr, hCond, MiniCImpl.verifyFun, verifyCore, hValid]

theorem settleSenderBalIfValidFun_runNatFunFragN
    (sender recipient amount nonce senderBal senderNonce sigOk : Nat) :
    FragRunner.runNatFunFragN MiniCImpl.settleSenderBalIfValidFun
        [sender, recipient, amount, nonce, senderBal, senderNonce, sigOk]
      = some (settleSenderBalIfValid sender recipient amount nonce senderBal senderNonce sigOk) := by
  classical
  have hBind :
      MiniC.bindParams MiniCImpl.settleSenderBalIfValidFun.params
          ([sender, recipient, amount, nonce, senderBal, senderNonce, sigOk].map natToVal)
        = some (store7 sender recipient amount nonce senderBal senderNonce sigOk) := by
    simp [MiniCImpl.settleSenderBalIfValidFun, MiniC.bindParams, store7]
  by_cases hValid : validCore sender recipient amount nonce senderBal senderNonce sigOk
  · have hBool : validCoreBool sender recipient amount nonce senderBal senderNonce sigOk = true := by
      exact (validCoreBool_eq_true_iff _ _ _ _ _ _ _).2 hValid
    have hCond :
        MiniC.evalExpr MiniCImpl.condCore (store7 sender recipient amount nonce senderBal senderNonce sigOk)
          = some (MiniC.Val.bool true) := by
      simpa [hBool] using
        (eval_condCore_store7 sender recipient amount nonce senderBal senderNonce sigOk)
    have hAsNat :
        MiniC.Val.asNat? (MiniC.Val.int ((senderBal : Int) - (amount : Int)))
          = some (senderBal - amount) :=
      asNat?_sub_ofNat_ofNat (a := senderBal) (b := amount) (h := hValid.2.2.2)
    unfold FragRunner.runNatFunFragN
    rw [hBind]
    simp [-MiniC.Val.asNat?, MiniC.execFrag, hCond, MiniCImpl.settleSenderBalIfValidFun,
      settleSenderBalIfValid, hValid]
    simp [-MiniC.Val.asNat?, MiniC.evalExpr, store7, Names.sender, Names.recipient, Names.amount, Names.nonce,
      Names.senderBal, hAsNat]
  · have hBool : validCoreBool sender recipient amount nonce senderBal senderNonce sigOk = false := by
      rcases Bool.dichotomy (validCoreBool sender recipient amount nonce senderBal senderNonce sigOk) with hb | hb
      · exact hb
      · exfalso
        exact hValid ((validCoreBool_eq_true_iff _ _ _ _ _ _ _).1 hb)
    have hCond :
        MiniC.evalExpr MiniCImpl.condCore (store7 sender recipient amount nonce senderBal senderNonce sigOk)
          = some (MiniC.Val.bool false) := by
      simpa [hBool] using
        (eval_condCore_store7 sender recipient amount nonce senderBal senderNonce sigOk)
    unfold FragRunner.runNatFunFragN
    rw [hBind]
    simp [MiniC.execFrag, hCond, MiniCImpl.settleSenderBalIfValidFun, settleSenderBalIfValid, hValid]
    simp [MiniC.evalExpr, store7, Names.sender, Names.recipient, Names.amount, Names.nonce, Names.senderBal]

theorem settleRecipientBalIfValidFun_runNatFunFragN
    (sender recipient amount nonce recipientBal senderBal senderNonce sigOk : Nat) :
    FragRunner.runNatFunFragN MiniCImpl.settleRecipientBalIfValidFun
        [sender, recipient, amount, nonce, recipientBal, senderBal, senderNonce, sigOk]
      = some (settleRecipientBalIfValid sender recipient amount nonce recipientBal senderBal senderNonce sigOk) := by
  classical
  have hBind :
      MiniC.bindParams MiniCImpl.settleRecipientBalIfValidFun.params
          ([sender, recipient, amount, nonce, recipientBal, senderBal, senderNonce, sigOk].map natToVal)
        = some (store8 sender recipient amount nonce recipientBal senderBal senderNonce sigOk) := by
    simp [MiniCImpl.settleRecipientBalIfValidFun, MiniC.bindParams, store8]
  by_cases hValid : validCore sender recipient amount nonce senderBal senderNonce sigOk
  · have hBool : validCoreBool sender recipient amount nonce senderBal senderNonce sigOk = true := by
      exact (validCoreBool_eq_true_iff _ _ _ _ _ _ _).2 hValid
    have hCond :
        MiniC.evalExpr MiniCImpl.condCore (store8 sender recipient amount nonce recipientBal senderBal senderNonce sigOk)
          = some (MiniC.Val.bool true) := by
      simpa [hBool] using
        (eval_condCore_store8 sender recipient amount nonce recipientBal senderBal senderNonce sigOk)
    have hAsNat :
        MiniC.Val.asNat? (MiniC.Val.int ((recipientBal : Int) + (amount : Int)))
          = some (recipientBal + amount) :=
      asNat?_add_ofNat_ofNat recipientBal amount
    unfold FragRunner.runNatFunFragN
    rw [hBind]
    simp [-MiniC.Val.asNat?, MiniC.execFrag, hCond, MiniCImpl.settleRecipientBalIfValidFun,
      settleRecipientBalIfValid, hValid]
    simp [-MiniC.Val.asNat?, MiniC.evalExpr, store8, Names.sender, Names.recipient, Names.amount, Names.nonce,
      Names.recipientBal, hAsNat]
  · have hBool : validCoreBool sender recipient amount nonce senderBal senderNonce sigOk = false := by
      rcases Bool.dichotomy (validCoreBool sender recipient amount nonce senderBal senderNonce sigOk) with hb | hb
      · exact hb
      · exfalso
        exact hValid ((validCoreBool_eq_true_iff _ _ _ _ _ _ _).1 hb)
    have hCond :
        MiniC.evalExpr MiniCImpl.condCore (store8 sender recipient amount nonce recipientBal senderBal senderNonce sigOk)
          = some (MiniC.Val.bool false) := by
      simpa [hBool] using
        (eval_condCore_store8 sender recipient amount nonce recipientBal senderBal senderNonce sigOk)
    unfold FragRunner.runNatFunFragN
    rw [hBind]
    simp [MiniC.execFrag, hCond, MiniCImpl.settleRecipientBalIfValidFun, settleRecipientBalIfValid, hValid]
    simp [MiniC.evalExpr, store8, Names.sender, Names.recipient, Names.amount, Names.nonce, Names.recipientBal]

theorem settleSenderNonceIfValidFun_runNatFunFragN
    (sender recipient amount nonce senderNonce senderBal sigOk : Nat) :
    FragRunner.runNatFunFragN MiniCImpl.settleSenderNonceIfValidFun
        [sender, recipient, amount, nonce, senderNonce, senderBal, sigOk]
      = some (settleSenderNonceIfValid sender recipient amount nonce senderNonce senderBal sigOk) := by
  classical
  have hBind :
      MiniC.bindParams MiniCImpl.settleSenderNonceIfValidFun.params
          ([sender, recipient, amount, nonce, senderNonce, senderBal, sigOk].map natToVal)
        = some (store7Nonce sender recipient amount nonce senderNonce senderBal sigOk) := by
    simp [MiniCImpl.settleSenderNonceIfValidFun, MiniC.bindParams, store7Nonce]
  by_cases hValid : validCore sender recipient amount nonce senderBal senderNonce sigOk
  · have hBool : validCoreBool sender recipient amount nonce senderBal senderNonce sigOk = true := by
      exact (validCoreBool_eq_true_iff _ _ _ _ _ _ _).2 hValid
    have hCond :
        MiniC.evalExpr MiniCImpl.condCore (store7Nonce sender recipient amount nonce senderNonce senderBal sigOk)
          = some (MiniC.Val.bool true) := by
      simpa [hBool] using
        (eval_condCore_store7Nonce sender recipient amount nonce senderNonce senderBal sigOk)
    have hAsNat :
        MiniC.Val.asNat? (MiniC.Val.int ((senderNonce : Int) + (1 : Int)))
          = some (senderNonce + 1) := by
      simpa using (asNat?_add_ofNat_ofNat senderNonce 1)
    unfold FragRunner.runNatFunFragN
    rw [hBind]
    simp [-MiniC.Val.asNat?, MiniC.execFrag, hCond, MiniCImpl.settleSenderNonceIfValidFun,
      settleSenderNonceIfValid, hValid]
    simp [-MiniC.Val.asNat?, MiniC.evalExpr, store7Nonce, Names.sender, Names.recipient, Names.amount, Names.nonce,
      Names.senderNonce, hAsNat]
  · have hBool : validCoreBool sender recipient amount nonce senderBal senderNonce sigOk = false := by
      rcases Bool.dichotomy (validCoreBool sender recipient amount nonce senderBal senderNonce sigOk) with hb | hb
      · exact hb
      · exfalso
        exact hValid ((validCoreBool_eq_true_iff _ _ _ _ _ _ _).1 hb)
    have hCond :
        MiniC.evalExpr MiniCImpl.condCore (store7Nonce sender recipient amount nonce senderNonce senderBal sigOk)
          = some (MiniC.Val.bool false) := by
      simpa [hBool] using
        (eval_condCore_store7Nonce sender recipient amount nonce senderNonce senderBal sigOk)
    unfold FragRunner.runNatFunFragN
    rw [hBind]
    simp [MiniC.execFrag, hCond, MiniCImpl.settleSenderNonceIfValidFun, settleSenderNonceIfValid, hValid]
    simp [MiniC.evalExpr, store7Nonce, Names.sender, Names.recipient, Names.amount, Names.nonce, Names.senderNonce]

theorem verifyFun_correct_toC
    (sender recipient amount nonce senderBal senderNonce sigOk : Nat) :
    C.runCFunFrag (MiniC.ToC.compileFun MiniCImpl.verifyFun)
        ([sender, recipient, amount, nonce, senderBal, senderNonce, sigOk].map Int.ofNat)
      = some (Int.ofNat (verifyCore sender recipient amount nonce senderBal senderNonce sigOk)) := by
  apply FragRunner.runNatFunFragN_correct_toC (fn := MiniCImpl.verifyFun)
    (args := [sender, recipient, amount, nonce, senderBal, senderNonce, sigOk])
    (out := verifyCore sender recipient amount nonce senderBal senderNonce sigOk)
  simpa using verifyFun_runNatFunFragN sender recipient amount nonce senderBal senderNonce sigOk

theorem settleSenderBalIfValidFun_correct_toC
    (sender recipient amount nonce senderBal senderNonce sigOk : Nat) :
    C.runCFunFrag (MiniC.ToC.compileFun MiniCImpl.settleSenderBalIfValidFun)
        ([sender, recipient, amount, nonce, senderBal, senderNonce, sigOk].map Int.ofNat)
      = some (Int.ofNat (settleSenderBalIfValid sender recipient amount nonce senderBal senderNonce sigOk)) := by
  apply FragRunner.runNatFunFragN_correct_toC (fn := MiniCImpl.settleSenderBalIfValidFun)
    (args := [sender, recipient, amount, nonce, senderBal, senderNonce, sigOk])
    (out := settleSenderBalIfValid sender recipient amount nonce senderBal senderNonce sigOk)
  simpa using settleSenderBalIfValidFun_runNatFunFragN sender recipient amount nonce senderBal senderNonce sigOk

theorem settleRecipientBalIfValidFun_correct_toC
    (sender recipient amount nonce recipientBal senderBal senderNonce sigOk : Nat) :
    C.runCFunFrag (MiniC.ToC.compileFun MiniCImpl.settleRecipientBalIfValidFun)
        ([sender, recipient, amount, nonce, recipientBal, senderBal, senderNonce, sigOk].map Int.ofNat)
      =
      some (Int.ofNat (settleRecipientBalIfValid sender recipient amount nonce recipientBal senderBal senderNonce sigOk)) := by
  apply FragRunner.runNatFunFragN_correct_toC (fn := MiniCImpl.settleRecipientBalIfValidFun)
    (args := [sender, recipient, amount, nonce, recipientBal, senderBal, senderNonce, sigOk])
    (out := settleRecipientBalIfValid sender recipient amount nonce recipientBal senderBal senderNonce sigOk)
  simpa using
    settleRecipientBalIfValidFun_runNatFunFragN sender recipient amount nonce recipientBal senderBal senderNonce sigOk

theorem settleSenderNonceIfValidFun_correct_toC
    (sender recipient amount nonce senderNonce senderBal sigOk : Nat) :
    C.runCFunFrag (MiniC.ToC.compileFun MiniCImpl.settleSenderNonceIfValidFun)
        ([sender, recipient, amount, nonce, senderNonce, senderBal, sigOk].map Int.ofNat)
      = some (Int.ofNat (settleSenderNonceIfValid sender recipient amount nonce senderNonce senderBal sigOk)) := by
  apply FragRunner.runNatFunFragN_correct_toC (fn := MiniCImpl.settleSenderNonceIfValidFun)
    (args := [sender, recipient, amount, nonce, senderNonce, senderBal, sigOk])
    (out := settleSenderNonceIfValid sender recipient amount nonce senderNonce senderBal sigOk)
  simpa using settleSenderNonceIfValidFun_runNatFunFragN sender recipient amount nonce senderNonce senderBal sigOk

end MiniCImplCorrectness

end Extraction
end Facilitator
end Blockchain
end HeytingLean
