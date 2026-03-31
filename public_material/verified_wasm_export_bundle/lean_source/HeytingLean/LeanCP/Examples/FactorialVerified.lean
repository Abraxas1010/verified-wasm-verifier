import Mathlib.Data.Nat.Factorial.Basic
import HeytingLean.LeanCP.Core.VarLemmas
import HeytingLean.LeanCP.VCG.RecCallSound
import HeytingLean.LeanCP.Lang.CSyntaxLemmas

/-!
# LeanCP Example: Recursive Factorial

This module verifies a single recursive consumer of `execStmtRec` / `execCallRec`.
The function spec is now state-sensitive enough to recover the input parameter
from the callee state and assert the exact factorial return value.
-/

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

def factorialBody : CStmt :=
  .ite (.binop .eq (.var "n") (.intLit 0))
    (.ret (.intLit 1))
    (.seq
      (.assign (.var "tmp") (.call "factorial" [(.binop .sub (.var "n") (.intLit 1))]))
      (.ret (.binop .mul (.var "n") (.var "tmp"))))

def factorialState (heap : Heap) (nextAddr n : Nat) : CState :=
  { heap := heap
    env := [("n", .int (Int.ofNat n))]
    nextAddr := nextAddr }

def factorialPost (ret : CVal) : SProp := fun st =>
  ∃ n,
    st.lookupVar "n" = some (.int (Int.ofNat n)) ∧
    ret = .int (Int.ofNat (Nat.factorial n))

def factorialSpec : SFunSpec where
  name := "factorial"
  params := [("n", .int)]
  retType := .int
  pre := fun st => ∃ heap nextAddr n, st = factorialState heap nextAddr n
  post := factorialPost
  body := factorialBody

def factorialFunEnv : FunEnv
  | "factorial" => some factorialSpec
  | _ => none

def factorialMeasure : TermMeasure where
  measure fname st :=
    if fname = "factorial" then
      match st.lookupVar "n" with
      | some (.int z) => 4 * Int.toNat z + 2
      | _ => 0
    else
      0

private theorem factorial_entry_state (heap : Heap) (nextAddr n : Nat) :
    callEntryState (factorialState heap nextAddr (n + 1)) factorialSpec
        [.int (Int.ofNat n)] =
      factorialState heap nextAddr n := by
  simp [factorialState, callEntryState, factorialSpec, bindCallEnv]

private theorem factorial_entry_state_same (heap : Heap) (nextAddr n : Nat) :
    callEntryState (factorialState heap nextAddr n) factorialSpec
        [.int (Int.ofNat n)] =
      factorialState heap nextAddr n := by
  simp [factorialState, callEntryState, factorialSpec, bindCallEnv]

private theorem factorial_measure_state (heap : Heap) (nextAddr n : Nat) :
    factorialMeasure.measure "factorial" (factorialState heap nextAddr n) = 4 * n + 2 := by
  simp [factorialMeasure, factorialState, CState.lookupVar]

theorem factorial_body_executes :
    ∀ n heap nextAddr,
      ∃ st',
        execStmtRec factorialFunEnv (4 * n + 2) factorialBody (factorialState heap nextAddr n) =
          some (.returned (.int (Int.ofNat (Nat.factorial n))) st') ∧
        st'.lookupVar "n" = some (.int (Int.ofNat n)) := by
  intro n
  induction n with
  | zero =>
      intro heap nextAddr
      refine ⟨factorialState heap nextAddr 0, ?_, ?_⟩
      · have hcond :
            evalExpr (.binop .eq (.var "n") (.intLit 0)) (factorialState heap nextAddr 0) =
              some (.int 1) := by
            simpa [factorialState, evalExpr, evalStaticExpr, CState.lookupVar] using
              (show evalBinOp .eq (.int 0) (.int 0) = some (.int 1) by
                rfl)
        have hret :
            evalExpr (.intLit 1) (factorialState heap nextAddr 0) = some (.int 1) := by
          simp [evalExpr, evalStaticExpr]
        simp [factorialBody, execStmtRec, hcond, hret, isTruthy]
      · simp [factorialState, CState.lookupVar]
  | succ n ih =>
      intro heap nextAddr
      rcases ih heap nextAddr with ⟨stRec, hrec, _hnRec⟩
      let st := factorialState heap nextAddr (n + 1)
      let stTmp := (restoreCallerState st stRec).updateVar "tmp" (.int (Int.ofNat (Nat.factorial n)))
      have hfuelCall : 4 * (n + 1) = 4 * n + 3 + 1 := by omega
      have hfuelBody : 4 * (n + 1) + 2 = (4 * (n + 1) + 1) + 1 := by omega
      have hcond :
          evalExpr (.binop .eq (.var "n") (.intLit 0)) st = some (.int 0) := by
        simpa [st, factorialState, evalExpr, evalStaticExpr, CState.lookupVar] using
          (show evalBinOp .eq (.int (Int.ofNat (n + 1))) (.int 0) = some (.int 0) by
            change some (CVal.int (if ((n : Int) + 1) = 0 then 1 else 0)) = some (CVal.int 0)
            have hsucc : ((n : Int) + 1) ≠ 0 := by omega
            simp [hsucc])
      have harg :
          evalExpr (.binop .sub (.var "n") (.intLit 1)) st = some (.int (Int.ofNat n)) := by
        simpa [st, factorialState, evalExpr, evalStaticExpr, CState.lookupVar] using
          (show evalBinOp .sub (.int (Int.ofNat (n + 1))) (.int 1) = some (.int (Int.ofNat n)) by
            change some (CVal.int (((n : Int) + 1) - 1)) = some (CVal.int (n : Int))
            have hsub : (((n : Int) + 1) - 1) = (n : Int) := by omega
            simp [hsub])
      have hargs :
          evalArgs [(.binop .sub (.var "n") (.intLit 1))] st =
            some [.int (Int.ofNat n)] := by
        simp [evalArgs, harg]
      have hcall :
          execCallRec factorialFunEnv (4 * n + 3) "factorial"
              [(.binop .sub (.var "n") (.intLit 1))] st =
            some (.int (Int.ofNat (Nat.factorial n)), restoreCallerState st stRec) := by
        let k : ExecResult → Option (CVal × CState) := fun res =>
          match res with
          | .returned ret callee => some (ret, restoreCallerState st callee)
          | .normal callee => some (.undef, restoreCallerState st callee)
        rw [execCallRec, factorialFunEnv, hargs]
        simp [factorialSpec, st, factorialState, callEntryState, bindCallEnv]
        have hbind := congrArg (fun x => x.bind k) hrec
        simpa [factorialState, k] using hbind
      have hlookupN :
          stTmp.lookupVar "n" = some (.int (Int.ofNat (n + 1))) := by
        calc
          stTmp.lookupVar "n" = (restoreCallerState st stRec).lookupVar "n" := by
            simpa [stTmp] using
              lookupVar_updateVar_ne (restoreCallerState st stRec) "tmp" "n"
                (.int (Int.ofNat (Nat.factorial n))) (by decide : "n" ≠ "tmp")
          _ = st.lookupVar "n" := by
            rfl
          _ = some (.int (Int.ofNat (n + 1))) := by
            simp [st, factorialState, CState.lookupVar]
      have hlookupTmp :
          stTmp.lookupVar "tmp" = some (.int (Int.ofNat (Nat.factorial n))) := by
        simpa [stTmp] using
          lookupVar_updateVar_eq (restoreCallerState st stRec) "tmp" (.int (Int.ofNat (Nat.factorial n)))
      have hmul :
          evalExpr (.binop .mul (.var "n") (.var "tmp")) stTmp =
            some (.int (Int.ofNat (Nat.factorial (n + 1)))) := by
        calc
          evalExpr (.binop .mul (.var "n") (.var "tmp")) stTmp
              = some (.int (Int.ofNat (n + 1) * Int.ofNat (Nat.factorial n))) := by
                  simpa [evalExpr, evalStaticExpr, hlookupN, hlookupTmp] using
                    (show evalBinOp .mul (.int (Int.ofNat (n + 1))) (.int (Int.ofNat (Nat.factorial n))) =
                        some (.int (Int.ofNat (n + 1) * Int.ofNat (Nat.factorial n))) by
                      rfl)
          _ = some (.int (Int.ofNat ((n + 1) * Nat.factorial n))) := by
              simp
          _ = some (.int (Int.ofNat (Nat.factorial (n + 1)))) := by
              simp [Nat.factorial_succ, Nat.mul_comm]
      have hassign :
          execStmtRec factorialFunEnv (4 * (n + 1))
              (.assign (.var "tmp") (.call "factorial" [(.binop .sub (.var "n") (.intLit 1))])) st =
            some (.normal stTmp) := by
        let kAssign : CVal × CState → Option ExecResult := fun vr =>
          some (.normal (vr.2.updateVar "tmp" vr.1))
        rw [hfuelCall]
        have hbind := congrArg (fun x => x.bind kAssign) hcall
        simpa [execStmtRec, kAssign, stTmp] using hbind
      have hret :
          execStmtRec factorialFunEnv (4 * (n + 1))
              (.ret (.binop .mul (.var "n") (.var "tmp"))) stTmp =
            some (.returned (.int (Int.ofNat (Nat.factorial (n + 1)))) stTmp) := by
        rw [hfuelCall]
        rw [execStmtRec, hmul]
        · rfl
        · intro h
          omega
        · intro fuel fname args hf hEq
          cases hEq
      let kSeq : ExecResult → Option ExecResult := fun res =>
        match res with
        | .normal st' =>
            execStmtRec factorialFunEnv (4 * (n + 1))
              (.ret (.binop .mul (.var "n") (.var "tmp"))) st'
        | .returned v st' => some (.returned v st')
      have hseq :
          (execStmtRec factorialFunEnv (4 * (n + 1))
              (.assign (.var "tmp") (.call "factorial" [(.binop .sub (.var "n") (.intLit 1))])) st).bind kSeq =
            some (.returned (.int (Int.ofNat (Nat.factorial (n + 1)))) stTmp) := by
        have hbind := congrArg (fun x => x.bind kSeq) hassign
        simpa [kSeq, hret] using hbind
      refine ⟨stTmp, ?_, hlookupN⟩
      simpa [hfuelBody, factorialBody, execStmtRec, hcond, isTruthy, kSeq] using hseq

def factorialFunEnv_soundRec : FunEnvSoundRec factorialFunEnv := by
  refine ⟨factorialMeasure, ?_⟩
  intro fname spec hlookup st hpre
  by_cases hf : fname = "factorial"
  · subst hf
    have hspec : some factorialSpec = some spec := by simpa [factorialFunEnv] using hlookup
    injection hspec with hEq
    subst hEq
    rcases hpre with ⟨heap, nextAddr, n, rfl⟩
    rcases factorial_body_executes n heap nextAddr with ⟨st', hexec, hlookupN⟩
    refine ⟨.int (Int.ofNat (Nat.factorial n)), st', ?_, ?_⟩
    simpa [factorial_measure_state] using hexec
    exact ⟨n, hlookupN, rfl⟩
  · simp [factorialFunEnv] at hlookup

theorem factorial_xapp_smoke (n : Nat) (heap : Heap) (nextAddr : Nat) :
    swpCall factorialFunEnv "factorial" [.var "n"] (fun _ _ => True)
      (factorialState heap nextAddr n) := by
  apply swpCall_intro (funEnv := factorialFunEnv) (fname := "factorial")
    (args := [.var "n"]) (spec := factorialSpec)
    (vals := [.int (Int.ofNat n)]) (Q := fun _ _ => True)
  · rfl
  · simp [evalArgs, factorialState, evalExpr, evalStaticExpr, CState.lookupVar]
  · simp [factorialSpec]
  · exact ⟨heap, nextAddr, n, factorial_entry_state_same heap nextAddr n⟩
  · intro _ _ _
    trivial

theorem factorial_call_sound_smoke (n : Nat) (heap : Heap) (nextAddr : Nat) :
    ∃ ret st',
      execCallRec factorialFunEnv
          (factorialFunEnv_soundRec.term.measure "factorial"
            (callEntryState (factorialState heap nextAddr n) factorialSpec
              [.int (Int.ofNat n)]) + 1)
          "factorial" [.var "n"] (factorialState heap nextAddr n) =
        some (ret, st') := by
  have hvals :
      evalArgs [.var "n"] (factorialState heap nextAddr n) =
        some [.int (Int.ofNat n)] := by
    simp [evalArgs, factorialState, evalExpr, evalStaticExpr, CState.lookupVar]
  have hpre :
      factorialSpec.pre
        (callEntryState (factorialState heap nextAddr n) factorialSpec
          [.int (Int.ofNat n)]) := by
    exact ⟨heap, nextAddr, n, factorial_entry_state_same heap nextAddr n⟩
  rcases execCall_rec_sound (funEnv := factorialFunEnv) (henv := factorialFunEnv_soundRec)
      (fname := "factorial") (spec := factorialSpec)
      (vals := [.int (Int.ofNat n)]) (Q := fun _ _ => True)
      (hlookup := rfl) (hvals := hvals) (hlen := by simp [factorialSpec])
      (hpre := hpre) (hpost := by intro _ _ _; trivial) with
    ⟨ret, st', hexec, _⟩
  exact ⟨ret, st', hexec⟩

theorem factorial_executes (n : Nat) (heap : Heap) (nextAddr : Nat) :
    ∃ st',
      execStmtRec factorialFunEnv (4 * n + 2) factorialBody (factorialState heap nextAddr n) =
        some (.returned (.int (Int.ofNat (Nat.factorial n))) st') ∧
      st'.lookupVar "n" = some (.int (Int.ofNat n)) := by
  exact factorial_body_executes n heap nextAddr

end HeytingLean.LeanCP.Examples
