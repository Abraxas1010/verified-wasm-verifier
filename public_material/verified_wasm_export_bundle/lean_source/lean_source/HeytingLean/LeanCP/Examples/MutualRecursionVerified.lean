import Mathlib.Data.Nat.Bits
import HeytingLean.LeanCP.VCG.RecCallSound
import HeytingLean.LeanCP.Lang.CSyntaxLemmas

/-!
# LeanCP Example: Mutual Recursion

This module exercises the recursive call layer on a genuine two-function cycle:
`isEven` calls `isOdd`, and `isOdd` calls `isEven`.
-/

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

def isEvenBody : CStmt :=
  .ite (.binop .eq (.var "n") (.intLit 0))
    (.ret (.intLit 1))
    (.ret (.call "isOdd" [(.binop .sub (.var "n") (.intLit 1))]))

def isOddBody : CStmt :=
  .ite (.binop .eq (.var "n") (.intLit 0))
    (.ret (.intLit 0))
    (.ret (.call "isEven" [(.binop .sub (.var "n") (.intLit 1))]))

def parityState (heap : Heap) (nextAddr n : Nat) : CState :=
  { heap := heap
    env := [("n", .int (Int.ofNat n))]
    nextAddr := nextAddr }

def evenRet (n : Nat) : CVal :=
  .int (if n % 2 = 0 then 1 else 0)

def oddRet (n : Nat) : CVal :=
  .int (if n % 2 = 0 then 0 else 1)

private theorem evenRet_succ (n : Nat) : evenRet (n + 1) = oddRet n := by
  unfold evenRet oddRet
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h] <;> omega

private theorem oddRet_succ (n : Nat) : oddRet (n + 1) = evenRet n := by
  unfold evenRet oddRet
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h] <;> omega

def evenPost (ret : CVal) : SProp := fun st =>
  ∃ n,
    st.lookupVar "n" = some (.int (Int.ofNat n)) ∧
    ret = evenRet n

def oddPost (ret : CVal) : SProp := fun st =>
  ∃ n,
    st.lookupVar "n" = some (.int (Int.ofNat n)) ∧
    ret = oddRet n

def evenSpec : SFunSpec where
  name := "isEven"
  params := [("n", .int)]
  retType := .int
  pre := fun st => ∃ heap nextAddr n, st = parityState heap nextAddr n
  post := evenPost
  body := isEvenBody

def oddSpec : SFunSpec where
  name := "isOdd"
  params := [("n", .int)]
  retType := .int
  pre := fun st => ∃ heap nextAddr n, st = parityState heap nextAddr n
  post := oddPost
  body := isOddBody

def parityFunEnv : FunEnv
  | "isEven" => some evenSpec
  | "isOdd" => some oddSpec
  | _ => none

def parityMeasure : TermMeasure where
      measure fname st :=
    if fname = "isEven" then
      match st.lookupVar "n" with
      | some (.int z) => 3 * Int.toNat z + 2
      | _ => 0
    else if fname = "isOdd" then
      match st.lookupVar "n" with
      | some (.int z) => 3 * Int.toNat z + 2
      | _ => 0
    else
      0

private theorem even_entry_state (heap : Heap) (nextAddr n : Nat) :
    callEntryState (parityState heap nextAddr (n + 1)) evenSpec [.int (Int.ofNat n)] =
      parityState heap nextAddr n := by
  simp [parityState, callEntryState, evenSpec, bindCallEnv]

private theorem odd_entry_state (heap : Heap) (nextAddr n : Nat) :
    callEntryState (parityState heap nextAddr (n + 1)) oddSpec [.int (Int.ofNat n)] =
      parityState heap nextAddr n := by
  simp [parityState, callEntryState, oddSpec, bindCallEnv]

private theorem even_entry_state_same (heap : Heap) (nextAddr n : Nat) :
    callEntryState (parityState heap nextAddr n) evenSpec [.int (Int.ofNat n)] =
      parityState heap nextAddr n := by
  simp [parityState, callEntryState, evenSpec, bindCallEnv]

private theorem odd_entry_state_same (heap : Heap) (nextAddr n : Nat) :
    callEntryState (parityState heap nextAddr n) oddSpec [.int (Int.ofNat n)] =
      parityState heap nextAddr n := by
  simp [parityState, callEntryState, oddSpec, bindCallEnv]

private theorem parity_measure_even_state (heap : Heap) (nextAddr n : Nat) :
    parityMeasure.measure "isEven" (parityState heap nextAddr n) = 3 * n + 2 := by
  simp [parityMeasure, parityState, CState.lookupVar]

private theorem parity_measure_odd_state (heap : Heap) (nextAddr n : Nat) :
    parityMeasure.measure "isOdd" (parityState heap nextAddr n) = 3 * n + 2 := by
  simp [parityMeasure, parityState, CState.lookupVar]

theorem mutual_recursion_executes :
    ∀ n heap nextAddr,
      (∃ stEven,
          execStmtRec parityFunEnv (3 * n + 2) isEvenBody (parityState heap nextAddr n) =
            some (.returned (evenRet n) stEven) ∧
          stEven.lookupVar "n" = some (.int (Int.ofNat n))) ∧
      (∃ stOdd,
          execStmtRec parityFunEnv (3 * n + 2) isOddBody (parityState heap nextAddr n) =
            some (.returned (oddRet n) stOdd) ∧
          stOdd.lookupVar "n" = some (.int (Int.ofNat n))) := by
  intro n
  induction n with
  | zero =>
      intro heap nextAddr
      refine ⟨?_, ?_⟩
      · refine ⟨parityState heap nextAddr 0, ?_, ?_⟩
        · have hcond :
              evalExpr (.binop .eq (.var "n") (.intLit 0)) (parityState heap nextAddr 0) =
                some (.int 1) := by
            simpa [parityState, evalExpr, evalStaticExpr, CState.lookupVar] using
              (show evalBinOp .eq (.int 0) (.int 0) = some (.int 1) by
                rfl)
          have hret :
              evalExpr (.intLit 1) (parityState heap nextAddr 0) = some (.int 1) := by
            simp [evalExpr, evalStaticExpr]
          simp [evenRet, show 3 * 0 + 2 = 1 + 1 by decide, isEvenBody, execStmtRec, hcond, hret, isTruthy]
        · simp [parityState, CState.lookupVar]
      · refine ⟨parityState heap nextAddr 0, ?_, ?_⟩
        · have hcond :
              evalExpr (.binop .eq (.var "n") (.intLit 0)) (parityState heap nextAddr 0) =
                some (.int 1) := by
            simpa [parityState, evalExpr, evalStaticExpr, CState.lookupVar] using
              (show evalBinOp .eq (.int 0) (.int 0) = some (.int 1) by
                rfl)
          have hret :
              evalExpr (.intLit 0) (parityState heap nextAddr 0) = some (.int 0) := by
            simp [evalExpr, evalStaticExpr]
          simp [oddRet, show 3 * 0 + 2 = 1 + 1 by decide, isOddBody, execStmtRec, hcond, hret, isTruthy]
        · simp [parityState, CState.lookupVar]
  | succ n ih =>
      intro heap nextAddr
      rcases ih heap nextAddr with
        ⟨⟨stEvenRec, hEvenRec, hEvenLookup⟩, ⟨stOddRec, hOddRec, hOddLookup⟩⟩
      let st := parityState heap nextAddr (n + 1)
      have hfuelCall : 3 * (n + 1) = 3 * n + 2 + 1 := by omega
      have hfuelBody : 3 * (n + 1) + 2 = (3 * (n + 1) + 1) + 1 := by omega
      have hcond :
          evalExpr (.binop .eq (.var "n") (.intLit 0)) st = some (.int 0) := by
        simpa [st, parityState, evalExpr, evalStaticExpr, CState.lookupVar] using
          (show evalBinOp .eq (.int (Int.ofNat (n + 1))) (.int 0) = some (.int 0) by
            change some (CVal.int (if ((n : Int) + 1) = 0 then 1 else 0)) = some (CVal.int 0)
            have hsucc : ((n : Int) + 1) ≠ 0 := by omega
            simp [hsucc])
      have harg :
          evalExpr (.binop .sub (.var "n") (.intLit 1)) st = some (.int (Int.ofNat n)) := by
        simpa [st, parityState, evalExpr, evalStaticExpr, CState.lookupVar] using
          (show evalBinOp .sub (.int (Int.ofNat (n + 1))) (.int 1) = some (.int (Int.ofNat n)) by
            change some (CVal.int (((n : Int) + 1) - 1)) = some (CVal.int (n : Int))
            have hsub : (((n : Int) + 1) - 1) = (n : Int) := by omega
            simp [hsub])
      have hargs :
          evalArgs [(.binop .sub (.var "n") (.intLit 1))] st = some [.int (Int.ofNat n)] := by
        simp [evalArgs, harg]
      have hEvenCall :
          execCallRec parityFunEnv (3 * (n + 1)) "isEven"
              [(.binop .sub (.var "n") (.intLit 1))] st =
            some (evenRet n, restoreCallerState st stEvenRec) := by
        let k : ExecResult → Option (CVal × CState) := fun res =>
          match res with
          | .returned ret callee => some (ret, restoreCallerState st callee)
          | .normal callee => some (.undef, restoreCallerState st callee)
        rw [hfuelCall]
        rw [execCallRec, parityFunEnv, hargs]
        simp [evenSpec, st, parityState, callEntryState, bindCallEnv]
        have hbind := congrArg (fun x => x.bind k) hEvenRec
        simpa [parityState, k] using hbind
      have hOddCall :
          execCallRec parityFunEnv (3 * (n + 1)) "isOdd"
              [(.binop .sub (.var "n") (.intLit 1))] st =
            some (oddRet n, restoreCallerState st stOddRec) := by
        let k : ExecResult → Option (CVal × CState) := fun res =>
          match res with
          | .returned ret callee => some (ret, restoreCallerState st callee)
          | .normal callee => some (.undef, restoreCallerState st callee)
        rw [hfuelCall]
        rw [execCallRec, parityFunEnv, hargs]
        simp [oddSpec, st, parityState, callEntryState, bindCallEnv]
        have hbind := congrArg (fun x => x.bind k) hOddRec
        simpa [parityState, k] using hbind
      have hEvenLookupN :
          (restoreCallerState st stEvenRec).lookupVar "n" = some (.int (Int.ofNat (n + 1))) := by
        simp [restoreCallerState, st, parityState, CState.lookupVar]
      have hOddLookupN :
          (restoreCallerState st stOddRec).lookupVar "n" = some (.int (Int.ofNat (n + 1))) := by
        simp [restoreCallerState, st, parityState, CState.lookupVar]
      refine ⟨?_, ?_⟩
      · refine ⟨restoreCallerState st stOddRec, ?_, hOddLookupN⟩
        let kRet : CVal × CState → Option ExecResult := fun vr =>
          some (.returned vr.1 vr.2)
        rw [hfuelBody]
        simp [isEvenBody, execStmtRec]
        rw [hcond]
        have hbind := congrArg (fun x => x.bind kRet) hOddCall
        simpa [kRet, isTruthy, evenRet_succ] using hbind
      · refine ⟨restoreCallerState st stEvenRec, ?_, hEvenLookupN⟩
        let kRet : CVal × CState → Option ExecResult := fun vr =>
          some (.returned vr.1 vr.2)
        rw [hfuelBody]
        simp [isOddBody, execStmtRec]
        rw [hcond]
        have hbind := congrArg (fun x => x.bind kRet) hEvenCall
        simpa [kRet, isTruthy, oddRet_succ] using hbind

theorem isEven_executes (n : Nat) (heap : Heap) (nextAddr : Nat) :
    ∃ st',
      execStmtRec parityFunEnv (3 * n + 2) isEvenBody (parityState heap nextAddr n) =
        some (.returned (evenRet n) st') ∧
      st'.lookupVar "n" = some (.int (Int.ofNat n)) := by
  exact (mutual_recursion_executes n heap nextAddr).1

theorem isOdd_executes (n : Nat) (heap : Heap) (nextAddr : Nat) :
    ∃ st',
      execStmtRec parityFunEnv (3 * n + 2) isOddBody (parityState heap nextAddr n) =
        some (.returned (oddRet n) st') ∧
      st'.lookupVar "n" = some (.int (Int.ofNat n)) := by
  exact (mutual_recursion_executes n heap nextAddr).2

def parityFunEnv_soundRec : FunEnvSoundRec parityFunEnv := by
  refine ⟨parityMeasure, ?_⟩
  intro fname spec hlookup st hpre
  by_cases he : fname = "isEven"
  · subst he
    have hspec : some evenSpec = some spec := by simpa [parityFunEnv] using hlookup
    injection hspec with hEq
    subst hEq
    rcases hpre with ⟨heap, nextAddr, n, rfl⟩
    rcases isEven_executes n heap nextAddr with ⟨st', hexec, hlookupN⟩
    refine ⟨evenRet n, st', ?_, ?_⟩
    simpa [parity_measure_even_state] using hexec
    exact ⟨n, hlookupN, rfl⟩
  · by_cases ho : fname = "isOdd"
    · subst ho
      have hspec : some oddSpec = some spec := by simpa [parityFunEnv, he] using hlookup
      injection hspec with hEq
      subst hEq
      rcases hpre with ⟨heap, nextAddr, n, rfl⟩
      rcases isOdd_executes n heap nextAddr with ⟨st', hexec, hlookupN⟩
      refine ⟨oddRet n, st', ?_, ?_⟩
      simpa [parity_measure_odd_state] using hexec
      exact ⟨n, hlookupN, rfl⟩
    · simp [parityFunEnv] at hlookup

theorem isEven_xapp_smoke (n : Nat) (heap : Heap) (nextAddr : Nat) :
    swpCall parityFunEnv "isEven" [.var "n"] (fun _ _ => True)
      (parityState heap nextAddr n) := by
  apply swpCall_intro (funEnv := parityFunEnv) (fname := "isEven")
    (args := [.var "n"]) (spec := evenSpec)
    (vals := [.int (Int.ofNat n)]) (Q := fun _ _ => True)
  · rfl
  · simp [evalArgs, parityState, evalExpr, evalStaticExpr, CState.lookupVar]
  · simp [evenSpec]
  · exact ⟨heap, nextAddr, n, even_entry_state_same heap nextAddr n⟩
  · intro _ _ _
    trivial

theorem isOdd_xapp_smoke (n : Nat) (heap : Heap) (nextAddr : Nat) :
    swpCall parityFunEnv "isOdd" [.var "n"] (fun _ _ => True)
      (parityState heap nextAddr n) := by
  apply swpCall_intro (funEnv := parityFunEnv) (fname := "isOdd")
    (args := [.var "n"]) (spec := oddSpec)
    (vals := [.int (Int.ofNat n)]) (Q := fun _ _ => True)
  · rfl
  · simp [evalArgs, parityState, evalExpr, evalStaticExpr, CState.lookupVar]
  · simp [oddSpec]
  · exact ⟨heap, nextAddr, n, odd_entry_state_same heap nextAddr n⟩
  · intro _ _ _
    trivial

end HeytingLean.LeanCP.Examples
