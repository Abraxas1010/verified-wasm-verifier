import HeytingLean.LeanCP.RealWorld.Support
import HeytingLean.LeanCP.VCG.SWhile
import HeytingLean.LeanCP.Core.VarLemmas

namespace HeytingLean.LeanCP.RealWorld

open HeytingLean.LeanCP

set_option linter.unnecessarySimpa false

def strnlenCond : CExpr :=
  .binop .ne (.deref (.var "s")) (.intLit 0)

def strnlenLoopBody : CStmt :=
  .seq
    (.assign (.var "s") (.binop .add (.var "s") (.intLit 1)))
    (.assign (.var "len") (.binop .add (.var "len") (.intLit 1)))

def strnlenFinal : CStmt :=
  .ite (.binop .lt (.var "len") (.var "n"))
    (.ret (.var "len"))
    (.ret (.var "n"))

def strnlenBody : CStmt :=
  .seq (.assign (.var "len") (.intLit 0))
    (.seq (.whileInv strnlenCond HProp.htrue strnlenLoopBody) strnlenFinal)

def strnlenInv (chars : List Int) (base n : Nat) : SProp := fun st =>
  ∃ done rest,
    chars = done ++ rest ∧
    st.lookupVar "s" = some (CVal.ptrAddr ((base + done.length) : PtrVal)) ∧
    st.lookupVar "n" = some (.int (Int.ofNat n)) ∧
    st.lookupVar "len" = some (.int (Int.ofNat done.length)) ∧
    stringAt_s base chars st

def strnlenLoopPost (chars : List Int) (base n : Nat) : CVal → SProp := fun _ st =>
  st.lookupVar "n" = some (.int (Int.ofNat n)) ∧
  st.lookupVar "len" = some (.int (Int.ofNat chars.length)) ∧
  stringAt_s base chars st

private theorem strnlen_loopFree : LoopFree strnlenLoopBody := by
  simp [strnlenLoopBody, LoopFree]

private theorem strnlen_noReturn : NoReturn strnlenLoopBody := by
  simp [strnlenLoopBody, NoReturn]

private theorem strnlen_loop_from_state
    (chars done rest : List Int) (base n : Nat) (st : CState)
    (hchars : chars = done ++ rest)
    (hs : st.lookupVar "s" = some (CVal.ptrAddr ((base + done.length) : PtrVal)))
    (hn : st.lookupVar "n" = some (.int (Int.ofNat n)))
    (hlen : st.lookupVar "len" = some (.int (Int.ofNat done.length)))
    (hstring : stringAt_s base chars st)
    (hnz : ∀ (i : Nat) (c : Int), chars[i]? = some c → c ≠ 0) :
    swhileWP rest.length strnlenCond (strnlenInv chars base n) strnlenLoopBody
      (strnlenLoopPost chars base n) st := by
  induction rest generalizing done st with
  | nil =>
      have hInv : strnlenInv chars base n st := by
        exact ⟨done, [], hchars, hs, hn, hlen, hstring⟩
      have hdone : chars = done := by
        simpa using hchars
      have hReadZero : st.heap.read (base + done.length) = some (.int 0) := by
        exact hstring done.length 0 (by simpa [hdone])
      have hReadPtrZero : st.readPtr (base + done.length : PtrVal) = some (.int 0) := by
        simpa [hReadZero] using CState.readPtr_block0 st (base + done.length) (base + done.length)
      have hEvalS : evalExpr (.var "s") st = some (CVal.ptrAddr ((base + done.length) : PtrVal)) := by
        simpa [evalExpr, evalStaticExpr] using hs
      have hEvalDeref : evalExpr (.deref (.var "s")) st = some (.int 0) := by
        simpa [evalExpr, evalStaticExpr, hEvalS] using hReadPtrZero
      have hCond : evalExpr strnlenCond st = some (.int 0) := by
        simpa [strnlenCond, evalExpr, evalStaticExpr, hEvalDeref] using
          (show evalBinOp .ne (.int 0) (.int 0) = some (.int 0) by
            change some (CVal.int (if (0 : Int) ≠ 0 then 1 else 0)) = some (CVal.int 0)
            simp)
      have hPost : strnlenLoopPost chars base n CVal.undef st := by
        refine ⟨hn, ?_, hstring⟩
        simpa [hdone] using hlen
      simpa [swhileWP, hCond, isTruthy] using And.intro hInv hPost
  | cons h tail ih =>
      have hInv : strnlenInv chars base n st := by
        exact ⟨done, h :: tail, hchars, hs, hn, hlen, hstring⟩
      have hHeadIndex : chars[done.length]? = some h := by
        rw [hchars]
        simp
      have hneZero : h ≠ 0 := hnz done.length h hHeadIndex
      have hReadHead : st.heap.read (base + done.length) = some (.int h) := by
        exact hstring done.length h (by simpa [hchars])
      have hReadPtrHead : st.readPtr ((base + done.length) : PtrVal) = some (.int h) := by
        simpa [hReadHead] using CState.readPtr_block0 st (base + done.length) (base + done.length)
      have hEvalS : evalExpr (.var "s") st = some (CVal.ptrAddr ((base + done.length) : PtrVal)) := by
        simpa [evalExpr, evalStaticExpr] using hs
      have hEvalDeref : evalExpr (.deref (.var "s")) st = some (.int h) := by
        simpa [evalExpr, evalStaticExpr, hEvalS] using hReadPtrHead
      have hCond : evalExpr strnlenCond st = some (.int 1) := by
        simpa [strnlenCond, evalExpr, evalStaticExpr, hEvalDeref] using
          (show evalBinOp .ne (.int h) (.int 0) = some (.int 1) by
            change some (CVal.int (if h ≠ 0 then 1 else 0)) = some (CVal.int 1)
            simp [hneZero])
      have hEvalNextS :
          evalExpr (.binop .add (.var "s") (.intLit 1)) st =
            some (CVal.ptrAddr { block := 0, offset := Int.ofNat (base + (done ++ [h]).length) }) := by
        simpa [evalExpr, evalStaticExpr, hs] using
          (show evalBinOp .add (CVal.ptrAddr ((base + done.length : Nat) : PtrVal)) (.int 1) =
              some (CVal.ptrAddr { block := 0, offset := Int.ofNat (base + (done ++ [h]).length) }) by
            change
              (if 0 ≤ (1 : Int) then
                some (CVal.ptrAddr { block := 0, offset := Int.ofNat (base + done.length) + 1 })
              else none) =
                some (CVal.ptrAddr { block := 0, offset := Int.ofNat (base + (done ++ [h]).length) })
            simpa [Int.add_assoc])
      let st1 := st.updateVar "s"
        (CVal.ptrAddr { block := 0, offset := Int.ofNat (base + (done ++ [h]).length) })
      let st2 := st1.updateVar "len" (.int (Int.ofNat (done.length + 1)))
      have hs1 :
          st1.lookupVar "s" = some
            (CVal.ptrAddr { block := 0, offset := Int.ofNat (base + (done ++ [h]).length) }) := by
        simpa [st1] using lookupVar_updateVar_eq st "s"
          (CVal.ptrAddr { block := 0, offset := Int.ofNat (base + (done ++ [h]).length) })
      have hlen1 : st1.lookupVar "len" = some (.int (Int.ofNat done.length)) := by
        calc
          st1.lookupVar "len" = st.lookupVar "len" := by
            simpa [st1] using lookupVar_updateVar_ne st "s" "len"
              (CVal.ptrAddr { block := 0, offset := Int.ofNat (base + (done ++ [h]).length) })
              (by decide : "len" ≠ "s")
          _ = some (.int (Int.ofNat done.length)) := hlen
      have hn1 : st1.lookupVar "n" = some (.int (Int.ofNat n)) := by
        calc
          st1.lookupVar "n" = st.lookupVar "n" := by
            simpa [st1] using lookupVar_updateVar_ne st "s" "n"
              (CVal.ptrAddr { block := 0, offset := Int.ofNat (base + (done ++ [h]).length) })
              (by decide : "n" ≠ "s")
          _ = some (.int (Int.ofNat n)) := hn
      have hs2 :
          st2.lookupVar "s" = some
            (CVal.ptrAddr { block := 0, offset := Int.ofNat (base + (done ++ [h]).length) }) := by
        calc
          st2.lookupVar "s" = st1.lookupVar "s" := by
            simpa [st2] using lookupVar_updateVar_ne st1 "len" "s" (.int (Int.ofNat (done.length + 1)))
              (by decide : "s" ≠ "len")
          _ = some
                (CVal.ptrAddr { block := 0, offset := Int.ofNat (base + (done ++ [h]).length) }) := hs1
      have hn2 : st2.lookupVar "n" = some (.int (Int.ofNat n)) := by
        calc
          st2.lookupVar "n" = st1.lookupVar "n" := by
            simpa [st2] using lookupVar_updateVar_ne st1 "len" "n" (.int (Int.ofNat (done.length + 1)))
              (by decide : "n" ≠ "len")
          _ = some (.int (Int.ofNat n)) := hn1
      have hlen2 : st2.lookupVar "len" = some (.int (Int.ofNat ((done ++ [h]).length))) := by
        simpa [st2] using lookupVar_updateVar_eq st1 "len" (.int (Int.ofNat (done.length + 1)))
      have hstring1 : stringAt_s base chars st1 := by
        simpa [st1] using (stringAt_s_updateVar base chars st "s"
          (CVal.ptrAddr { block := 0, offset := Int.ofNat (base + (done ++ [h]).length) })).2 hstring
      have hstring2 : stringAt_s base chars st2 := by
        simpa [st2] using (stringAt_s_updateVar base chars st1 "len" (.int (Int.ofNat (done.length + 1)))).2 hstring1
      have hchars2 : chars = (done ++ [h]) ++ tail := by
        simpa [List.append_assoc] using hchars
      have hLoop2 :
          swhileWP tail.length strnlenCond (strnlenInv chars base n) strnlenLoopBody
            (strnlenLoopPost chars base n) st2 := by
        exact ih (done ++ [h]) st2 hchars2 hs2 hn2 hlen2 hstring2
      have hEvalLenInc :
          evalExpr (.binop .add (.var "len") (.intLit 1)) st1 =
            some (.int (Int.ofNat (done.length + 1))) := by
        simpa [evalExpr, evalStaticExpr, hlen1] using
          (show evalBinOp .add (.int (Int.ofNat done.length)) (.int 1) =
              some (.int (Int.ofNat (done.length + 1))) by
            change some (CVal.int (Int.ofNat done.length + 1)) =
              some (CVal.int (Int.ofNat (done.length + 1)))
            simp)
      have hAssignLen :
          swp (.assign (.var "len") (.binop .add (.var "len") (.intLit 1)))
            (fun _ => swhileWP tail.length strnlenCond (strnlenInv chars base n) strnlenLoopBody
              (strnlenLoopPost chars base n)) st1 := by
        simpa [swp, hEvalLenInc, st2] using hLoop2
      have hBody :
          swp strnlenLoopBody
            (fun _ => swhileWP tail.length strnlenCond (strnlenInv chars base n) strnlenLoopBody
              (strnlenLoopPost chars base n)) st := by
        simpa [strnlenLoopBody, swp, hEvalNextS, st1] using hAssignLen
      simpa [swhileWP, hCond] using And.intro hInv hBody

theorem strnlen_correct (chars : List Int) (base n : Nat) :
    ∀ st,
      st.lookupVar "s" = some (CVal.ptrAddr (base : PtrVal)) →
      st.lookupVar "n" = some (.int (Int.ofNat n)) →
      stringAt_s base chars st →
      (∀ (i : Nat) (c : Int), chars[i]? = some c → c ≠ 0) →
      ∃ st',
        execStmt (swhileFuel strnlenLoopBody chars.length + 2) strnlenBody st =
          some (.returned (.int (Int.ofNat (Nat.min chars.length n))) st') ∧
        stringAt_s base chars st' := by
  intro st hs hn hstring hnz
  let st1 := st.updateVar "len" (.int 0)
  have hs1 : st1.lookupVar "s" = some (CVal.ptrAddr (base : PtrVal)) := by
    calc
      st1.lookupVar "s" = st.lookupVar "s" := by
        simpa [st1] using lookupVar_updateVar_ne st "len" "s" (.int 0) (by decide : "s" ≠ "len")
      _ = some (CVal.ptrAddr (base : PtrVal)) := hs
  have hn1 : st1.lookupVar "n" = some (.int (Int.ofNat n)) := by
    calc
      st1.lookupVar "n" = st.lookupVar "n" := by
        simpa [st1] using lookupVar_updateVar_ne st "len" "n" (.int 0) (by decide : "n" ≠ "len")
      _ = some (.int (Int.ofNat n)) := hn
  have hlen1 : st1.lookupVar "len" = some (.int 0) := by
    simpa [st1] using lookupVar_updateVar_eq st "len" (.int 0)
  have hstring1 : stringAt_s base chars st1 := by
    simpa [st1] using (stringAt_s_updateVar base chars st "len" (.int 0)).2 hstring
  have hLoopWP :
      swhileWP chars.length strnlenCond (strnlenInv chars base n) strnlenLoopBody
        (strnlenLoopPost chars base n) st1 := by
    exact strnlen_loop_from_state chars [] chars base n st1 (by simp) hs1 hn1 hlen1 hstring1 hnz
  have hLoopExec :
      ∃ stLoop,
        execStmt (swhileFuel strnlenLoopBody chars.length)
          (.whileInv strnlenCond HProp.htrue strnlenLoopBody) st1 =
            some (.normal stLoop) ∧
        strnlenLoopPost chars base n CVal.undef stLoop := by
    exact swhileWP_sound strnlenCond (strnlenInv chars base n) HProp.htrue strnlenLoopBody
      strnlen_loopFree strnlen_noReturn hLoopWP
  rcases hLoopExec with ⟨stLoop, hExecLoop, hPostLoop⟩
  rcases hPostLoop with ⟨hnLoop, hlenLoop, hstringLoop⟩
  let loopFuel := swhileFuel strnlenLoopBody chars.length
  have hCondFinal :
      evalExpr (.binop .lt (.var "len") (.var "n")) stLoop =
        some (.int (if chars.length < n then 1 else 0)) := by
    by_cases hlt : chars.length < n
    · simpa [evalExpr, evalStaticExpr, hlenLoop, hnLoop, hlt, Int.ofNat_lt.mpr hlt] using
        (show evalBinOp .lt (.int (Int.ofNat chars.length)) (.int (Int.ofNat n)) =
            some (.int 1) by
          change some (CVal.int (if Int.ofNat chars.length < Int.ofNat n then 1 else 0)) =
            some (CVal.int 1)
          simp [Int.ofNat_lt.mpr hlt])
    · have hge : n ≤ chars.length := Nat.le_of_not_gt hlt
      have hnotlt : ¬ Int.ofNat chars.length < Int.ofNat n := by
        exact Int.not_lt.mpr (Int.ofNat_le.mpr hge)
      simpa [evalExpr, evalStaticExpr, hlenLoop, hnLoop, hlt] using
        (show evalBinOp .lt (.int (Int.ofNat chars.length)) (.int (Int.ofNat n)) =
            some (.int 0) by
          change some (CVal.int (if Int.ofNat chars.length < Int.ofNat n then 1 else 0)) =
            some (CVal.int 0)
          simp [hnotlt])
  have hFinalExec :
      execStmt loopFuel strnlenFinal stLoop =
        some (.returned (.int (Int.ofNat (Nat.min chars.length n))) stLoop) := by
    cases hFuel : loopFuel with
    | zero =>
        simp [loopFuel, swhileFuel] at hFuel
    | succ fuel' =>
        by_cases hlt : chars.length < n
        · have hCond1 :
              evalExpr (.binop .lt (.var "len") (.var "n")) stLoop = some (.int 1) := by
              simpa [hlt] using hCondFinal
          have hMinNat : Nat.min chars.length n = chars.length :=
            Nat.min_eq_left (Nat.le_of_lt hlt)
          have hRetLen :
              execStmt fuel' (.ret (.var "len")) stLoop =
                some (.returned (.int (Int.ofNat chars.length)) stLoop) := by
            cases fuel' with
            | zero =>
                have : False := by
                  simp [loopFuel, swhileFuel, strnlenLoopBody, stmtDepth] at hFuel
                exact False.elim this
            | succ fuel'' =>
                simp [execStmt, evalExpr, evalStaticExpr, hlenLoop]
          simpa [strnlenFinal, execStmt, hCond1, isTruthy, hMinNat] using hRetLen
        · have hge : n ≤ chars.length := Nat.le_of_not_gt hlt
          have hCond0 :
              evalExpr (.binop .lt (.var "len") (.var "n")) stLoop = some (.int 0) := by
              simpa [hlt] using hCondFinal
          have hMinNat : Nat.min chars.length n = n := Nat.min_eq_right hge
          have hRetN :
              execStmt fuel' (.ret (.var "n")) stLoop =
                some (.returned (.int (Int.ofNat n)) stLoop) := by
            cases fuel' with
            | zero =>
                have : False := by
                  simp [loopFuel, swhileFuel, strnlenLoopBody, stmtDepth] at hFuel
                exact False.elim this
            | succ fuel'' =>
                simp [execStmt, evalExpr, evalStaticExpr, hnLoop]
          simpa [strnlenFinal, execStmt, hCond0, isTruthy, hMinNat] using hRetN
  have hExecInner :
      execStmt (loopFuel + 1)
        (.seq (.whileInv strnlenCond HProp.htrue strnlenLoopBody) strnlenFinal) st1 =
          some (.returned (.int (Int.ofNat (Nat.min chars.length n))) stLoop) := by
    simp [execStmt]
    rw [hExecLoop]
    simpa [loopFuel] using hFinalExec
  refine ⟨stLoop, ?_, hstringLoop⟩
  change execStmt (Nat.succ (loopFuel + 1)) strnlenBody st =
    some (.returned (.int (Int.ofNat (Nat.min chars.length n))) stLoop)
  simpa [strnlenBody, execStmt, st1] using hExecInner

end HeytingLean.LeanCP.RealWorld
