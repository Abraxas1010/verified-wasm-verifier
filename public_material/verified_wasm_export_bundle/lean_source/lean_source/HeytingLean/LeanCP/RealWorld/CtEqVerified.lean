import HeytingLean.LeanCP.RealWorld.Support
import HeytingLean.LeanCP.VCG.SWhile
import HeytingLean.LeanCP.Core.VarLemmas
import Mathlib.Tactic

namespace HeytingLean.LeanCP.RealWorld

open HeytingLean.LeanCP

set_option linter.unnecessarySimpa false

/-- Count pointwise mismatches between two same-length byte buffers. -/
def neqCount : List Int → List Int → Nat
  | [], [] => 0
  | x :: xs, y :: ys => (if x = y then 0 else 1) + neqCount xs ys
  | _ :: xs, [] => xs.length + 1
  | [], _ :: ys => ys.length + 1

theorem neqCount_eq_zero_iff {xs ys : List Int} :
    neqCount xs ys = 0 ↔ xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => simp [neqCount]
      | cons y ys => simp [neqCount]
  | cons x xs ih =>
      cases ys with
      | nil => simp [neqCount]
      | cons y ys =>
          by_cases hxy : x = y
          · subst hxy
            simp [neqCount, ih]
          · simp [neqCount, hxy]

def ctEqCond : CExpr :=
  .binop .lt (.var "i") (.var "n")

def ctEqCellA : CExpr :=
  .deref (.binop .add (.var "a") (.var "i"))

def ctEqCellB : CExpr :=
  .deref (.binop .add (.var "b") (.var "i"))

/-- Branch-free loop body: mismatch accumulation happens through arithmetic, not `ite`. -/
def ctEqLoopBody : CStmt :=
  .seq
    (.assign (.var "m") (.binop .add (.var "m") (.binop .ne ctEqCellA ctEqCellB)))
    (.assign (.var "i") (.binop .add (.var "i") (.intLit 1)))

def ctEqBody : CStmt :=
  .seq (.assign (.var "m") (.intLit 0))
    (.seq (.assign (.var "i") (.intLit 0))
      (.seq (.whileInv ctEqCond HProp.htrue ctEqLoopBody)
        (.ret (.binop .eq (.var "m") (.intLit 0)))))

/-- Syntactic control-flow audit for the current constant-time surface. -/
def NoBranch : CStmt → Prop
  | .skip => True
  | .assign _ _ => True
  | .seq s₁ s₂ => NoBranch s₁ ∧ NoBranch s₂
  | .ite _ _ _ => False
  | .whileInv _ _ body => NoBranch body
  | .block _ body => NoBranch body
  | .switch _ _ _ _ => False
  | .forLoop init _ step body => NoBranch init ∧ NoBranch step ∧ NoBranch body
  | .break => True
  | .continue => True
  | .ret _ => True
  | .alloc _ _ => True
  | .free _ _ => True
  | .decl _ _ => True

theorem ctEq_noBranch : NoBranch ctEqBody := by
  simp [NoBranch, ctEqBody, ctEqLoopBody]

def ctEqInv (aBase bBase : Nat) (xs ys : List Int) : SProp := fun st =>
  ∃ doneXs restXs doneYs restYs,
    xs = doneXs ++ restXs ∧
    ys = doneYs ++ restYs ∧
    xs.length = ys.length ∧
    doneXs.length = doneYs.length ∧
    st.lookupVar "a" = some (CVal.ptrAddr (aBase : PtrVal)) ∧
    st.lookupVar "b" = some (CVal.ptrAddr (bBase : PtrVal)) ∧
    st.lookupVar "n" = some (.int (Int.ofNat xs.length)) ∧
    st.lookupVar "i" = some (.int (Int.ofNat doneXs.length)) ∧
    st.lookupVar "m" = some (.int (Int.ofNat (neqCount doneXs doneYs))) ∧
    bytesAt_s aBase xs st ∧
    bytesAt_s bBase ys st

def ctEqLoopPost (aBase bBase : Nat) (xs ys : List Int) : CVal → SProp := fun _ st =>
  st.lookupVar "m" = some (.int (Int.ofNat (neqCount xs ys))) ∧
  bytesAt_s aBase xs st ∧
  bytesAt_s bBase ys st

private theorem ctEq_loopFree : LoopFree ctEqLoopBody := by
  simp [ctEqLoopBody, LoopFree]

private theorem ctEq_noReturn : NoReturn ctEqLoopBody := by
  simp [ctEqLoopBody, NoReturn]

private theorem neqCount_append_single
    (doneXs doneYs : List Int) (hLen : doneXs.length = doneYs.length) (x y : Int) :
    neqCount (doneXs ++ [x]) (doneYs ++ [y]) =
      neqCount doneXs doneYs + (if x = y then 0 else 1) := by
  induction doneXs generalizing doneYs with
  | nil =>
      cases doneYs with
      | nil => by_cases hxy : x = y <;> simp [neqCount, hxy]
      | cons a rest => simp at hLen
  | cons h t ih =>
      cases doneYs with
      | nil => simp at hLen
      | cons a rest =>
          have hLen' : t.length = rest.length := by simpa using hLen
          by_cases hha : h = a
          · subst hha
            simp [neqCount, ih rest hLen']
          · simp [neqCount, hha, ih rest hLen', Nat.add_assoc]

private theorem ctEq_loop_from_state
    (aBase bBase : Nat)
    (xs doneXs restXs ys doneYs restYs : List Int)
    (st : CState)
    (hXs : xs = doneXs ++ restXs)
    (hYs : ys = doneYs ++ restYs)
    (hLen : xs.length = ys.length)
    (hDoneLen : doneXs.length = doneYs.length)
    (hAPtr : st.lookupVar "a" = some (CVal.ptrAddr (aBase : PtrVal)))
    (hBPtr : st.lookupVar "b" = some (CVal.ptrAddr (bBase : PtrVal)))
    (hN : st.lookupVar "n" = some (.int (Int.ofNat xs.length)))
    (hI : st.lookupVar "i" = some (.int (Int.ofNat doneXs.length)))
    (hM : st.lookupVar "m" = some (.int (Int.ofNat (neqCount doneXs doneYs))))
    (hXsBytes : bytesAt_s aBase xs st)
    (hYsBytes : bytesAt_s bBase ys st) :
    swhileWP restXs.length ctEqCond (ctEqInv aBase bBase xs ys)
      ctEqLoopBody (ctEqLoopPost aBase bBase xs ys) st := by
  induction restXs generalizing doneXs ys doneYs restYs st with
  | nil =>
      have hRestYsNil : restYs = [] := by
        have : restYs.length = 0 := by
          have hLen' := hLen
          rw [hXs, hYs] at hLen'
          simp at hLen'
          omega
        exact List.length_eq_zero_iff.mp this
      subst hRestYsNil
      have hInv : ctEqInv aBase bBase xs ys st := by
        exact ⟨doneXs, [], doneYs, [], hXs, hYs, hLen, hDoneLen,
          hAPtr, hBPtr, hN, hI, hM, hXsBytes, hYsBytes⟩
      have hCond : evalExpr ctEqCond st = some (.int 0) := by
        simpa [ctEqCond, evalExpr, evalStaticExpr, hI, hN, hXs] using
          (show evalBinOp .lt (.int (Int.ofNat doneXs.length))
              (.int (Int.ofNat doneXs.length)) = some (.int 0) by
            change some (CVal.int (if Int.ofNat doneXs.length < Int.ofNat doneXs.length then 1 else 0)) =
              some (CVal.int 0)
            simp)
      have hPost : ctEqLoopPost aBase bBase xs ys CVal.undef st := by
        refine ⟨?_, hXsBytes, hYsBytes⟩
        simpa [hXs, hYs] using hM
      simpa [swhileWP, hCond, isTruthy] using And.intro hInv hPost
  | cons nextX tailXs ih =>
      cases restYs with
      | nil =>
          have : False := by
            have hLen' := hLen
            rw [hXs, hYs] at hLen'
            simp at hLen'
            omega
          exact False.elim this
      | cons nextY tailYs =>
          have hInv : ctEqInv aBase bBase xs ys st := by
            exact ⟨doneXs, nextX :: tailXs, doneYs, nextY :: tailYs,
              hXs, hYs, hLen, hDoneLen, hAPtr, hBPtr, hN, hI, hM, hXsBytes, hYsBytes⟩
          have hLt : doneXs.length < xs.length := by
            rw [hXs]
            simp
          have hCond : evalExpr ctEqCond st = some (.int 1) := by
            simpa [ctEqCond, evalExpr, evalStaticExpr, hI, hN] using
              (show evalBinOp .lt (.int (Int.ofNat doneXs.length))
                  (.int (Int.ofNat xs.length)) = some (.int 1) by
                change some (CVal.int (if Int.ofNat doneXs.length < Int.ofNat xs.length then 1 else 0)) =
                  some (CVal.int 1)
                simp [Int.ofNat_lt.mpr hLt])
          have hXsGet : xs[doneXs.length]? = some nextX := by
            rw [hXs]
            simp
          have hYsGet : ys[doneYs.length]? = some nextY := by
            rw [hYs]
            simp
          have hIYs : st.lookupVar "i" = some (.int (Int.ofNat doneYs.length)) := by
            simpa [hDoneLen] using hI
          have hAPtrEval :
              evalExpr (.binop .add (.var "a") (.var "i")) st =
                some (CVal.ptrAddr ((aBase + doneXs.length) : PtrVal)) := by
            simpa [evalExpr, evalStaticExpr, hAPtr, hI] using
              (show evalBinOp .add (CVal.ptrAddr (aBase : PtrVal))
                  (.int (Int.ofNat doneXs.length)) =
                    some (CVal.ptrAddr ((aBase + doneXs.length) : PtrVal)) by
                change
                  (if 0 ≤ Int.ofNat doneXs.length then
                    some (CVal.ptrAddr { block := 0, offset := Int.ofNat aBase + Int.ofNat doneXs.length })
                  else none) = some (CVal.ptrAddr ((aBase + doneXs.length) : PtrVal))
                simp)
          have hBPtrEval :
              evalExpr (.binop .add (.var "b") (.var "i")) st =
                some (CVal.ptrAddr ((bBase + doneYs.length) : PtrVal)) := by
            simpa [evalExpr, evalStaticExpr, hBPtr, hIYs] using
              (show evalBinOp .add (CVal.ptrAddr (bBase : PtrVal))
                  (.int (Int.ofNat doneYs.length)) =
                    some (CVal.ptrAddr ((bBase + doneYs.length) : PtrVal)) by
                change
                  (if 0 ≤ Int.ofNat doneYs.length then
                    some (CVal.ptrAddr { block := 0, offset := Int.ofNat bBase + Int.ofNat doneYs.length })
                  else none) = some (CVal.ptrAddr ((bBase + doneYs.length) : PtrVal))
                simp)
          have hXsRead : st.heap.read (aBase + doneXs.length) = some (.int nextX) := by
            exact hXsBytes _ _ hXsGet
          have hYsRead : st.heap.read (bBase + doneYs.length) = some (.int nextY) := by
            exact hYsBytes _ _ hYsGet
          have hXsDeref : evalExpr ctEqCellA st = some (.int nextX) := by
            simpa [ctEqCellA, evalExpr, evalStaticExpr, hAPtrEval] using
              (CState.readPtr_block0 st (aBase + doneXs.length) (aBase + doneXs.length)).trans hXsRead
          have hYsDeref : evalExpr ctEqCellB st = some (.int nextY) := by
            simpa [ctEqCellB, evalExpr, evalStaticExpr, hBPtrEval] using
              (CState.readPtr_block0 st (bBase + doneYs.length) (bBase + doneYs.length)).trans hYsRead
          have hStaticMismatch :
              evalStaticExpr (.binop .ne ctEqCellA ctEqCellB) = none := by
            simp [ctEqCellA, ctEqCellB, evalStaticExpr]
          let mismatchFlag : Nat := if nextX = nextY then 0 else 1
          have hMismatchEval :
              evalExpr (.binop .ne ctEqCellA ctEqCellB) st =
                some (.int (Int.ofNat mismatchFlag)) := by
            by_cases hEq : nextX = nextY
            · subst hEq
              simpa [hStaticMismatch, mismatchFlag, evalExpr, hXsDeref, hYsDeref] using
                (show evalBinOp .ne (.int nextX) (.int nextX) = some (.int 0) by
                  change some (CVal.int (if nextX ≠ nextX then 1 else 0)) =
                    some (CVal.int 0)
                  simp)
            · simpa [hStaticMismatch, mismatchFlag, evalExpr, hXsDeref, hYsDeref, hEq] using
                (show evalBinOp .ne (.int nextX) (.int nextY) = some (.int 1) by
                  change some (CVal.int (if nextX ≠ nextY then 1 else 0)) =
                    some (CVal.int 1)
                  simp [hEq])
          let st1 := st.updateVar "m" (.int (Int.ofNat (neqCount doneXs doneYs + mismatchFlag)))
          have hM1 :
              st1.lookupVar "m" =
                some (.int (Int.ofNat (neqCount (doneXs ++ [nextX]) (doneYs ++ [nextY])))) := by
            by_cases hEq : nextX = nextY
            · subst nextY
              have hFlag : mismatchFlag = 0 := by simp [mismatchFlag]
              calc
                st1.lookupVar "m" = some (.int (Int.ofNat (neqCount doneXs doneYs + mismatchFlag))) := by
                  simp [st1]
                _ = some (.int (Int.ofNat (neqCount doneXs doneYs))) := by simp [hFlag]
                _ = some (.int (Int.ofNat (neqCount (doneXs ++ [nextX]) (doneYs ++ [nextX])))) := by
                  simp [neqCount_append_single, hDoneLen]
            · calc
                st1.lookupVar "m" = some (.int (Int.ofNat (neqCount doneXs doneYs + mismatchFlag))) := by
                  simp [st1]
                _ = some (.int (Int.ofNat (neqCount doneXs doneYs + 1))) := by simp [mismatchFlag, hEq]
                _ = some (.int (Int.ofNat (neqCount (doneXs ++ [nextX]) (doneYs ++ [nextY])))) := by
                  simp [neqCount_append_single, hDoneLen, hEq]
          have hAPtr1 : st1.lookupVar "a" = some (CVal.ptrAddr (aBase : PtrVal)) := by
            calc
              st1.lookupVar "a" = st.lookupVar "a" := by
                simpa [st1] using lookupVar_updateVar_ne st "m" "a"
                  (.int (Int.ofNat (neqCount doneXs doneYs + mismatchFlag))) (by decide : "a" ≠ "m")
              _ = some (CVal.ptrAddr (aBase : PtrVal)) := hAPtr
          have hBPtr1 : st1.lookupVar "b" = some (CVal.ptrAddr (bBase : PtrVal)) := by
            calc
              st1.lookupVar "b" = st.lookupVar "b" := by
                simpa [st1] using lookupVar_updateVar_ne st "m" "b"
                  (.int (Int.ofNat (neqCount doneXs doneYs + mismatchFlag))) (by decide : "b" ≠ "m")
              _ = some (CVal.ptrAddr (bBase : PtrVal)) := hBPtr
          have hN1 : st1.lookupVar "n" = some (.int (Int.ofNat xs.length)) := by
            calc
              st1.lookupVar "n" = st.lookupVar "n" := by
                simpa [st1] using lookupVar_updateVar_ne st "m" "n"
                  (.int (Int.ofNat (neqCount doneXs doneYs + mismatchFlag))) (by decide : "n" ≠ "m")
              _ = some (.int (Int.ofNat xs.length)) := hN
          have hI1 : st1.lookupVar "i" = some (.int (Int.ofNat doneXs.length)) := by
            calc
              st1.lookupVar "i" = st.lookupVar "i" := by
                simpa [st1] using lookupVar_updateVar_ne st "m" "i"
                  (.int (Int.ofNat (neqCount doneXs doneYs + mismatchFlag))) (by decide : "i" ≠ "m")
              _ = some (.int (Int.ofNat doneXs.length)) := hI
          let st2 := st1.updateVar "i" (.int (Int.ofNat (doneXs.length + 1)))
          have hDoneLen' : (doneXs ++ [nextX]).length = (doneYs ++ [nextY]).length := by
            simp [hDoneLen]
          have hAPtr2 : st2.lookupVar "a" = some (CVal.ptrAddr (aBase : PtrVal)) := by
            calc
              st2.lookupVar "a" = st1.lookupVar "a" := by
                simpa [st2] using lookupVar_updateVar_ne st1 "i" "a" (.int (Int.ofNat (doneXs.length + 1)))
                  (by decide : "a" ≠ "i")
              _ = some (CVal.ptrAddr (aBase : PtrVal)) := hAPtr1
          have hBPtr2 : st2.lookupVar "b" = some (CVal.ptrAddr (bBase : PtrVal)) := by
            calc
              st2.lookupVar "b" = st1.lookupVar "b" := by
                simpa [st2] using lookupVar_updateVar_ne st1 "i" "b" (.int (Int.ofNat (doneXs.length + 1)))
                  (by decide : "b" ≠ "i")
              _ = some (CVal.ptrAddr (bBase : PtrVal)) := hBPtr1
          have hN2 : st2.lookupVar "n" = some (.int (Int.ofNat xs.length)) := by
            calc
              st2.lookupVar "n" = st1.lookupVar "n" := by
                simpa [st2] using lookupVar_updateVar_ne st1 "i" "n" (.int (Int.ofNat (doneXs.length + 1)))
                  (by decide : "n" ≠ "i")
              _ = some (.int (Int.ofNat xs.length)) := hN1
          have hI2 : st2.lookupVar "i" = some (.int (Int.ofNat (doneXs.length + 1))) := by
            simpa [st2] using lookupVar_updateVar_eq st1 "i" (.int (Int.ofNat (doneXs.length + 1)))
          have hI2' : st2.lookupVar "i" = some (.int (Int.ofNat (doneXs ++ [nextX]).length)) := by
            simpa using hI2
          have hXsBytes2 : bytesAt_s aBase xs st2 := by
            simpa [st2, st1] using
              (bytesAt_s_updateVar aBase xs st1 "i" (.int (Int.ofNat (doneXs.length + 1)))).2
                ((bytesAt_s_updateVar aBase xs st "m" (.int (Int.ofNat (neqCount doneXs doneYs + mismatchFlag)))).2 hXsBytes)
          have hYsBytes2 : bytesAt_s bBase ys st2 := by
            simpa [st2, st1] using
              (bytesAt_s_updateVar bBase ys st1 "i" (.int (Int.ofNat (doneXs.length + 1)))).2
                ((bytesAt_s_updateVar bBase ys st "m" (.int (Int.ofNat (neqCount doneXs doneYs + mismatchFlag)))).2 hYsBytes)
          have hLoop2 :
              swhileWP tailXs.length ctEqCond (ctEqInv aBase bBase xs ys)
                ctEqLoopBody (ctEqLoopPost aBase bBase xs ys) st2 := by
            exact ih (doneXs ++ [nextX]) ys (doneYs ++ [nextY]) tailYs st2
              (by simpa [List.append_assoc] using hXs)
              (by simpa [List.append_assoc] using hYs)
              hLen hDoneLen' hAPtr2 hBPtr2 hN2 hI2' hM1 hXsBytes2 hYsBytes2
          have hEvalAcc :
              evalExpr (.binop .add (.var "m") (.binop .ne ctEqCellA ctEqCellB)) st =
                some (.int (Int.ofNat (neqCount doneXs doneYs + mismatchFlag))) := by
            simpa [evalExpr, evalStaticExpr, hM, hMismatchEval]
          have hEvalInc :
              evalExpr (.binop .add (.var "i") (.intLit 1)) st1 =
                some (.int (Int.ofNat (doneXs.length + 1))) := by
            simpa [evalExpr, evalStaticExpr, hI1] using
              (show evalBinOp .add (.int (Int.ofNat doneXs.length)) (.int 1) =
                  some (.int (Int.ofNat (doneXs.length + 1))) by
                change some (CVal.int (Int.ofNat doneXs.length + 1)) =
                  some (CVal.int (Int.ofNat (doneXs.length + 1)))
                simp)
          have hAssignI :
              swp (.assign (.var "i") (.binop .add (.var "i") (.intLit 1)))
                (fun _ => swhileWP tailXs.length ctEqCond (ctEqInv aBase bBase xs ys)
                  ctEqLoopBody (ctEqLoopPost aBase bBase xs ys)) st1 := by
            simpa [swp, hEvalInc, st2] using hLoop2
          have hAssignM :
              swp (.assign (.var "m") (.binop .add (.var "m") (.binop .ne ctEqCellA ctEqCellB)))
                (fun _ => swp (.assign (.var "i") (.binop .add (.var "i") (.intLit 1)))
                  (fun _ => swhileWP tailXs.length ctEqCond (ctEqInv aBase bBase xs ys)
                    ctEqLoopBody (ctEqLoopPost aBase bBase xs ys))) st := by
            simpa [swp, hEvalAcc, st1] using hAssignI
          have hBody :
              swp ctEqLoopBody
                (fun _ => swhileWP tailXs.length ctEqCond (ctEqInv aBase bBase xs ys)
                  ctEqLoopBody (ctEqLoopPost aBase bBase xs ys)) st := by
            simpa [ctEqLoopBody, swp] using hAssignM
          simpa [swhileWP, hCond] using And.intro hInv hBody

theorem ctEq_correct (aBase bBase : Nat) (xs ys : List Int)
    (hLen : xs.length = ys.length) :
    ∀ st,
      st.lookupVar "a" = some (CVal.ptrAddr (aBase : PtrVal)) →
      st.lookupVar "b" = some (CVal.ptrAddr (bBase : PtrVal)) →
      st.lookupVar "n" = some (.int (Int.ofNat xs.length)) →
      bytesAt_s aBase xs st →
      bytesAt_s bBase ys st →
      ∃ st',
        execStmt (swhileFuel ctEqLoopBody xs.length + 3) ctEqBody st =
          some (.returned (.int (if xs = ys then 1 else 0)) st') ∧
        bytesAt_s aBase xs st' ∧
        bytesAt_s bBase ys st' := by
  intro st hAPtr hBPtr hN hXsBytes hYsBytes
  let st1 := st.updateVar "m" (.int 0)
  let st2 := st1.updateVar "i" (.int 0)
  have hAPtr2 : st2.lookupVar "a" = some (CVal.ptrAddr (aBase : PtrVal)) := by
    simp [st2, st1, hAPtr, lookupVar_updateVar_ne]
  have hBPtr2 : st2.lookupVar "b" = some (CVal.ptrAddr (bBase : PtrVal)) := by
    simp [st2, st1, hBPtr, lookupVar_updateVar_ne]
  have hN2 : st2.lookupVar "n" = some (.int (Int.ofNat xs.length)) := by
    simp [st2, st1, hN, lookupVar_updateVar_ne]
  have hI2 : st2.lookupVar "i" = some (.int 0) := by
    simp [st2]
  have hM2 : st2.lookupVar "m" = some (.int 0) := by
    simp [st2, st1, lookupVar_updateVar_ne]
  have hXsBytes2 : bytesAt_s aBase xs st2 := by
    simpa [st2, st1] using
      (bytesAt_s_updateVar aBase xs st1 "i" (.int 0)).2
        ((bytesAt_s_updateVar aBase xs st "m" (.int 0)).2 hXsBytes)
  have hYsBytes2 : bytesAt_s bBase ys st2 := by
    simpa [st2, st1] using
      (bytesAt_s_updateVar bBase ys st1 "i" (.int 0)).2
        ((bytesAt_s_updateVar bBase ys st "m" (.int 0)).2 hYsBytes)
  have hLoopWP :
      swhileWP xs.length ctEqCond (ctEqInv aBase bBase xs ys)
        ctEqLoopBody (ctEqLoopPost aBase bBase xs ys) st2 := by
    exact ctEq_loop_from_state aBase bBase xs [] xs ys [] ys st2
      (by simp) (by simp) hLen (by simp) hAPtr2 hBPtr2 hN2 hI2 hM2 hXsBytes2 hYsBytes2
  have hLoopExec :
      ∃ stLoop,
        execStmt (swhileFuel ctEqLoopBody xs.length)
          (.whileInv ctEqCond HProp.htrue ctEqLoopBody) st2 =
            some (.normal stLoop) ∧
        ctEqLoopPost aBase bBase xs ys CVal.undef stLoop := by
    exact swhileWP_sound ctEqCond (ctEqInv aBase bBase xs ys) HProp.htrue
      ctEqLoopBody ctEq_loopFree ctEq_noReturn hLoopWP
  rcases hLoopExec with ⟨stLoop, hExecLoop, hPostLoop⟩
  rcases hPostLoop with ⟨hMFinal, hXsFinal, hYsFinal⟩
  have hRet :
      execStmt (swhileFuel ctEqLoopBody xs.length)
        (.ret (.binop .eq (.var "m") (.intLit 0))) stLoop =
          some (.returned (.int (if xs = ys then 1 else 0)) stLoop) := by
    change execStmt (Nat.succ (stmtDepth ctEqLoopBody + xs.length))
      (.ret (.binop .eq (.var "m") (.intLit 0))) stLoop =
        some (.returned (.int (if xs = ys then 1 else 0)) stLoop)
    have hEval :
        evalExpr (.binop .eq (.var "m") (.intLit 0)) stLoop =
          some (.int (if xs = ys then 1 else 0)) := by
      simp [evalExpr, evalStaticExpr, hMFinal, neqCount_eq_zero_iff]
    simpa [execStmt, hEval]
  let loopFuel := swhileFuel ctEqLoopBody xs.length
  have hExecInner :
      execStmt (loopFuel + 1)
        (.seq (.whileInv ctEqCond HProp.htrue ctEqLoopBody)
          (.ret (.binop .eq (.var "m") (.intLit 0)))) st2 =
          some (.returned (.int (if xs = ys then 1 else 0)) stLoop) := by
    simp [execStmt]
    rw [hExecLoop]
    simpa [hRet]
  have hExecAfterI :
      execStmt (loopFuel + 2)
        (.seq (.assign (.var "i") (.intLit 0))
          (.seq (.whileInv ctEqCond HProp.htrue ctEqLoopBody)
            (.ret (.binop .eq (.var "m") (.intLit 0))))) st1 =
          some (.returned (.int (if xs = ys then 1 else 0)) stLoop) := by
    simp [execStmt, st2]
    exact hExecInner
  refine ⟨stLoop, ?_, hXsFinal, hYsFinal⟩
  have hExecAfterM :
      execStmt (loopFuel + 3) ctEqBody st =
        some (.returned (.int (if xs = ys then 1 else 0)) stLoop) := by
    simp [ctEqBody, execStmt, st1]
    exact hExecAfterI
  simpa [loopFuel, swhileFuel, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hExecAfterM

end HeytingLean.LeanCP.RealWorld
