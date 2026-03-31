import HeytingLean.LeanCP.RealWorld.Support
import HeytingLean.LeanCP.VCG.SWhile
import HeytingLean.LeanCP.Core.VarLemmas
import HeytingLean.LoF.ICC.WitnessSpec
import Mathlib.Tactic

namespace HeytingLean.LeanCP.RealWorld

open HeytingLean.LeanCP
open HeytingLean.LoF.ICC

set_option linter.unnecessarySimpa false

def mismatchCount : List Int → List Int → Nat
  | [], [] => 0
  | x :: xs, y :: ys => (if x = y then 0 else 1) + mismatchCount xs ys
  | _ :: xs, [] => xs.length + 1
  | [], _ :: ys => ys.length + 1

theorem mismatchCount_eq_zero_iff {xs ys : List Int} :
    mismatchCount xs ys = 0 ↔ xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => simp [mismatchCount]
      | cons y ys => simp [mismatchCount]
  | cons x xs ih =>
      cases ys with
      | nil => simp [mismatchCount]
      | cons y ys =>
          by_cases hxy : x = y
          · subst hxy
            simp [mismatchCount, ih]
          · simp [mismatchCount, hxy]

def writeIntCells : Heap → Nat → List Int → Heap
  | heap, _, [] => heap
  | heap, base, value :: rest => writeIntCells (heap.write base (.int value)) (base + 1) rest

def iccWitnessExpectedBase : Nat := 100
def iccWitnessActualBase (expectedCells : List Int) : Nat :=
  iccWitnessExpectedBase + expectedCells.length + 16

private theorem writeIntCells_read_preserve
    (heap : Heap) (base : Nat) (vals : List Int) (addr : Nat) (v : CVal)
    (hread : heap.read addr = some v)
    (hdisj : ∀ i, i < vals.length → base + i ≠ addr) :
    (writeIntCells heap base vals).read addr = some v := by
  induction vals generalizing heap base with
  | nil =>
      simpa [writeIntCells] using hread
  | cons x xs ih =>
      have hbase : base ≠ addr := by
        exact hdisj 0 (by simp)
      have hread' : (heap.write base (.int x)).read addr = some v := by
        calc
          (heap.write base (.int x)).read addr = heap.read addr := by
            simpa using heap_read_write_ne heap base addr (.int x) hbase.symm
          _ = some v := hread
      have hdisj' : ∀ i, i < xs.length → (base + 1) + i ≠ addr := by
        intro i hi
        have := hdisj (i + 1) (by simpa)
        omega
      simpa [writeIntCells, Nat.add_assoc] using
        ih (heap := heap.write base (.int x)) (base := base + 1) hread' hdisj'

private theorem writeIntCells_read_self (heap : Heap) (base : Nat) (vals : List Int) :
    ∀ i v, vals[i]? = some v → (writeIntCells heap base vals).read (base + i) = some (.int v) := by
  induction vals generalizing heap base with
  | nil =>
      intro i v hv
      simp at hv
  | cons x xs ih =>
      intro i v hv
      cases i with
      | zero =>
          simp [writeIntCells] at hv ⊢
          cases hv
          have hread0 : (heap.write base (.int x)).read base = some (.int x) := by
            simpa using heap_read_write_eq heap base (.int x)
          have hdisj : ∀ j, j < xs.length → (base + 1) + j ≠ base := by
            intro j hj
            omega
          simpa [Nat.add_assoc] using
            writeIntCells_read_preserve (heap := heap.write base (.int x)) (base := base + 1)
              (vals := xs) (addr := base) (v := .int x) hread0 hdisj
      | succ i =>
          simpa [writeIntCells, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            ih (heap := heap.write base (.int x)) (base := base + 1) i v hv

def iccWitnessInitState (expectedCells actualCells : List Int) : CState :=
  let actualBase := iccWitnessActualBase expectedCells
  let heap := writeIntCells (writeIntCells Heap.empty actualBase actualCells)
    iccWitnessExpectedBase expectedCells
  { heap := heap
    env :=
      [ ("actual", CVal.ptrAddr (actualBase : PtrVal))
      , ("expected", CVal.ptrAddr (iccWitnessExpectedBase : PtrVal))
      , ("n", .int (Int.ofNat expectedCells.length))
      ]
    nextAddr := max (iccWitnessExpectedBase + expectedCells.length)
      (actualBase + actualCells.length) + 16 }

def iccWitnessCond : CExpr :=
  .binop .lt (.var "i") (.var "n")

def iccWitnessExpectedCell : CExpr :=
  .deref (.binop .add (.var "expected") (.var "i"))

def iccWitnessActualCell : CExpr :=
  .deref (.binop .add (.var "actual") (.var "i"))

def iccWitnessLoopBody : CStmt :=
  .seq
    (.ite
      (.binop .ne iccWitnessExpectedCell iccWitnessActualCell)
      (.assign (.var "m") (.binop .add (.var "m") (.intLit 1)))
      .skip)
    (.assign (.var "i") (.binop .add (.var "i") (.intLit 1)))

def iccWitnessVerifierBody : CStmt :=
  .seq (.assign (.var "m") (.intLit 0))
    (.seq (.assign (.var "i") (.intLit 0))
      (.seq (.whileInv iccWitnessCond HProp.htrue iccWitnessLoopBody)
        (.ret (.binop .eq (.var "m") (.intLit 0)))))

def iccWitnessInv (expectedCells actualCells : List Int) : SProp := fun st =>
  ∃ doneExpected restExpected doneActual restActual,
    expectedCells = doneExpected ++ restExpected ∧
    actualCells = doneActual ++ restActual ∧
    expectedCells.length = actualCells.length ∧
    doneExpected.length = doneActual.length ∧
    st.lookupVar "expected" = some (CVal.ptrAddr (iccWitnessExpectedBase : PtrVal)) ∧
    st.lookupVar "actual" = some (CVal.ptrAddr (iccWitnessActualBase expectedCells : PtrVal)) ∧
    st.lookupVar "n" = some (.int (Int.ofNat expectedCells.length)) ∧
    st.lookupVar "i" = some (.int (Int.ofNat doneExpected.length)) ∧
    st.lookupVar "m" = some (.int (Int.ofNat (mismatchCount doneExpected doneActual))) ∧
    bytesAt_s iccWitnessExpectedBase expectedCells st ∧
    bytesAt_s (iccWitnessActualBase expectedCells) actualCells st

def iccWitnessLoopPost (expectedCells actualCells : List Int) : CVal → SProp := fun _ st =>
  st.lookupVar "m" = some (.int (Int.ofNat (mismatchCount expectedCells actualCells))) ∧
  bytesAt_s iccWitnessExpectedBase expectedCells st ∧
  bytesAt_s (iccWitnessActualBase expectedCells) actualCells st

private theorem iccWitness_loopFree : LoopFree iccWitnessLoopBody := by
  simp [iccWitnessLoopBody, LoopFree]

private theorem iccWitness_noReturn : NoReturn iccWitnessLoopBody := by
  simp [iccWitnessLoopBody, NoReturn]

private theorem mismatchCount_append_single
    (doneExpected doneActual : List Int) (hLen : doneExpected.length = doneActual.length)
    (x y : Int) :
    mismatchCount (doneExpected ++ [x]) (doneActual ++ [y]) =
      mismatchCount doneExpected doneActual + (if x = y then 0 else 1) := by
  induction doneExpected generalizing doneActual with
  | nil =>
      cases doneActual with
      | nil => by_cases hxy : x = y <;> simp [mismatchCount, hxy]
      | cons a rest => simp at hLen
  | cons h t ih =>
      cases doneActual with
      | nil => simp at hLen
      | cons a rest =>
          have hLen' : t.length = rest.length := by simpa using hLen
          by_cases hha : h = a
          · subst hha
            simp [mismatchCount, ih rest hLen']
          · simp [mismatchCount, hha, ih rest hLen', Nat.add_assoc]

private theorem iccWitness_loop_from_state
    (expectedCells doneExpected restExpected actualCells doneActual restActual : List Int)
    (st : CState)
    (hExpected : expectedCells = doneExpected ++ restExpected)
    (hActual : actualCells = doneActual ++ restActual)
    (hLen : expectedCells.length = actualCells.length)
    (hDoneLen : doneExpected.length = doneActual.length)
    (hExpectedPtr : st.lookupVar "expected" = some (CVal.ptrAddr (iccWitnessExpectedBase : PtrVal)))
    (hActualPtr : st.lookupVar "actual" = some (CVal.ptrAddr (iccWitnessActualBase expectedCells : PtrVal)))
    (hN : st.lookupVar "n" = some (.int (Int.ofNat expectedCells.length)))
    (hI : st.lookupVar "i" = some (.int (Int.ofNat doneExpected.length)))
    (hM : st.lookupVar "m" = some (.int (Int.ofNat (mismatchCount doneExpected doneActual))))
    (hExpectedCells : bytesAt_s iccWitnessExpectedBase expectedCells st)
    (hActualCells : bytesAt_s (iccWitnessActualBase expectedCells) actualCells st) :
    swhileWP restExpected.length iccWitnessCond (iccWitnessInv expectedCells actualCells)
      iccWitnessLoopBody (iccWitnessLoopPost expectedCells actualCells) st := by
  let actualBase := iccWitnessActualBase expectedCells
  induction restExpected generalizing doneExpected actualCells doneActual restActual st with
  | nil =>
      have hRestActualNil : restActual = [] := by
        have : restActual.length = 0 := by
          have hLen' := hLen
          rw [hExpected, hActual] at hLen'
          simp at hLen'
          omega
        exact List.length_eq_zero_iff.mp this
      subst hRestActualNil
      have hInv : iccWitnessInv expectedCells actualCells st := by
        exact ⟨doneExpected, [], doneActual, [], hExpected, hActual, hLen, hDoneLen,
          hExpectedPtr, hActualPtr, hN, hI, hM, hExpectedCells, hActualCells⟩
      have hCond : evalExpr iccWitnessCond st = some (.int 0) := by
        simpa [iccWitnessCond, evalExpr, evalStaticExpr, hI, hN, hExpected] using
          (show evalBinOp .lt (.int (Int.ofNat doneExpected.length))
              (.int (Int.ofNat doneExpected.length)) = some (.int 0) by
            change some (CVal.int (if Int.ofNat doneExpected.length < Int.ofNat doneExpected.length then 1 else 0)) =
              some (CVal.int 0)
            simp)
      have hPost : iccWitnessLoopPost expectedCells actualCells CVal.undef st := by
        refine ⟨?_, hExpectedCells, hActualCells⟩
        simpa [hExpected, hActual] using hM
      simpa [swhileWP, hCond, isTruthy] using And.intro hInv hPost
  | cons nextExpected tailExpected ih =>
      cases restActual with
      | nil =>
          have : False := by
            have hLen' := hLen
            rw [hExpected, hActual] at hLen'
            simp at hLen'
            omega
          exact False.elim this
      | cons nextActual tailActual =>
          have hInv : iccWitnessInv expectedCells actualCells st := by
            exact ⟨doneExpected, nextExpected :: tailExpected, doneActual, nextActual :: tailActual,
              hExpected, hActual, hLen, hDoneLen, hExpectedPtr, hActualPtr, hN, hI, hM,
              hExpectedCells, hActualCells⟩
          have hLt : doneExpected.length < expectedCells.length := by
            rw [hExpected]
            simp
          have hCond : evalExpr iccWitnessCond st = some (.int 1) := by
            simpa [iccWitnessCond, evalExpr, evalStaticExpr, hI, hN] using
              (show evalBinOp .lt (.int (Int.ofNat doneExpected.length))
                  (.int (Int.ofNat expectedCells.length)) = some (.int 1) by
                change some (CVal.int (if Int.ofNat doneExpected.length < Int.ofNat expectedCells.length then 1 else 0)) =
                  some (CVal.int 1)
                simp [Int.ofNat_lt.mpr hLt])
          have hExpectedGet : expectedCells[doneExpected.length]? = some nextExpected := by
            rw [hExpected]
            simp
          have hActualGet : actualCells[doneActual.length]? = some nextActual := by
            rw [hActual]
            simp
          have hExpectedRead : st.heap.read (iccWitnessExpectedBase + doneExpected.length) =
              some (.int nextExpected) := by
            exact hExpectedCells _ _ hExpectedGet
          have hActualRead : st.heap.read (actualBase + doneActual.length) =
              some (.int nextActual) := by
            exact hActualCells _ _ hActualGet
          have hIActual : st.lookupVar "i" = some (.int (Int.ofNat doneActual.length)) := by
            simpa [hDoneLen] using hI
          have hExpectedPtrEval :
              evalExpr (.binop .add (.var "expected") (.var "i")) st =
                some (CVal.ptrAddr ((iccWitnessExpectedBase + doneExpected.length) : PtrVal)) := by
            simpa [evalExpr, evalStaticExpr, hExpectedPtr, hI] using
              (show evalBinOp .add (CVal.ptrAddr (iccWitnessExpectedBase : PtrVal))
                  (.int (Int.ofNat doneExpected.length)) =
                    some (CVal.ptrAddr ((iccWitnessExpectedBase + doneExpected.length) : PtrVal)) by
                change
                  (if 0 ≤ Int.ofNat doneExpected.length then
                    some (CVal.ptrAddr
                      { block := 0, offset := Int.ofNat iccWitnessExpectedBase + Int.ofNat doneExpected.length })
                  else none) = some (CVal.ptrAddr ((iccWitnessExpectedBase + doneExpected.length) : PtrVal))
                simp)
          have hActualPtrEval :
              evalExpr (.binop .add (.var "actual") (.var "i")) st =
                some (CVal.ptrAddr ((actualBase + doneActual.length) : PtrVal)) := by
            simpa [actualBase, evalExpr, evalStaticExpr, hActualPtr, hIActual] using
              (show evalBinOp .add (CVal.ptrAddr (actualBase : PtrVal))
                  (.int (Int.ofNat doneActual.length)) =
                    some (CVal.ptrAddr ((actualBase + doneActual.length) : PtrVal)) by
                change
                  (if 0 ≤ Int.ofNat doneActual.length then
                    some (CVal.ptrAddr
                      { block := 0, offset := Int.ofNat actualBase + Int.ofNat doneActual.length })
                  else none) = some (CVal.ptrAddr ((actualBase + doneActual.length) : PtrVal))
                simp)
          have hExpectedDeref : evalExpr iccWitnessExpectedCell st = some (.int nextExpected) := by
            simpa [iccWitnessExpectedCell, evalExpr, evalStaticExpr, hExpectedPtrEval, hExpectedRead] using
              (CState.readPtr_block0 st (iccWitnessExpectedBase + doneExpected.length)
                (iccWitnessExpectedBase + doneExpected.length))
          have hActualDeref : evalExpr iccWitnessActualCell st = some (.int nextActual) := by
            simpa [iccWitnessActualCell, evalExpr, evalStaticExpr, hActualPtrEval, hActualRead] using
              (CState.readPtr_block0 st (actualBase + doneActual.length)
                (actualBase + doneActual.length))
          have hInc : evalExpr (.binop .add (.var "i") (.intLit 1)) st =
              some (.int (Int.ofNat (doneExpected.length + 1))) := by
            simpa [evalExpr, evalStaticExpr, hI] using
              (show evalBinOp .add (.int (Int.ofNat doneExpected.length)) (.int 1) =
                  some (.int (Int.ofNat (doneExpected.length + 1))) by
                change some (CVal.int (Int.ofNat doneExpected.length + 1)) =
                  some (CVal.int (Int.ofNat (doneExpected.length + 1)))
                simp)
          let mismatchFlag : Nat := if nextExpected = nextActual then 0 else 1
          have hMismatchEval :
              evalExpr (.binop .ne iccWitnessExpectedCell iccWitnessActualCell) st =
                some (.int (Int.ofNat mismatchFlag)) := by
            by_cases hEq : nextExpected = nextActual
            · subst hEq
              have hBinOp : evalBinOp .ne (.int nextExpected) (.int nextExpected) = some (.int 0) := by
                change some (CVal.int (if nextExpected ≠ nextExpected then 1 else 0)) =
                  some (CVal.int 0)
                simp
              -- lean4#11546 workaround: prove static branch = none separately to avoid
              -- recursive evalExpr unfolding when cell defs are in the simp set
              have hStaticNone : evalStaticExpr (.binop .ne iccWitnessExpectedCell iccWitnessActualCell) = none := by
                simp [iccWitnessExpectedCell, iccWitnessActualCell, evalStaticExpr]
              simp only [evalExpr, hStaticNone, hExpectedDeref, hActualDeref,
                  Option.bind, Bind.bind, hBinOp, mismatchFlag]
              simp
            · have hBinOp : evalBinOp .ne (.int nextExpected) (.int nextActual) = some (.int 1) := by
                change some (CVal.int (if nextExpected ≠ nextActual then 1 else 0)) =
                  some (CVal.int 1)
                simp [hEq]
              have hStaticNone : evalStaticExpr (.binop .ne iccWitnessExpectedCell iccWitnessActualCell) = none := by
                simp [iccWitnessExpectedCell, iccWitnessActualCell, evalStaticExpr]
              simp only [evalExpr, hStaticNone, hExpectedDeref, hActualDeref, hEq,
                  Option.bind, Bind.bind, hBinOp, mismatchFlag]
              simp
          have hAddMismatch :
              evalExpr (.binop .add (.var "m") (.intLit 1)) st =
                some (.int (Int.ofNat (mismatchCount doneExpected doneActual + 1))) := by
            simpa [evalExpr, evalStaticExpr, hM, Nat.cast_add] using
              (show evalBinOp .add (.int (Int.ofNat (mismatchCount doneExpected doneActual))) (.int 1) =
                  some (.int (Int.ofNat (mismatchCount doneExpected doneActual + 1))) by
                change some (CVal.int (Int.ofNat (mismatchCount doneExpected doneActual) + 1)) =
                  some (CVal.int (Int.ofNat (mismatchCount doneExpected doneActual + 1)))
                simp)
          by_cases hEq : nextExpected = nextActual
          · subst hEq
            let st2 := st.updateVar "i" (.int (Int.ofNat (doneExpected.length + 1)))
            have hExpectedPtr2 : st2.lookupVar "expected" = some (CVal.ptrAddr (iccWitnessExpectedBase : PtrVal)) := by
              calc
                st2.lookupVar "expected" = st.lookupVar "expected" := by
                  simpa [st2] using lookupVar_updateVar_ne st "i" "expected"
                    (.int (Int.ofNat (doneExpected.length + 1))) (by decide : "expected" ≠ "i")
                _ = some (CVal.ptrAddr (iccWitnessExpectedBase : PtrVal)) := hExpectedPtr
            have hActualPtr2 : st2.lookupVar "actual" = some (CVal.ptrAddr (actualBase : PtrVal)) := by
              calc
                st2.lookupVar "actual" = st.lookupVar "actual" := by
                  simpa [st2] using lookupVar_updateVar_ne st "i" "actual"
                    (.int (Int.ofNat (doneExpected.length + 1))) (by decide : "actual" ≠ "i")
                _ = some (CVal.ptrAddr (actualBase : PtrVal)) := hActualPtr
            have hN2 : st2.lookupVar "n" = some (.int (Int.ofNat expectedCells.length)) := by
              calc
                st2.lookupVar "n" = st.lookupVar "n" := by
                  simpa [st2] using lookupVar_updateVar_ne st "i" "n"
                    (.int (Int.ofNat (doneExpected.length + 1))) (by decide : "n" ≠ "i")
                _ = some (.int (Int.ofNat expectedCells.length)) := hN
            have hI2 : st2.lookupVar "i" = some (.int (Int.ofNat ((doneExpected ++ [nextExpected]).length))) := by
              simpa [st2] using lookupVar_updateVar_eq st "i" (.int (Int.ofNat (doneExpected.length + 1)))
            have hM2 : st2.lookupVar "m" = some (.int (Int.ofNat (mismatchCount (doneExpected ++ [nextExpected]) (doneActual ++ [nextExpected])))) := by
              calc
                st2.lookupVar "m" = st.lookupVar "m" := by
                  simpa [st2] using lookupVar_updateVar_ne st "i" "m"
                    (.int (Int.ofNat (doneExpected.length + 1))) (by decide : "m" ≠ "i")
                _ = some (.int (Int.ofNat (mismatchCount doneExpected doneActual))) := hM
                _ = some (.int (Int.ofNat (mismatchCount (doneExpected ++ [nextExpected]) (doneActual ++ [nextExpected])))) := by
                  simp [mismatchCount_append_single, hDoneLen]
            have hExpectedCells2 : bytesAt_s iccWitnessExpectedBase expectedCells st2 := by
              simpa [st2] using
                (bytesAt_s_updateVar iccWitnessExpectedBase expectedCells st "i"
                  (.int (Int.ofNat (doneExpected.length + 1)))).2 hExpectedCells
            have hActualCells2 : bytesAt_s actualBase actualCells st2 := by
              simpa [st2] using
                (bytesAt_s_updateVar actualBase actualCells st "i"
                  (.int (Int.ofNat (doneExpected.length + 1)))).2 hActualCells
            have hExpected2 : expectedCells = (doneExpected ++ [nextExpected]) ++ tailExpected := by
              simpa [List.append_assoc] using hExpected
            have hActual2 : actualCells = (doneActual ++ [nextExpected]) ++ tailActual := by
              simpa [List.append_assoc] using hActual
            have hDoneLen2 : (doneExpected ++ [nextExpected]).length = (doneActual ++ [nextExpected]).length := by
              simp [hDoneLen]
            have hLoop2 :
                swhileWP tailExpected.length iccWitnessCond (iccWitnessInv expectedCells actualCells)
                  iccWitnessLoopBody (iccWitnessLoopPost expectedCells actualCells) st2 := by
              exact ih (doneExpected ++ [nextExpected]) actualCells (doneActual ++ [nextExpected]) tailActual st2
                hExpected2 hActual2 hLen hDoneLen2 hExpectedPtr2 hActualPtr2 hN2 hI2 hM2
                hExpectedCells2 hActualCells2
            have hAssignI :
                swp (.assign (.var "i") (.binop .add (.var "i") (.intLit 1)))
                  (fun _ => swhileWP tailExpected.length iccWitnessCond (iccWitnessInv expectedCells actualCells)
                    iccWitnessLoopBody (iccWitnessLoopPost expectedCells actualCells)) st := by
              simpa [swp, hInc, st2] using hLoop2
            have hBody :
                swp iccWitnessLoopBody
                  (fun _ => swhileWP tailExpected.length iccWitnessCond (iccWitnessInv expectedCells actualCells)
                    iccWitnessLoopBody (iccWitnessLoopPost expectedCells actualCells)) st := by
              have hFlag : mismatchFlag = 0 := by
                simp [mismatchFlag]
              have hTruthy : isTruthy (.int (Int.ofNat mismatchFlag)) = false := by
                simpa [hFlag, isTruthy]
              simpa [iccWitnessLoopBody, swp, hMismatchEval, hTruthy, hFlag] using hAssignI
            simpa [swhileWP, hCond] using And.intro hInv hBody
          · let st1 := st.updateVar "m" (.int (Int.ofNat (mismatchCount doneExpected doneActual + 1)))
            let st2 := st1.updateVar "i" (.int (Int.ofNat (doneExpected.length + 1)))
            have hExpectedPtr1 : st1.lookupVar "expected" = some (CVal.ptrAddr (iccWitnessExpectedBase : PtrVal)) := by
              calc
                st1.lookupVar "expected" = st.lookupVar "expected" := by
                  simpa [st1] using lookupVar_updateVar_ne st "m"
                    "expected" (.int (Int.ofNat (mismatchCount doneExpected doneActual + 1)))
                    (by decide : "expected" ≠ "m")
                _ = some (CVal.ptrAddr (iccWitnessExpectedBase : PtrVal)) := hExpectedPtr
            have hActualPtr1 : st1.lookupVar "actual" = some (CVal.ptrAddr (actualBase : PtrVal)) := by
              calc
                st1.lookupVar "actual" = st.lookupVar "actual" := by
                  simpa [st1] using lookupVar_updateVar_ne st "m"
                    "actual" (.int (Int.ofNat (mismatchCount doneExpected doneActual + 1)))
                    (by decide : "actual" ≠ "m")
                _ = some (CVal.ptrAddr (actualBase : PtrVal)) := hActualPtr
            have hN1 : st1.lookupVar "n" = some (.int (Int.ofNat expectedCells.length)) := by
              calc
                st1.lookupVar "n" = st.lookupVar "n" := by
                  simpa [st1] using lookupVar_updateVar_ne st "m"
                    "n" (.int (Int.ofNat (mismatchCount doneExpected doneActual + 1)))
                    (by decide : "n" ≠ "m")
                _ = some (.int (Int.ofNat expectedCells.length)) := hN
            have hExpectedPtr2 : st2.lookupVar "expected" = some (CVal.ptrAddr (iccWitnessExpectedBase : PtrVal)) := by
              calc
                st2.lookupVar "expected" = st1.lookupVar "expected" := by
                  simpa [st2] using lookupVar_updateVar_ne st1 "i"
                    "expected" (.int (Int.ofNat (doneExpected.length + 1)))
                    (by decide : "expected" ≠ "i")
                _ = some (CVal.ptrAddr (iccWitnessExpectedBase : PtrVal)) := hExpectedPtr1
            have hActualPtr2 : st2.lookupVar "actual" = some (CVal.ptrAddr (actualBase : PtrVal)) := by
              calc
                st2.lookupVar "actual" = st1.lookupVar "actual" := by
                  simpa [st2] using lookupVar_updateVar_ne st1 "i"
                    "actual" (.int (Int.ofNat (doneExpected.length + 1)))
                    (by decide : "actual" ≠ "i")
                _ = some (CVal.ptrAddr (actualBase : PtrVal)) := hActualPtr1
            have hN2 : st2.lookupVar "n" = some (.int (Int.ofNat expectedCells.length)) := by
              calc
                st2.lookupVar "n" = st1.lookupVar "n" := by
                  simpa [st2] using lookupVar_updateVar_ne st1 "i"
                    "n" (.int (Int.ofNat (doneExpected.length + 1)))
                    (by decide : "n" ≠ "i")
                _ = some (.int (Int.ofNat expectedCells.length)) := hN1
            have hI2 : st2.lookupVar "i" = some (.int (Int.ofNat ((doneExpected ++ [nextExpected]).length))) := by
              simpa [st2] using lookupVar_updateVar_eq st1 "i" (.int (Int.ofNat (doneExpected.length + 1)))
            have hM2 : st2.lookupVar "m" = some (.int (Int.ofNat (mismatchCount (doneExpected ++ [nextExpected]) (doneActual ++ [nextActual])))) := by
              calc
                st2.lookupVar "m" = st1.lookupVar "m" := by
                  simpa [st2] using lookupVar_updateVar_ne st1 "i" "m"
                    (.int (Int.ofNat (doneExpected.length + 1))) (by decide : "m" ≠ "i")
                _ = some (.int (Int.ofNat (mismatchCount doneExpected doneActual + 1))) := by
                  simpa [st1] using lookupVar_updateVar_eq st "m"
                    (.int (Int.ofNat (mismatchCount doneExpected doneActual + 1)))
                _ = some (.int (Int.ofNat (mismatchCount (doneExpected ++ [nextExpected]) (doneActual ++ [nextActual])))) := by
                  simp [mismatchCount_append_single, hDoneLen, hEq]
            have hExpectedCells1 : bytesAt_s iccWitnessExpectedBase expectedCells st1 := by
              simpa [st1] using
                (bytesAt_s_updateVar iccWitnessExpectedBase expectedCells st "m"
                  (.int (Int.ofNat (mismatchCount doneExpected doneActual + 1)))).2 hExpectedCells
            have hActualCells1 : bytesAt_s actualBase actualCells st1 := by
              simpa [st1] using
                (bytesAt_s_updateVar actualBase actualCells st "m"
                  (.int (Int.ofNat (mismatchCount doneExpected doneActual + 1)))).2 hActualCells
            have hExpectedCells2 : bytesAt_s iccWitnessExpectedBase expectedCells st2 := by
              simpa [st2] using
                (bytesAt_s_updateVar iccWitnessExpectedBase expectedCells st1 "i"
                  (.int (Int.ofNat (doneExpected.length + 1)))).2 hExpectedCells1
            have hActualCells2 : bytesAt_s actualBase actualCells st2 := by
              simpa [st2] using
                (bytesAt_s_updateVar actualBase actualCells st1 "i"
                  (.int (Int.ofNat (doneExpected.length + 1)))).2 hActualCells1
            have hExpected2 : expectedCells = (doneExpected ++ [nextExpected]) ++ tailExpected := by
              simpa [List.append_assoc] using hExpected
            have hActual2 : actualCells = (doneActual ++ [nextActual]) ++ tailActual := by
              simpa [List.append_assoc] using hActual
            have hDoneLen2 : (doneExpected ++ [nextExpected]).length = (doneActual ++ [nextActual]).length := by
              simp [hDoneLen]
            have hLoop2 :
                swhileWP tailExpected.length iccWitnessCond (iccWitnessInv expectedCells actualCells)
                  iccWitnessLoopBody (iccWitnessLoopPost expectedCells actualCells) st2 := by
              exact ih (doneExpected ++ [nextExpected]) actualCells (doneActual ++ [nextActual]) tailActual st2
                hExpected2 hActual2 hLen hDoneLen2 hExpectedPtr2 hActualPtr2 hN2 hI2 hM2
                hExpectedCells2 hActualCells2
            have hAssignI :
                swp (.assign (.var "i") (.binop .add (.var "i") (.intLit 1)))
                  (fun _ => swhileWP tailExpected.length iccWitnessCond (iccWitnessInv expectedCells actualCells)
                    iccWitnessLoopBody (iccWitnessLoopPost expectedCells actualCells)) st1 := by
              have hInc1 :
                  evalExpr (.binop .add (.var "i") (.intLit 1)) st1 =
                    some (.int (Int.ofNat (doneExpected.length + 1))) := by
                calc
                  evalExpr (.binop .add (.var "i") (.intLit 1)) st1
                      = evalExpr (.binop .add (.var "i") (.intLit 1)) st := by
                        simp [evalExpr, evalStaticExpr, st1, lookupVar_updateVar_ne, hI]
                  _ = some (.int (Int.ofNat (doneExpected.length + 1))) := hInc
              simpa [swp, hInc1, st2] using hLoop2
            have hAssignMismatch :
                swp (.assign (.var "m") (.binop .add (.var "m") (.intLit 1)))
                  (fun _ => swp (.assign (.var "i") (.binop .add (.var "i") (.intLit 1)))
                    (fun _ => swhileWP tailExpected.length iccWitnessCond (iccWitnessInv expectedCells actualCells)
                      iccWitnessLoopBody (iccWitnessLoopPost expectedCells actualCells))) st := by
              simpa [swp, hAddMismatch, st1] using hAssignI
            have hBody :
                swp iccWitnessLoopBody
                  (fun _ => swhileWP tailExpected.length iccWitnessCond (iccWitnessInv expectedCells actualCells)
                    iccWitnessLoopBody (iccWitnessLoopPost expectedCells actualCells)) st := by
              have hFlag : mismatchFlag = 1 := by
                simp [mismatchFlag, hEq]
              have hTruthy : isTruthy (.int (Int.ofNat mismatchFlag)) = true := by
                simpa [hFlag, isTruthy]
              simpa [iccWitnessLoopBody, swp, hMismatchEval, hTruthy, hFlag] using hAssignMismatch
            simpa [swhileWP, hCond] using And.intro hInv hBody

theorem iccWitnessCells_correct (expectedCells actualCells : List Int)
    (hLen : expectedCells.length = actualCells.length) :
    ∃ st',
      execStmt (swhileFuel iccWitnessLoopBody expectedCells.length + 3)
        iccWitnessVerifierBody (iccWitnessInitState expectedCells actualCells) =
          some (.returned (.int (if mismatchCount expectedCells actualCells = 0 then 1 else 0)) st') ∧
      bytesAt_s iccWitnessExpectedBase expectedCells st' ∧
      bytesAt_s (iccWitnessActualBase expectedCells) actualCells st' := by
  let st0 := iccWitnessInitState expectedCells actualCells
  let actualBase := iccWitnessActualBase expectedCells
  let st1 := st0.updateVar "m" (.int 0)
  let st2 := st1.updateVar "i" (.int 0)
  have hExpectedPtr0 : st0.lookupVar "expected" = some (CVal.ptrAddr (iccWitnessExpectedBase : PtrVal)) := by
    simp [st0, iccWitnessInitState, CState.lookupVar, List.lookup]
  have hActualPtr0 : st0.lookupVar "actual" = some (CVal.ptrAddr (actualBase : PtrVal)) := by
    simp [st0, iccWitnessInitState, actualBase, CState.lookupVar, List.lookup]
  have hN0 : st0.lookupVar "n" = some (.int (Int.ofNat expectedCells.length)) := by
    simp [st0, iccWitnessInitState, CState.lookupVar, List.lookup]
  have hExpectedBytes0 : bytesAt_s iccWitnessExpectedBase expectedCells st0 := by
    intro i v hv
    simpa [st0, iccWitnessInitState, actualBase] using
      writeIntCells_read_self
        (heap := writeIntCells Heap.empty actualBase actualCells)
        (base := iccWitnessExpectedBase) (vals := expectedCells) i v hv
  have hActualBytes0 : bytesAt_s actualBase actualCells st0 := by
    intro i v hv
    have hRead0 :
        (writeIntCells Heap.empty actualBase actualCells).read (actualBase + i) = some (.int v) := by
      exact writeIntCells_read_self (heap := Heap.empty) (base := actualBase) (vals := actualCells) i v hv
    have hPreserve :
        (writeIntCells (writeIntCells Heap.empty actualBase actualCells)
          iccWitnessExpectedBase expectedCells).read (actualBase + i) = some (.int v) := by
      refine writeIntCells_read_preserve
        (heap := writeIntCells Heap.empty actualBase actualCells)
        (base := iccWitnessExpectedBase) (vals := expectedCells)
        (addr := actualBase + i) (v := .int v) hRead0 ?_
      intro j hj
      unfold actualBase iccWitnessActualBase
      omega
    simpa [st0, iccWitnessInitState, actualBase] using hPreserve
  have hExpectedPtr2 : st2.lookupVar "expected" = some (CVal.ptrAddr (iccWitnessExpectedBase : PtrVal)) := by
    simp [st2, st1, hExpectedPtr0, lookupVar_updateVar_ne]
  have hActualPtr2 : st2.lookupVar "actual" = some (CVal.ptrAddr (actualBase : PtrVal)) := by
    simp [st2, st1, hActualPtr0, lookupVar_updateVar_ne]
  have hN2 : st2.lookupVar "n" = some (.int (Int.ofNat expectedCells.length)) := by
    simp [st2, st1, hN0, lookupVar_updateVar_ne]
  have hI2 : st2.lookupVar "i" = some (.int 0) := by
    simp [st2]
  have hM2 : st2.lookupVar "m" = some (.int 0) := by
    simp [st2, st1, lookupVar_updateVar_ne]
  have hExpectedBytes2 : bytesAt_s iccWitnessExpectedBase expectedCells st2 := by
    simpa [st2, st1] using
      (bytesAt_s_updateVar iccWitnessExpectedBase expectedCells st1 "i" (.int 0)).2
        ((bytesAt_s_updateVar iccWitnessExpectedBase expectedCells st0 "m" (.int 0)).2 hExpectedBytes0)
  have hActualBytes2 : bytesAt_s actualBase actualCells st2 := by
    simpa [st2, st1] using
      (bytesAt_s_updateVar actualBase actualCells st1 "i" (.int 0)).2
        ((bytesAt_s_updateVar actualBase actualCells st0 "m" (.int 0)).2 hActualBytes0)
  have hLoopWP :
      swhileWP expectedCells.length iccWitnessCond (iccWitnessInv expectedCells actualCells)
        iccWitnessLoopBody (iccWitnessLoopPost expectedCells actualCells) st2 := by
    exact iccWitness_loop_from_state expectedCells [] expectedCells actualCells [] actualCells st2
      (by simp) (by simp) hLen (by simp) hExpectedPtr2 hActualPtr2 hN2 hI2 hM2
      hExpectedBytes2 hActualBytes2
  have hLoopExec :
      ∃ stLoop,
        execStmt (swhileFuel iccWitnessLoopBody expectedCells.length)
          (.whileInv iccWitnessCond HProp.htrue iccWitnessLoopBody) st2 =
            some (.normal stLoop) ∧
        iccWitnessLoopPost expectedCells actualCells CVal.undef stLoop := by
    exact swhileWP_sound iccWitnessCond (iccWitnessInv expectedCells actualCells) HProp.htrue
      iccWitnessLoopBody iccWitness_loopFree iccWitness_noReturn hLoopWP
  rcases hLoopExec with ⟨stLoop, hExecLoop, hPostLoop⟩
  rcases hPostLoop with ⟨hMFinal, hExpectedFinal, hActualFinal⟩
  have hRet :
      execStmt (swhileFuel iccWitnessLoopBody expectedCells.length)
        (.ret (.binop .eq (.var "m") (.intLit 0))) stLoop =
          some (.returned (.int (if mismatchCount expectedCells actualCells = 0 then 1 else 0)) stLoop) := by
    change execStmt (Nat.succ (stmtDepth iccWitnessLoopBody + expectedCells.length))
      (.ret (.binop .eq (.var "m") (.intLit 0))) stLoop =
        some (.returned (.int (if mismatchCount expectedCells actualCells = 0 then 1 else 0)) stLoop)
    have hEval :
        evalExpr (.binop .eq (.var "m") (.intLit 0)) stLoop =
          some (.int (if mismatchCount expectedCells actualCells = 0 then 1 else 0)) := by
      have hMismatchLookup :
          stLoop.lookupVar "m" = some (.int (Int.ofNat (mismatchCount expectedCells actualCells))) := hMFinal
      simp [evalExpr, evalStaticExpr, hMismatchLookup]
    simpa [execStmt, hEval]
  let loopFuel := swhileFuel iccWitnessLoopBody expectedCells.length
  have hExecInner :
      execStmt (loopFuel + 1)
        (.seq (.whileInv iccWitnessCond HProp.htrue iccWitnessLoopBody)
          (.ret (.binop .eq (.var "m") (.intLit 0)))) st2 =
            some (.returned (.int (if mismatchCount expectedCells actualCells = 0 then 1 else 0)) stLoop) := by
    simp [execStmt]
    rw [hExecLoop]
    simpa [hRet]
  refine ⟨stLoop, ?_, hExpectedFinal, hActualFinal⟩
  have hExecAfterI :
      execStmt (loopFuel + 2)
        (.seq (.assign (.var "i") (.intLit 0))
          (.seq (.whileInv iccWitnessCond HProp.htrue iccWitnessLoopBody)
            (.ret (.binop .eq (.var "m") (.intLit 0))))) st1 =
          some (.returned (.int (if mismatchCount expectedCells actualCells = 0 then 1 else 0)) stLoop) := by
    simp [execStmt, st2]
    exact hExecInner
  have hExecAfterM :
      execStmt (loopFuel + 3) iccWitnessVerifierBody st0 =
        some (.returned (.int (if mismatchCount expectedCells actualCells = 0 then 1 else 0)) stLoop) := by
    simp [iccWitnessVerifierBody, execStmt, st1]
    exact hExecAfterI
  simpa [loopFuel, swhileFuel, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hExecAfterM

theorem iccWitnessVerifier_replay_correct (row : ICCCanonicalWitness) (candidate : List WitnessEntry)
    (hCanonical : replayEntries row.certificate row.witness = some row.normalized)
    (hCandidateLen : candidate.length = row.witness.length) :
    ∃ st',
      execStmt (swhileFuel iccWitnessLoopBody (flattenWitnessEntries row.witness).length + 3)
        iccWitnessVerifierBody
        (iccWitnessInitState (flattenWitnessEntries row.witness) (flattenWitnessEntries candidate)) =
          some (.returned
            (.int (if replayEntries row.certificate candidate = some row.normalized then 1 else 0)) st') ∧
      bytesAt_s iccWitnessExpectedBase (flattenWitnessEntries row.witness) st' ∧
      bytesAt_s (iccWitnessActualBase (flattenWitnessEntries row.witness))
        (flattenWitnessEntries candidate) st' := by
  have hSameLength :
      (flattenWitnessEntries row.witness).length = (flattenWitnessEntries candidate).length := by
    have hFlatLen : ∀ xs : List WitnessEntry, (flattenWitnessEntries xs).length = 3 * xs.length := by
      intro xs
      induction xs with
      | nil =>
          simp [flattenWitnessEntries]
      | cons x xs ih =>
          simp [flattenWitnessEntries, witnessEntryCells, ih, Nat.mul_succ, Nat.add_assoc]
    simpa [hFlatLen row.witness, hFlatLen candidate, hCandidateLen]
  have hReplayEq :
      replayEntries row.certificate candidate = some row.normalized ↔ candidate = row.witness := by
    exact replayEntries_eq_canonical_iff hCanonical
  have hZeroIffReplay :
      mismatchCount (flattenWitnessEntries row.witness) (flattenWitnessEntries candidate) = 0 ↔
        replayEntries row.certificate candidate = some row.normalized := by
    rw [mismatchCount_eq_zero_iff]
    constructor
    · intro hFlat
      have hEq : row.witness = candidate := flattenWitnessEntries_injective hFlat
      simpa [hEq] using hCanonical
    · intro hReplay
      have hEq : candidate = row.witness := hReplayEq.mp hReplay
      simpa [hEq]
  rcases iccWitnessCells_correct (flattenWitnessEntries row.witness)
      (flattenWitnessEntries candidate) hSameLength with ⟨st', hExec, hExpected, hActual⟩
  refine ⟨st', ?_, hExpected, hActual⟩
  simpa [hZeroIffReplay] using hExec

end HeytingLean.LeanCP.RealWorld
