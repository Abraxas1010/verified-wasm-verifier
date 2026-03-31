import HeytingLean.LeanCP.Examples.BinarySearch
import HeytingLean.LeanCP.Examples.ArraySumVerified
import HeytingLean.LeanCP.VCG.SWhile
import HeytingLean.LeanCP.Core.SFrameRule
import HeytingLean.LeanCP.Core.VarLemmas
import HeytingLean.LeanCP.Lang.CSemanticsDecEq
import HeytingLean.LeanCP.Tactics.Forward
import Batteries.Data.List.Lemmas
import Mathlib.Data.Int.DivMod
import Mathlib.Data.List.Sort
import Mathlib.Tactic

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

set_option linter.unnecessarySimpa false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

private theorem arrayAt_s_updateVar (base : Nat) (vals : List Int) (st : CState)
    (x : String) (v : CVal) :
    arrayAt_s base vals (st.updateVar x v) ↔ arrayAt_s base vals st := by
  rfl

/-- The current `binarySearchBody` computes the first index with `vals[idx] ≥ target`,
or `vals.length` if no such index exists. -/
def lowerBoundIndex (vals : List Int) (target : Int) : Nat :=
  vals.findIdx (fun v => decide (target ≤ v))

def binarySearchCond : CExpr :=
  .binop .lt (.var "lo") (.var "hi")

def binarySearchMidExpr : CExpr :=
  .binop .div (.binop .add (.var "lo") (.var "hi")) (.intLit 2)

def binarySearchBranchCond : CExpr :=
  .binop .lt (.deref (.binop .add (.var "a") (.var "mid"))) (.var "target")

def binarySearchLoopBody : CStmt :=
  .seq
    (.assign (.var "mid") binarySearchMidExpr)
    (.ite binarySearchBranchCond
      (.assign (.var "lo") (.binop .add (.var "mid") (.intLit 1)))
      (.assign (.var "hi") (.var "mid")))

def binarySearchInv (vals : List Int) (base : Nat) (target : Int) : SProp := fun st =>
  ∃ lo hi,
    st.lookupVar "a" = some (CVal.ptrAddr (base : PtrVal)) ∧
    st.lookupVar "n" = some (.int (Int.ofNat vals.length)) ∧
    st.lookupVar "target" = some (.int target) ∧
    st.lookupVar "lo" = some (.int (Int.ofNat lo)) ∧
    st.lookupVar "hi" = some (.int (Int.ofNat hi)) ∧
    lo ≤ lowerBoundIndex vals target ∧
    lowerBoundIndex vals target ≤ hi ∧
    hi ≤ vals.length ∧
    arrayAt_s base vals st

def binarySearchLoopPost (vals : List Int) (base : Nat) (target : Int) : CVal → SProp := fun _ st =>
  st.lookupVar "lo" = some (.int (Int.ofNat (lowerBoundIndex vals target))) ∧
  st.lookupVar "hi" = some (.int (Int.ofNat (lowerBoundIndex vals target))) ∧
  arrayAt_s base vals st

private theorem binarySearch_loopFree : LoopFree binarySearchLoopBody := by
  simp [binarySearchLoopBody, LoopFree]

private theorem binarySearch_noReturn : NoReturn binarySearchLoopBody := by
  simp [binarySearchLoopBody, NoReturn]

private theorem lowerBoundIndex_le_length (vals : List Int) (target : Int) :
    lowerBoundIndex vals target ≤ vals.length := by
  simpa [lowerBoundIndex] using
    (List.findIdx_le_length (p := fun v => decide (target ≤ v)) (xs := vals))

private theorem lowerBoundIndex_get_ge (vals : List Int) (target : Int)
    (h : lowerBoundIndex vals target < vals.length) :
    target ≤ vals[lowerBoundIndex vals target] := by
  exact of_decide_eq_true (List.findIdx_getElem (w := h))

private theorem get_lt_target_of_lt_lowerBound (vals : List Int) (target : Int)
    {i : Nat} (h : i < lowerBoundIndex vals target) :
    vals[i]'(lt_of_lt_of_le h (lowerBoundIndex_le_length vals target)) < target := by
  have hfalse :
      decide (target ≤ vals[i]'(Nat.le_trans h (lowerBoundIndex_le_length vals target))) = false := by
    simpa using
      (List.not_of_lt_findIdx (p := fun v => decide (target ≤ v)) (xs := vals) h)
  exact lt_of_not_ge (of_decide_eq_false hfalse)

private theorem get_mono_of_pairwise_le {vals : List Int}
    (hsorted : vals.Pairwise (· ≤ ·)) {i j : Nat}
    (hi : i < vals.length) (hj : j < vals.length) (hij : i ≤ j) :
    vals[i] ≤ vals[j] := by
  rcases lt_or_eq_of_le hij with hlt | rfl
  · exact (List.pairwise_iff_get.mp hsorted ⟨i, hi⟩ ⟨j, hj⟩ hlt)
  · rfl

private theorem lowerBoundIndex_le_of_target_le_get (vals : List Int) (target : Int)
    {i : Nat} (hi : i < vals.length) (hge : target ≤ vals[i]'hi) :
    lowerBoundIndex vals target ≤ i := by
  by_contra hlt
  have hlt' : i < lowerBoundIndex vals target := Nat.lt_of_not_ge hlt
  have hfalse :
      decide (target ≤ vals[i]'(Nat.le_trans hlt' (lowerBoundIndex_le_length vals target))) = false := by
    simpa using
      (List.not_of_lt_findIdx (p := fun v => decide (target ≤ v)) (xs := vals) hlt')
  exact (of_decide_eq_false hfalse) hge

private theorem lt_lowerBoundIndex_of_get_lt_target {vals : List Int}
    (hsorted : vals.Pairwise (· ≤ ·)) (target : Int) {i : Nat}
    (hi : i < vals.length) (hlt : vals[i]'hi < target) :
    i < lowerBoundIndex vals target := by
  by_contra hnot
  have hle : lowerBoundIndex vals target ≤ i := le_of_not_gt hnot
  have hlb_lt : lowerBoundIndex vals target < vals.length := lt_of_le_of_lt hle hi
  have hge_lb : target ≤ vals[lowerBoundIndex vals target] :=
    lowerBoundIndex_get_ge vals target hlb_lt
  have hmono :
      vals[lowerBoundIndex vals target] ≤ vals[i] :=
    get_mono_of_pairwise_le hsorted hlb_lt hi hle
  exact (not_le_of_gt hlt) (le_trans hge_lb hmono)

private theorem swhileWP_mono (cond : CExpr) (inv : SProp) (body : CStmt) (Q : CVal → SProp) :
    ∀ {n m st}, n ≤ m → swhileWP n cond inv body Q st → swhileWP m cond inv body Q st := by
  intro n m st hnm hwp
  induction m generalizing n st with
  | zero =>
      have hn : n = 0 := Nat.eq_zero_of_le_zero hnm
      subst hn
      simpa using hwp
  | succ m ih =>
      cases n with
      | zero =>
          rcases hwp with ⟨hinv, hstep⟩
          cases hc : evalExpr cond st with
          | none =>
              simp [swhileWP, hc] at hstep
          | some v =>
              cases ht : isTruthy v with
              | true =>
                  simp [swhileWP, hc, ht] at hstep
              | false =>
                  simpa [swhileWP, hc, ht] using And.intro hinv hstep
      | succ n =>
          rcases hwp with ⟨hinv, hstep⟩
          cases hc : evalExpr cond st with
          | none =>
              simp [swhileWP, hc] at hstep
          | some v =>
              cases ht : isTruthy v with
              | true =>
                  have hstep' :
                      swp body (fun _ => swhileWP n cond inv body Q) st := by
                    simpa [swhileWP, hc, ht] using hstep
                  have hpost :
                      ∀ _ : CVal, (fun st' => swhileWP n cond inv body Q st') ⊢ₛₛ
                        (fun st' => swhileWP m cond inv body Q st') := by
                    intro _ st' hsmall
                    exact ih (Nat.le_of_succ_le_succ hnm) hsmall
                  have hbody :
                      swp body (fun _ => swhileWP m cond inv body Q) st := by
                    exact (HeytingLean.LeanCP.swp_mono body
                      (fun _ => swhileWP n cond inv body Q)
                      (fun _ => swhileWP m cond inv body Q)
                      hpost) st hstep'
                  simpa [swhileWP, hc, ht] using And.intro hinv hbody
              | false =>
                  simpa [swhileWP, hc, ht] using And.intro hinv hstep

private def binaryMid (lo hi : Nat) : Nat :=
  (lo + hi) / 2

private theorem binaryMid_bounds {lo hi : Nat} (hlohi : lo < hi) :
    lo ≤ binaryMid lo hi ∧ binaryMid lo hi < hi := by
  unfold binaryMid
  omega

private theorem binarySearch_loop_from_state
    (vals : List Int) (base : Nat) (target : Int)
    (hsorted : vals.Pairwise (· ≤ ·))
    (lo hi : Nat) (st : CState)
    (ha : st.lookupVar "a" = some (CVal.ptrAddr (base : PtrVal)))
    (hn : st.lookupVar "n" = some (.int (Int.ofNat vals.length)))
    (htarget : st.lookupVar "target" = some (.int target))
    (hlo : st.lookupVar "lo" = some (.int (Int.ofNat lo)))
    (hhi : st.lookupVar "hi" = some (.int (Int.ofNat hi)))
    (hlo_lb : lo ≤ lowerBoundIndex vals target)
    (hlb_hi : lowerBoundIndex vals target ≤ hi)
    (hhi_len : hi ≤ vals.length)
    (harray : arrayAt_s base vals st) :
    swhileWP (hi - lo) binarySearchCond (binarySearchInv vals base target)
      binarySearchLoopBody (binarySearchLoopPost vals base target) st := by
  by_cases hEq : lo = hi
  · have hInv : binarySearchInv vals base target st := by
      exact ⟨lo, hi, ha, hn, htarget, hlo, hhi, hlo_lb, hlb_hi, hhi_len, harray⟩
    have hlb_eq : lowerBoundIndex vals target = lo := by
      apply Nat.le_antisymm
      · simpa [hEq] using hlb_hi
      · exact hlo_lb
    have hCond : evalExpr binarySearchCond st = some (.int 0) := by
      simpa [binarySearchCond, evalExpr, evalStaticExpr, hlo, hhi, hEq] using
        (show evalBinOp .lt (.int (Int.ofNat lo)) (.int (Int.ofNat hi)) = some (.int 0) by
          change some (CVal.int (if Int.ofNat lo < Int.ofNat hi then 1 else 0)) =
            some (CVal.int 0)
          simp [hEq])
    have hPost : binarySearchLoopPost vals base target CVal.undef st := by
      refine ⟨?_, ?_, harray⟩
      · simpa [hlb_eq, hEq] using hlo
      · simpa [hlb_eq, hEq] using hhi
    have hDiffZero : hi - lo = 0 := by
      simp [hEq]
    simpa [swhileWP, hCond, isTruthy, hDiffZero] using And.intro hInv hPost
  · have hlohi : lo < hi := by
      omega
    let mid := binaryMid lo hi
    have hmid_lo : lo ≤ mid := (binaryMid_bounds hlohi).1
    have hmid_hi : mid < hi := (binaryMid_bounds hlohi).2
    have hmid_len : mid < vals.length := lt_of_lt_of_le hmid_hi hhi_len
    let st1 := st.updateVar "mid" (.int (Int.ofNat mid))

    have hEvalCond : evalExpr binarySearchCond st = some (.int 1) := by
      simpa [binarySearchCond, evalExpr, evalStaticExpr, hlo, hhi] using
        (show evalBinOp .lt (.int (Int.ofNat lo)) (.int (Int.ofNat hi)) = some (.int 1) by
          change some (CVal.int (if Int.ofNat lo < Int.ofNat hi then 1 else 0)) =
            some (CVal.int 1)
          simp [Int.ofNat_lt.mpr hlohi])

    have hEvalMid : evalExpr binarySearchMidExpr st = some (.int (Int.ofNat mid)) := by
      have hDiv :
          evalBinOp .div (.int (Int.ofNat (lo + hi))) (.int 2) =
            some (.int (Int.ofNat ((lo + hi) / 2))) := by
        change (if (2 : Int) ≠ 0 then some (CVal.int (Int.ofNat (lo + hi) / 2)) else none) =
          some (CVal.int (Int.ofNat ((lo + hi) / 2)))
        simp
      have hMidEq : Int.ofNat ((lo + hi) / 2) = Int.ofNat mid := by
        unfold mid binaryMid
        rfl
      simpa [binarySearchMidExpr, evalExpr, evalStaticExpr, hMidEq, hlo, hhi] using hDiv

    have ha1 : st1.lookupVar "a" = some (CVal.ptrAddr (base : PtrVal)) := by
      calc
        st1.lookupVar "a" = st.lookupVar "a" := by
          simpa [st1] using lookupVar_updateVar_ne st "mid" "a" (.int (Int.ofNat mid)) (by decide : "a" ≠ "mid")
        _ = some (CVal.ptrAddr (base : PtrVal)) := ha
    have hn1 : st1.lookupVar "n" = some (.int (Int.ofNat vals.length)) := by
      calc
        st1.lookupVar "n" = st.lookupVar "n" := by
          simpa [st1] using lookupVar_updateVar_ne st "mid" "n" (.int (Int.ofNat mid)) (by decide : "n" ≠ "mid")
        _ = some (.int (Int.ofNat vals.length)) := hn
    have htarget1 : st1.lookupVar "target" = some (.int target) := by
      calc
        st1.lookupVar "target" = st.lookupVar "target" := by
          simpa [st1] using lookupVar_updateVar_ne st "mid" "target" (.int (Int.ofNat mid)) (by decide : "target" ≠ "mid")
        _ = some (.int target) := htarget
    have hlo1 : st1.lookupVar "lo" = some (.int (Int.ofNat lo)) := by
      calc
        st1.lookupVar "lo" = st.lookupVar "lo" := by
          simpa [st1] using lookupVar_updateVar_ne st "mid" "lo" (.int (Int.ofNat mid)) (by decide : "lo" ≠ "mid")
        _ = some (.int (Int.ofNat lo)) := hlo
    have hhi1 : st1.lookupVar "hi" = some (.int (Int.ofNat hi)) := by
      calc
        st1.lookupVar "hi" = st.lookupVar "hi" := by
          simpa [st1] using lookupVar_updateVar_ne st "mid" "hi" (.int (Int.ofNat mid)) (by decide : "hi" ≠ "mid")
        _ = some (.int (Int.ofNat hi)) := hhi
    have hmid1 : st1.lookupVar "mid" = some (.int (Int.ofNat mid)) := by
      simpa [st1] using lookupVar_updateVar_eq st "mid" (.int (Int.ofNat mid))
    have harray1 : arrayAt_s base vals st1 := by
      simpa [st1] using (arrayAt_s_updateVar base vals st "mid" (.int (Int.ofNat mid))).2 harray

    have hReadMid : st1.heap.read (base + mid) = some (.int vals[mid]) := by
      exact harray1 mid vals[mid] (by simp [List.getElem?_eq_getElem hmid_len])
    have hEvalPtrMid :
        evalExpr (.binop .add (.var "a") (.var "mid")) st1 =
          some (CVal.ptrAddr ((base + mid) : PtrVal)) := by
      simpa [evalExpr, evalStaticExpr, ha1, hmid1] using
        (show evalBinOp .add (CVal.ptrAddr (base : PtrVal)) (.int (Int.ofNat mid)) =
            some (CVal.ptrAddr ((base + mid) : PtrVal)) by
          change (if 0 ≤ Int.ofNat mid then
              some (CVal.ptrAddr { block := 0, offset := Int.ofNat base + Int.ofNat mid })
            else none) = some (CVal.ptrAddr ((base + mid) : PtrVal))
          simp)
    have hReadPtrMid : st1.readPtr (base + mid) = some (.int vals[mid]) := by
      simpa [hReadMid] using (CState.readPtr_block0 st1 (base + mid) (base + mid))
    have hEvalDerefMid :
        evalExpr (.deref (.binop .add (.var "a") (.var "mid"))) st1 =
          some (.int vals[mid]) := by
      simpa [evalExpr, evalStaticExpr, hEvalPtrMid] using hReadPtrMid

    by_cases hBranch : vals[mid] < target
    · let st2 := st1.updateVar "lo" (.int (Int.ofNat (mid + 1)))
      have hEvalBranch :
          evalExpr binarySearchBranchCond st1 = some (.int 1) := by
        simpa [binarySearchBranchCond, evalExpr, evalStaticExpr, hEvalDerefMid, htarget1] using
          (show evalBinOp .lt (.int vals[mid]) (.int target) = some (.int 1) by
            change some (CVal.int (if vals[mid] < target then 1 else 0)) = some (CVal.int 1)
            simp [hBranch])
      have hmid_lb : mid < lowerBoundIndex vals target :=
        lt_lowerBoundIndex_of_get_lt_target hsorted target hmid_len hBranch
      have hlo2 : st2.lookupVar "lo" = some (.int (Int.ofNat (mid + 1))) := by
        simpa [st2] using lookupVar_updateVar_eq st1 "lo" (.int (Int.ofNat (mid + 1)))
      have hhi2 : st2.lookupVar "hi" = some (.int (Int.ofNat hi)) := by
        calc
          st2.lookupVar "hi" = st1.lookupVar "hi" := by
            simpa [st2] using lookupVar_updateVar_ne st1 "lo" "hi" (.int (Int.ofNat (mid + 1))) (by decide : "hi" ≠ "lo")
          _ = some (.int (Int.ofNat hi)) := hhi1
      have ha2 : st2.lookupVar "a" = some (CVal.ptrAddr (base : PtrVal)) := by
        calc
          st2.lookupVar "a" = st1.lookupVar "a" := by
            simpa [st2] using lookupVar_updateVar_ne st1 "lo" "a" (.int (Int.ofNat (mid + 1))) (by decide : "a" ≠ "lo")
          _ = some (CVal.ptrAddr (base : PtrVal)) := ha1
      have hn2 : st2.lookupVar "n" = some (.int (Int.ofNat vals.length)) := by
        calc
          st2.lookupVar "n" = st1.lookupVar "n" := by
            simpa [st2] using lookupVar_updateVar_ne st1 "lo" "n" (.int (Int.ofNat (mid + 1))) (by decide : "n" ≠ "lo")
          _ = some (.int (Int.ofNat vals.length)) := hn1
      have htarget2 : st2.lookupVar "target" = some (.int target) := by
        calc
          st2.lookupVar "target" = st1.lookupVar "target" := by
            simpa [st2] using lookupVar_updateVar_ne st1 "lo" "target" (.int (Int.ofNat (mid + 1))) (by decide : "target" ≠ "lo")
          _ = some (.int target) := htarget1
      have harray2 : arrayAt_s base vals st2 := by
        simpa [st2] using (arrayAt_s_updateVar base vals st1 "lo" (.int (Int.ofNat (mid + 1)))).2 harray1
      have hLoop2 :
          swhileWP (hi - (mid + 1)) binarySearchCond (binarySearchInv vals base target)
            binarySearchLoopBody (binarySearchLoopPost vals base target) st2 := by
        exact binarySearch_loop_from_state vals base target hsorted (mid + 1) hi st2
          ha2 hn2 htarget2 hlo2 hhi2 (Nat.succ_le_of_lt hmid_lb) hlb_hi hhi_len harray2
      have hBudget :
          hi - (mid + 1) ≤ hi - lo - 1 := by
        omega
      have hLoop2' :
          swhileWP (hi - lo - 1) binarySearchCond (binarySearchInv vals base target)
            binarySearchLoopBody (binarySearchLoopPost vals base target) st2 := by
        exact swhileWP_mono binarySearchCond (binarySearchInv vals base target)
          binarySearchLoopBody (binarySearchLoopPost vals base target) hBudget hLoop2
      have hAssignLo :
          swp (.assign (.var "lo") (.binop .add (.var "mid") (.intLit 1)))
            (fun _ => swhileWP (hi - lo - 1) binarySearchCond
              (binarySearchInv vals base target) binarySearchLoopBody
              (binarySearchLoopPost vals base target)) st1 := by
        have hEvalLo :
            evalExpr (.binop .add (.var "mid") (.intLit 1)) st1 =
              some (.int (Int.ofNat (mid + 1))) := by
          simpa [evalExpr, evalStaticExpr, hmid1] using
            (show evalBinOp .add (.int (Int.ofNat mid)) (.int 1) =
                some (.int (Int.ofNat (mid + 1))) by
              change some (CVal.int (Int.ofNat mid + 1)) = some (CVal.int (Int.ofNat (mid + 1)))
              simp)
        simpa [swp, hEvalLo, st2] using hLoop2'
      have hIte :
          swp (.ite binarySearchBranchCond
              (.assign (.var "lo") (.binop .add (.var "mid") (.intLit 1)))
              (.assign (.var "hi") (.var "mid")))
            (fun _ => swhileWP (hi - lo - 1) binarySearchCond
              (binarySearchInv vals base target) binarySearchLoopBody
              (binarySearchLoopPost vals base target)) st1 := by
        simpa [swp, hEvalBranch] using hAssignLo
      have hBody :
          swp binarySearchLoopBody
            (fun _ => swhileWP (hi - lo - 1) binarySearchCond
              (binarySearchInv vals base target) binarySearchLoopBody
              (binarySearchLoopPost vals base target)) st := by
        simpa [binarySearchLoopBody, swp, hEvalMid, st1] using hIte
      have hInv : binarySearchInv vals base target st := by
        exact ⟨lo, hi, ha, hn, htarget, hlo, hhi, hlo_lb, hlb_hi, hhi_len, harray⟩
      have hDiffSucc : hi - lo = Nat.succ (hi - lo - 1) := by
        omega
      have hLoop :
          swhileWP (Nat.succ (hi - lo - 1)) binarySearchCond
            (binarySearchInv vals base target) binarySearchLoopBody
            (binarySearchLoopPost vals base target) st := by
        simpa [swhileWP, hEvalCond] using And.intro hInv hBody
      exact hDiffSucc ▸ hLoop
    · let st2 := st1.updateVar "hi" (.int (Int.ofNat mid))
      have hTargetLeMid : target ≤ vals[mid] := le_of_not_gt hBranch
      have hEvalBranch :
          evalExpr binarySearchBranchCond st1 = some (.int 0) := by
        simpa [binarySearchBranchCond, evalExpr, evalStaticExpr, hEvalDerefMid, htarget1] using
          (show evalBinOp .lt (.int vals[mid]) (.int target) = some (.int 0) by
            change some (CVal.int (if vals[mid] < target then 1 else 0)) = some (CVal.int 0)
            simp [hBranch])
      have hlb_mid : lowerBoundIndex vals target ≤ mid :=
        lowerBoundIndex_le_of_target_le_get vals target hmid_len hTargetLeMid
      have hlo2 : st2.lookupVar "lo" = some (.int (Int.ofNat lo)) := by
        calc
          st2.lookupVar "lo" = st1.lookupVar "lo" := by
            simpa [st2] using lookupVar_updateVar_ne st1 "hi" "lo" (.int (Int.ofNat mid)) (by decide : "lo" ≠ "hi")
          _ = some (.int (Int.ofNat lo)) := hlo1
      have hhi2 : st2.lookupVar "hi" = some (.int (Int.ofNat mid)) := by
        simpa [st2] using lookupVar_updateVar_eq st1 "hi" (.int (Int.ofNat mid))
      have ha2 : st2.lookupVar "a" = some (CVal.ptrAddr (base : PtrVal)) := by
        calc
          st2.lookupVar "a" = st1.lookupVar "a" := by
            simpa [st2] using lookupVar_updateVar_ne st1 "hi" "a" (.int (Int.ofNat mid)) (by decide : "a" ≠ "hi")
          _ = some (CVal.ptrAddr (base : PtrVal)) := ha1
      have hn2 : st2.lookupVar "n" = some (.int (Int.ofNat vals.length)) := by
        calc
          st2.lookupVar "n" = st1.lookupVar "n" := by
            simpa [st2] using lookupVar_updateVar_ne st1 "hi" "n" (.int (Int.ofNat mid)) (by decide : "n" ≠ "hi")
          _ = some (.int (Int.ofNat vals.length)) := hn1
      have htarget2 : st2.lookupVar "target" = some (.int target) := by
        calc
          st2.lookupVar "target" = st1.lookupVar "target" := by
            simpa [st2] using lookupVar_updateVar_ne st1 "hi" "target" (.int (Int.ofNat mid)) (by decide : "target" ≠ "hi")
          _ = some (.int target) := htarget1
      have harray2 : arrayAt_s base vals st2 := by
        simpa [st2] using (arrayAt_s_updateVar base vals st1 "hi" (.int (Int.ofNat mid))).2 harray1
      have hLoop2 :
          swhileWP (mid - lo) binarySearchCond (binarySearchInv vals base target)
            binarySearchLoopBody (binarySearchLoopPost vals base target) st2 := by
        exact binarySearch_loop_from_state vals base target hsorted lo mid st2
          ha2 hn2 htarget2 hlo2 hhi2 hlo_lb hlb_mid (le_trans (Nat.le_of_lt hmid_hi) hhi_len) harray2
      have hBudget :
          mid - lo ≤ hi - lo - 1 := by
        omega
      have hLoop2' :
          swhileWP (hi - lo - 1) binarySearchCond (binarySearchInv vals base target)
            binarySearchLoopBody (binarySearchLoopPost vals base target) st2 := by
        exact swhileWP_mono binarySearchCond (binarySearchInv vals base target)
          binarySearchLoopBody (binarySearchLoopPost vals base target) hBudget hLoop2
      have hAssignHi :
          swp (.assign (.var "hi") (.var "mid"))
            (fun _ => swhileWP (hi - lo - 1) binarySearchCond
              (binarySearchInv vals base target) binarySearchLoopBody
              (binarySearchLoopPost vals base target)) st1 := by
        have hEvalHi : evalExpr (.var "mid") st1 = some (.int (Int.ofNat mid)) := by
          simpa [evalExpr, evalStaticExpr] using hmid1
        simpa [swp, hEvalHi, st2] using hLoop2'
      have hIte :
          swp (.ite binarySearchBranchCond
              (.assign (.var "lo") (.binop .add (.var "mid") (.intLit 1)))
              (.assign (.var "hi") (.var "mid")))
            (fun _ => swhileWP (hi - lo - 1) binarySearchCond
              (binarySearchInv vals base target) binarySearchLoopBody
              (binarySearchLoopPost vals base target)) st1 := by
        simpa [swp, hEvalBranch] using hAssignHi
      have hBody :
          swp binarySearchLoopBody
            (fun _ => swhileWP (hi - lo - 1) binarySearchCond
              (binarySearchInv vals base target) binarySearchLoopBody
              (binarySearchLoopPost vals base target)) st := by
        simpa [binarySearchLoopBody, swp, hEvalMid, st1] using hIte
      have hInv : binarySearchInv vals base target st := by
        exact ⟨lo, hi, ha, hn, htarget, hlo, hhi, hlo_lb, hlb_hi, hhi_len, harray⟩
      have hDiffSucc : hi - lo = Nat.succ (hi - lo - 1) := by
        omega
      have hLoop :
          swhileWP (Nat.succ (hi - lo - 1)) binarySearchCond
            (binarySearchInv vals base target) binarySearchLoopBody
            (binarySearchLoopPost vals base target) st := by
        simpa [swhileWP, hEvalCond] using And.intro hInv hBody
      exact hDiffSucc ▸ hLoop
termination_by hi - lo
decreasing_by
  all_goals
    unfold binaryMid
    omega

def binarySearchInit : CState :=
  { heap := (((Heap.empty.write 100 (.int 2)).write 101 (.int 4)).write 102 (.int 6)).write 103 (.int 8)
    env := [("a", .ptr 0 100), ("n", .int 4), ("target", .int 6)]
    nextAddr := 200 }

def binarySearchFinal : CState :=
  { heap := (((Heap.empty.write 100 (.int 2)).write 101 (.int 4)).write 102 (.int 6)).write 103 (.int 8)
    env := [("lo", .int 2), ("mid", .int 1), ("hi", .int 2),
      ("a", .ptr 0 100), ("n", .int 4), ("target", .int 6)]
    nextAddr := 200 }

theorem binarySearch_correct (vals : List Int) (base : Nat) (target : Int)
    (hsorted : vals.Pairwise (· ≤ ·)) :
    ∀ st,
      st.lookupVar "a" = some (CVal.ptrAddr (base : PtrVal)) →
      st.lookupVar "n" = some (.int (Int.ofNat vals.length)) →
      st.lookupVar "target" = some (.int target) →
      arrayAt_s base vals st →
      ∃ st',
        execStmt (swhileFuel binarySearchLoopBody vals.length + 3) binarySearchBody st =
          some (.returned (.int (Int.ofNat (lowerBoundIndex vals target))) st') ∧
        arrayAt_s base vals st' := by
  intro st ha hn htarget harray
  let st1 := st.updateVar "lo" (.int 0)
  let st2 := st1.updateVar "hi" (.int (Int.ofNat vals.length))

  have ha1 : st1.lookupVar "a" = some (CVal.ptrAddr (base : PtrVal)) := by
    calc
      st1.lookupVar "a" = st.lookupVar "a" := by
        simpa [st1] using lookupVar_updateVar_ne st "lo" "a" (.int 0) (by decide : "a" ≠ "lo")
      _ = some (CVal.ptrAddr (base : PtrVal)) := ha
  have hn1 : st1.lookupVar "n" = some (.int (Int.ofNat vals.length)) := by
    calc
      st1.lookupVar "n" = st.lookupVar "n" := by
        simpa [st1] using lookupVar_updateVar_ne st "lo" "n" (.int 0) (by decide : "n" ≠ "lo")
      _ = some (.int (Int.ofNat vals.length)) := hn
  have htarget1 : st1.lookupVar "target" = some (.int target) := by
    calc
      st1.lookupVar "target" = st.lookupVar "target" := by
        simpa [st1] using lookupVar_updateVar_ne st "lo" "target" (.int 0) (by decide : "target" ≠ "lo")
      _ = some (.int target) := htarget
  have ha2 : st2.lookupVar "a" = some (CVal.ptrAddr (base : PtrVal)) := by
    calc
      st2.lookupVar "a" = st1.lookupVar "a" := by
        simpa [st2] using lookupVar_updateVar_ne st1 "hi" "a" (.int (Int.ofNat vals.length)) (by decide : "a" ≠ "hi")
      _ = some (CVal.ptrAddr (base : PtrVal)) := ha1
  have hn2 : st2.lookupVar "n" = some (.int (Int.ofNat vals.length)) := by
    calc
      st2.lookupVar "n" = st1.lookupVar "n" := by
        simpa [st2] using lookupVar_updateVar_ne st1 "hi" "n" (.int (Int.ofNat vals.length)) (by decide : "n" ≠ "hi")
      _ = some (.int (Int.ofNat vals.length)) := hn1
  have htarget2 : st2.lookupVar "target" = some (.int target) := by
    calc
      st2.lookupVar "target" = st1.lookupVar "target" := by
        simpa [st2] using lookupVar_updateVar_ne st1 "hi" "target" (.int (Int.ofNat vals.length)) (by decide : "target" ≠ "hi")
      _ = some (.int target) := htarget1
  have hlo2 : st2.lookupVar "lo" = some (.int 0) := by
    calc
      st2.lookupVar "lo" = st1.lookupVar "lo" := by
        simpa [st2] using lookupVar_updateVar_ne st1 "hi" "lo" (.int (Int.ofNat vals.length)) (by decide : "lo" ≠ "hi")
      _ = some (.int 0) := by
        simpa [st1] using lookupVar_updateVar_eq st "lo" (.int 0)
  have hhi2 : st2.lookupVar "hi" = some (.int (Int.ofNat vals.length)) := by
    simpa [st2] using lookupVar_updateVar_eq st1 "hi" (.int (Int.ofNat vals.length))
  have harray1 : arrayAt_s base vals st1 := by
    simpa [st1] using (arrayAt_s_updateVar base vals st "lo" (.int 0)).2 harray
  have harray2 : arrayAt_s base vals st2 := by
    simpa [st2] using (arrayAt_s_updateVar base vals st1 "hi" (.int (Int.ofNat vals.length))).2 harray1

  have hLoopWP :
      swhileWP vals.length binarySearchCond (binarySearchInv vals base target)
        binarySearchLoopBody (binarySearchLoopPost vals base target) st2 := by
    have hlo_lb : 0 ≤ lowerBoundIndex vals target := Nat.zero_le _
    have hlb_hi : lowerBoundIndex vals target ≤ vals.length := lowerBoundIndex_le_length vals target
    exact binarySearch_loop_from_state vals base target hsorted 0 vals.length st2
      ha2 hn2 htarget2 hlo2 hhi2 hlo_lb hlb_hi (le_rfl) harray2

  have hLoopExec :
      ∃ stLoop,
        execStmt (swhileFuel binarySearchLoopBody vals.length)
          (.whileInv binarySearchCond HProp.htrue binarySearchLoopBody) st2 = some (.normal stLoop) ∧
        binarySearchLoopPost vals base target CVal.undef stLoop := by
    exact swhileWP_sound binarySearchCond (binarySearchInv vals base target) HProp.htrue
      binarySearchLoopBody binarySearch_loopFree binarySearch_noReturn hLoopWP
  rcases hLoopExec with ⟨stLoop, hExecLoop, hPostLoop⟩
  rcases hPostLoop with ⟨hloLoop, hhiLoop, harrayLoop⟩

  have hRet :
      execStmt (swhileFuel binarySearchLoopBody vals.length) (.ret (.var "lo")) stLoop =
        some (.returned (.int (Int.ofNat (lowerBoundIndex vals target))) stLoop) := by
    change execStmt (Nat.succ (stmtDepth binarySearchLoopBody + vals.length)) (.ret (.var "lo")) stLoop =
      some (.returned (.int (Int.ofNat (lowerBoundIndex vals target))) stLoop)
    simp [execStmt, evalExpr, hloLoop]
  let loopFuel := swhileFuel binarySearchLoopBody vals.length
  have hExecInner :
      execStmt (loopFuel + 1)
        (.seq (.whileInv binarySearchCond HProp.htrue binarySearchLoopBody) (.ret (.var "lo"))) st2 =
          some (.returned (.int (Int.ofNat (lowerBoundIndex vals target))) stLoop) := by
    change execStmt (loopFuel + 1)
      (.seq (.whileInv binarySearchCond HProp.htrue binarySearchLoopBody) (.ret (.var "lo"))) st2 =
        some (.returned (.int (Int.ofNat (lowerBoundIndex vals target))) stLoop)
    simp [execStmt]
    rw [hExecLoop]
    simpa [hRet]
  have hExecRest :
      execStmt (loopFuel + 2)
        (.seq (.assign (.var "hi") (.var "n"))
          (.seq (.whileInv binarySearchCond HProp.htrue binarySearchLoopBody) (.ret (.var "lo")))) st1 =
          some (.returned (.int (Int.ofNat (lowerBoundIndex vals target))) stLoop) := by
    change execStmt (Nat.succ (loopFuel + 1))
      (.seq (.assign (.var "hi") (.var "n"))
        (.seq (.whileInv binarySearchCond HProp.htrue binarySearchLoopBody) (.ret (.var "lo")))) st1 =
          some (.returned (.int (Int.ofNat (lowerBoundIndex vals target))) stLoop)
    have hEvalN1 : evalExpr (.var "n") st1 = some (.int (Int.ofNat vals.length)) := by
      simpa [evalExpr, evalStaticExpr] using hn1
    simpa [execStmt, hEvalN1, st2] using hExecInner
  have hExecStart :
      execStmt (loopFuel + 3) binarySearchBody st =
        some (.returned (.int (Int.ofNat (lowerBoundIndex vals target))) stLoop) := by
    change execStmt (Nat.succ (loopFuel + 2)) binarySearchBody st =
      some (.returned (.int (Int.ofNat (lowerBoundIndex vals target))) stLoop)
    have hEvalLo0 : evalExpr (.intLit 0) st = some (.int 0) := by
      rfl
    simpa [binarySearchBody, execStmt, hEvalLo0, st1] using hExecRest
  refine ⟨stLoop, ?_, harrayLoop⟩
  change execStmt (loopFuel + 3) binarySearchBody st =
    some (.returned (.int (Int.ofNat (lowerBoundIndex vals target))) stLoop)
  exact hExecStart

theorem binarySearch_executes :
    execStmt 12 binarySearchBody binarySearchInit =
      some (.returned (.int 2) binarySearchFinal) := by
  native_decide

theorem binarySearch_verified :
    ∃ st',
      execStmt 12 binarySearchBody binarySearchInit =
        some (.returned (.int 2) st') ∧
      st'.heap.read 100 = some (.int 2) ∧
      st'.heap.read 101 = some (.int 4) ∧
      st'.heap.read 102 = some (.int 6) ∧
      st'.heap.read 103 = some (.int 8) := by
  refine ⟨binarySearchFinal, binarySearch_executes, ?_, ?_, ?_, ?_⟩ <;>
    simp [binarySearchFinal]

theorem binarySearch_init_verified :
    swp (.assign (.var "lo") (.intLit 0))
      (fun _ st => st.lookupVar "lo" = some (.int 0))
      binarySearchInit := by
  simp [swp, binarySearchInit, evalExpr, evalStaticExpr,
    CState.lookupVar, CState.updateVar]

end HeytingLean.LeanCP.Examples
