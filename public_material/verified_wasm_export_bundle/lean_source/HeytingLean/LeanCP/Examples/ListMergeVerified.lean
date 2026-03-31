import HeytingLean.LeanCP.Examples.ListMerge
import HeytingLean.LeanCP.Lang.CSemanticsDecEq
import HeytingLean.LeanCP.Predicates.SLL
import HeytingLean.LeanCP.Tactics.Forward

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

set_option maxHeartbeats 1000000

/-- The current simplified merge body returns `b` when `a` is null and
otherwise returns `a`; it does not yet perform list interleaving. -/
def mergeResult (a b : CVal) : CVal :=
  if a = .null then b else a

private def mergeReturns (st : CState) (ret : CVal) : Prop :=
  execStmt 8 mergeBody st = some (.returned ret st)

private theorem evalEqNull_zero_of_sll_s_ne_null
    {ptr : CVal} {xs : List Int} {st : CState}
    (hsll : sll_s ptr xs st) (hptr : ptr ≠ .null) :
    evalBinOp .eq ptr .null = some (.int 0) := by
  cases xs with
  | nil =>
      have hnull : ptr = .null := sll_s_nil_ptr_eq_null hsll
      exact False.elim (hptr hnull)
  | cons x rest =>
      cases ptr with
      | null =>
          exact False.elim (hptr rfl)
      | int n =>
          simp [sll_s, ptrBase?] at hsll
      | uint n sz =>
          simp [sll_s, ptrBase?] at hsll
      | undef =>
          simp [sll_s, ptrBase?] at hsll
      | structVal fields =>
          simp [sll_s, ptrBase?] at hsll
      | unionVal tag val =>
          simp [sll_s, ptrBase?] at hsll
      | float v =>
          simp [sll_s, ptrBase?] at hsll
      | ptr block offset =>
          rfl

private theorem merge_executes_when_a_null
    (st : CState) (b : CVal)
    (ha : st.lookupVar "a" = some .null)
    (hb : st.lookupVar "b" = some b) :
    mergeReturns st b := by
  unfold mergeReturns
  have hEvalA :
      evalExpr (.binop .eq (.var "a") .null) st = some (.int 1) := by
    simpa [evalExpr, evalStaticExpr, ha] using
      (show evalBinOp .eq .null .null = some (.int 1) by rfl)
  simp [mergeBody, execStmt, hEvalA, hb, evalExpr, isTruthy]

private theorem merge_executes_when_a_nonnull_b_null
    (st : CState) (a : CVal)
    (ha : st.lookupVar "a" = some a)
    (hb : st.lookupVar "b" = some .null)
    (hEqA : evalBinOp .eq a .null = some (.int 0)) :
    mergeReturns st a := by
  unfold mergeReturns
  have hEvalA :
      evalExpr (.binop .eq (.var "a") .null) st = some (.int 0) := by
    simpa [evalExpr, evalStaticExpr, ha] using hEqA
  have hEvalB :
      evalExpr (.binop .eq (.var "b") .null) st = some (.int 1) := by
    simpa [evalExpr, evalStaticExpr, hb] using
      (show evalBinOp .eq .null .null = some (.int 1) by rfl)
  simp [mergeBody, execStmt, hEvalA, hEvalB, ha, isTruthy]

private theorem merge_executes_when_a_nonnull_b_nonnull
    (st : CState) (a b : CVal)
    (ha : st.lookupVar "a" = some a)
    (hb : st.lookupVar "b" = some b)
    (hEqA : evalBinOp .eq a .null = some (.int 0))
    (hEqB : evalBinOp .eq b .null = some (.int 0)) :
    mergeReturns st a := by
  unfold mergeReturns
  have hEvalA :
      evalExpr (.binop .eq (.var "a") .null) st = some (.int 0) := by
    simpa [evalExpr, evalStaticExpr, ha] using hEqA
  have hEvalB :
      evalExpr (.binop .eq (.var "b") .null) st = some (.int 0) := by
    simpa [evalExpr, evalStaticExpr, hb] using hEqB
  simp [mergeBody, execStmt, hEvalA, hEvalB, ha, isTruthy]

theorem merge_correct (la lb : List Int) (a b : CVal) :
    ∀ st,
      st.lookupVar "a" = some a →
      st.lookupVar "b" = some b →
      sll_s a la st →
      sll_s b lb st →
      ∃ st',
        execStmt 8 mergeBody st = some (.returned (mergeResult a b) st') ∧
        st'.lookupVar "a" = some a ∧
        st'.lookupVar "b" = some b ∧
        sll_s a la st' ∧
        sll_s b lb st' := by
  intro st ha hb hslla hsllb
  refine ⟨st, ?_, ha, hb, hslla, hsllb⟩
  by_cases hnull : a = .null
  · subst a
    simpa [mergeReturns, mergeResult] using merge_executes_when_a_null st b ha hb
  · have hEqA : evalBinOp .eq a .null = some (.int 0) := by
      exact evalEqNull_zero_of_sll_s_ne_null hslla hnull
    by_cases hbnull : b = .null
    · subst b
      simpa [mergeReturns, mergeResult, hnull] using
        merge_executes_when_a_nonnull_b_null st a ha hb hEqA
    · have hEqB : evalBinOp .eq b .null = some (.int 0) := by
        exact evalEqNull_zero_of_sll_s_ne_null hsllb hbnull
      simpa [mergeReturns, mergeResult, hnull] using
        merge_executes_when_a_nonnull_b_nonnull st a b ha hb hEqA hEqB

def mergeInit : CState :=
  { heap := Heap.empty
    env := [("a", .null), ("b", .ptr 0 200)]
    nextAddr := 300 }

def mergeFinal : CState :=
  { heap := Heap.empty
    env := [("a", .null), ("b", .ptr 0 200)]
    nextAddr := 300 }

theorem merge_executes :
    execStmt 8 mergeBody mergeInit = some (.returned (.ptr 0 200) mergeFinal) := by
  native_decide

theorem merge_verified :
    ∃ st',
      execStmt 8 mergeBody mergeInit = some (.returned (.ptr 0 200) st') ∧
      st'.lookupVar "a" = some .null ∧
      st'.lookupVar "b" = some (.ptr 0 200) := by
  refine ⟨mergeFinal, merge_executes, ?_, ?_⟩
  · native_decide
  · native_decide

end HeytingLean.LeanCP.Examples
