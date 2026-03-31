import HeytingLean.LeanCP.Examples.ListReverseVerified
import HeytingLean.LeanCP.Tactics.Forward

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

set_option linter.unnecessarySimpa false

attribute [leancp_unfold] listRevProgram

private theorem listRev_loopFree_tactic : LoopFree listRevLoopBody := by
  simp [listRevLoopBody, LoopFree]

private theorem listRev_noReturn_tactic : NoReturn listRevLoopBody := by
  simp [listRevLoopBody, NoReturn]

theorem listRev_correct_tactic (sigma : List Int) (p : CVal) :
    ∀ st, st.lookupVar "p" = some p →
      sll_s p sigma st →
      sll_s_exec p sigma st →
      ∃ w st',
        execStmt (swhileFuel listRevLoopBody sigma.length + 3) listRevProgram st =
          some (.returned w st') ∧
        sll_s w sigma.reverse st' := by
  intro st hp hsll hsExec
  let st1 := st.updateVar "w" .null
  let st2 := st1.updateVar "v" p

  have hp1 : st1.lookupVar "p" = some p := by
    have hpw : "p" ≠ "w" := by decide
    calc
      st1.lookupVar "p" = st.lookupVar "p" := by
        simpa [st1] using lookupVar_updateVar_ne st "w" "p" CVal.null hpw
      _ = some p := hp
  have hw2 : st2.lookupVar "w" = some .null := by
    have hwv : "w" ≠ "v" := by decide
    calc
      st2.lookupVar "w" = st1.lookupVar "w" := by
        simpa [st2] using lookupVar_updateVar_ne st1 "v" "w" p hwv
      _ = some .null := by
        simpa [st1] using lookupVar_updateVar_eq st "w" .null
  have hv2 : st2.lookupVar "v" = some p := by
    simpa [st2] using lookupVar_updateVar_eq st1 "v" p
  have hInit : listRevInv sigma st2 := by
    simpa [st1, st2] using listRev_inv_init sigma p st hp hsll hsExec
  rcases hInit with ⟨s1, s2, w, v, hsigma, hw, hv, hsllW, hsllV, hsExecV, hdis⟩
  have hwEq : w = .null := Option.some.inj (hw.symm.trans hw2)
  have hvEq : v = p := Option.some.inj (hv.symm.trans hv2)
  subst w v
  have hs1nil : s1 = [] := (sll_s_null_iff s1 st2).mp hsllW
  subst s1
  have hs2sigma : s2 = sigma := by
    simpa using hsigma.symm
  subst s2
  have hLoopWP :
      swhileWP sigma.length (.var "v") (listRevInv sigma) listRevLoopBody (listRevPost sigma) st2 := by
    exact listRev_loop_from_state sigma [] sigma .null p st2 (by simp) hw2 hv2 hsllW hsllV hsExecV hdis
  have hLoopExec :
      ∃ stLoop,
        execStmt (swhileFuel listRevLoopBody sigma.length)
          (.whileInv (.var "v") HProp.htrue listRevLoopBody) st2 = some (.normal stLoop) ∧
        listRevPost sigma CVal.undef stLoop := by
    exact swhileWP_sound (.var "v") (listRevInv sigma) HProp.htrue listRevLoopBody
      listRev_loopFree_tactic listRev_noReturn_tactic hLoopWP
  rcases hLoopExec with ⟨stLoop, hExecLoop, hPostLoop⟩
  rcases hPostLoop with ⟨w, hwLoop, hsllLoop⟩

  refine ⟨w, stLoop, ?_, hsllLoop⟩
  have hRet :
      execStmt (swhileFuel listRevLoopBody sigma.length) (.ret (.var "w")) stLoop =
        some (.returned w stLoop) := by
    change execStmt (Nat.succ (stmtDepth listRevLoopBody + sigma.length)) (.ret (.var "w")) stLoop =
      some (.returned w stLoop)
    simp [execStmt, hwLoop]
  let loopFuel := swhileFuel listRevLoopBody sigma.length
  have hExecInner :
      execStmt (loopFuel + 1)
        (.seq (.whileInv (.var "v") HProp.htrue listRevLoopBody) (.ret (.var "w"))) st2 =
          some (.returned w stLoop) := by
    change execStmt (loopFuel + 1)
      (.seq (.whileInv (.var "v") HProp.htrue listRevLoopBody) (.ret (.var "w"))) st2 =
        some (.returned w stLoop)
    simp [execStmt]
    rw [hExecLoop]
    simpa [hRet]
  have hExecRest :
      execStmt (loopFuel + 2)
        (.seq (.assign (.var "v") (.var "p"))
          (.seq (.whileInv (.var "v") HProp.htrue listRevLoopBody) (.ret (.var "w")))) st1 =
          some (.returned w stLoop) := by
    change execStmt (Nat.succ (loopFuel + 1))
      (.seq (.assign (.var "v") (.var "p"))
        (.seq (.whileInv (.var "v") HProp.htrue listRevLoopBody) (.ret (.var "w")))) st1 =
          some (.returned w stLoop)
    have hEvalP1 : evalExpr (.var "p") st1 = some p := by
      simpa [evalExpr] using hp1
    simpa [execStmt, hEvalP1, st2] using hExecInner
  change execStmt (Nat.succ (loopFuel + 2)) listRevProgram st =
    some (.returned w stLoop)
  have hEvalNull : evalExpr .null st = some .null := by
    simp [evalExpr, evalStaticExpr]
  simpa [listRevProgram, execStmt, hEvalNull, st1] using hExecRest

end HeytingLean.LeanCP.Examples
