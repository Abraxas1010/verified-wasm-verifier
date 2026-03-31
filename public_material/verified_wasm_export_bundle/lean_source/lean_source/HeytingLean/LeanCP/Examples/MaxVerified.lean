import HeytingLean.LeanCP.VCG.SWPSound

/-!
# LeanCP Example: Verified Max

State-sensitive verification of a conditional early-return program.
-/

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

def maxBody : CStmt :=
  .ite (.binop .gt (.var "a") (.var "b"))
    (.ret (.var "a"))
    (.ret (.var "b"))

def maxSSpec (a b : Int) : SFunSpec where
  name := "max_state_sensitive"
  params := [("a", .int), ("b", .int)]
  retType := .int
  pre := fun st =>
    st.lookupVar "a" = some (.int a) ∧
    st.lookupVar "b" = some (.int b)
  post := fun retVal _st =>
    retVal = .int (if a > b then a else b)
  body := maxBody

private theorem max_loopFree : LoopFree maxBody := by
  simp [maxBody, LoopFree]

private theorem max_tailReturn : TailReturn maxBody := by
  simp [maxBody, TailReturn]

theorem max_verified (a b : Int) :
    sgenVC (maxSSpec a b) := by
  intro st hpre
  rcases hpre with ⟨ha, hb⟩
  change swp maxBody (maxSSpec a b).post st
  have hEvalA : evalExpr (.var "a") st = some (.int a) := by
    simpa [evalExpr] using ha
  have hEvalB : evalExpr (.var "b") st = some (.int b) := by
    simpa [evalExpr] using hb
  by_cases hgt : a > b
  · have hCond : evalExpr (.binop .gt (.var "a") (.var "b")) st = some (.int 1) := by
        simpa [evalExpr, evalStaticExpr, ha, hb, hgt] using
          (show evalBinOp .gt (.int a) (.int b) = some (.int 1) by
            change some (CVal.int (if a > b then 1 else 0)) = some (CVal.int 1)
            simp [hgt])
    simpa [maxBody, swp, maxSSpec, hCond, isTruthy, hEvalA, hgt]
  · have hCond : evalExpr (.binop .gt (.var "a") (.var "b")) st = some (.int 0) := by
        simpa [evalExpr, evalStaticExpr, ha, hb, hgt] using
          (show evalBinOp .gt (.int a) (.int b) = some (.int 0) by
            change some (CVal.int (if a > b then 1 else 0)) = some (CVal.int 0)
            simp [hgt])
    simpa [maxBody, swp, maxSSpec, hCond, isTruthy, hEvalB, hgt]

theorem max_executes (a b : Int) {st fuel}
    (hpre : (maxSSpec a b).pre st)
    (hfuel : stmtDepth maxBody ≤ fuel) :
    ∃ res, execStmt fuel maxBody st = some res ∧
      match res with
      | .returned v st' => (maxSSpec a b).post v st'
      | .normal st' => (maxSSpec a b).post CVal.undef st' := by
  have hvc : swp maxBody (maxSSpec a b).post st :=
    max_verified a b st hpre
  exact swp_sound maxBody max_loopFree max_tailReturn hfuel hvc

end HeytingLean.LeanCP.Examples
