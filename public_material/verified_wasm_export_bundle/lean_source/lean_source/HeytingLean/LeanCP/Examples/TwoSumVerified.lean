import HeytingLean.LeanCP.VCG.SWPSound

/-!
# LeanCP Example: Verified Two Sum

State-sensitive end-to-end verification of a tiny arithmetic program. This
exercises variable assignment plus return through `swp`.
-/

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

set_option maxHeartbeats 800000

def twoSumVerifiedBody : CStmt :=
  .seq (.assign (.var "sum") (.binop .add (.var "a") (.var "b")))
    (.ret (.var "sum"))

def twoSumSSpec (a b : Int) : SFunSpec where
  name := "two_sum_state_sensitive"
  params := [("a", .int), ("b", .int)]
  retType := .int
  pre := fun st =>
    st.lookupVar "a" = some (.int a) ∧
    st.lookupVar "b" = some (.int b)
  post := fun retVal _st =>
    retVal = .int (a + b)
  body := twoSumVerifiedBody

private theorem twoSum_loopFree : LoopFree twoSumVerifiedBody := by
  simp [twoSumVerifiedBody, LoopFree]

private theorem twoSum_tailReturn : TailReturn twoSumVerifiedBody := by
  simp [twoSumVerifiedBody, TailReturn, NoReturn]

set_option maxHeartbeats 800000 in
theorem twoSum_verified (a b : Int) :
    sgenVC (twoSumSSpec a b) := by
  intro st hpre
  rcases hpre with ⟨ha, hb⟩
  have hStaticRhs :
      evalStaticExpr (.binop .add (.var "a") (.var "b")) = none := by
    simp [evalStaticExpr]
  have hEvalA : evalExpr (.var "a") st = some (.int a) := by
    simpa [evalExpr] using ha
  have hEvalB : evalExpr (.var "b") st = some (.int b) := by
    simpa [evalExpr] using hb
  have hEvalRhs :
      evalExpr (.binop .add (.var "a") (.var "b")) st = some (.int (a + b)) := by
    rw [evalExpr, hStaticRhs, hEvalA, hEvalB]
    · rfl
    · intro h
      cases h
    · intro h
      cases h
  let st' := st.updateVar "sum" (.int (a + b))
  have hEvalSum : evalExpr (.var "sum") st' = some (.int (a + b)) := by
    simp [evalExpr, evalStaticExpr, CState.lookupVar, CState.updateVar, st']
  change swp twoSumVerifiedBody (twoSumSSpec a b).post st
  simp [twoSumVerifiedBody, swp, twoSumSSpec, hEvalRhs, hEvalSum, st']

theorem twoSum_executes (a b : Int) {st fuel}
    (hpre : (twoSumSSpec a b).pre st)
    (hfuel : stmtDepth twoSumVerifiedBody ≤ fuel) :
    ∃ res, execStmt fuel twoSumVerifiedBody st = some res ∧
      match res with
      | .returned v st' => (twoSumSSpec a b).post v st'
      | .normal st' => (twoSumSSpec a b).post CVal.undef st' := by
  have hvc : swp twoSumVerifiedBody (twoSumSSpec a b).post st :=
    twoSum_verified a b st hpre
  exact swp_sound twoSumVerifiedBody twoSum_loopFree twoSum_tailReturn hfuel hvc

end HeytingLean.LeanCP.Examples
