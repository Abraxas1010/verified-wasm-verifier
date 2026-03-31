import HeytingLean.LeanCP.VCG.SWPSound

/-!
# LeanCP Example: Verified PQC Acceptance Kernel

This verifies the tiny C-style acceptance kernel used by the standards-aligned
proof-carrying PQ packet scaffold: return `1` iff all four checks pass.
-/

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

def verifiedPQCVerifierBody : CStmt :=
  .ite (.binop .eq (.var "passed_checks") (.intLit 4))
    (.ret (.intLit 1))
    (.ret (.intLit 0))

def verifiedPQCVerifierSpec (passedChecks : Int) : SFunSpec where
  name := "verified_pqc_accept_all_checks"
  params := [("passed_checks", .int)]
  retType := .int
  pre := fun st =>
    st.lookupVar "passed_checks" = some (.int passedChecks)
  post := fun retVal _st =>
    retVal = .int (if passedChecks = 4 then 1 else 0)
  body := verifiedPQCVerifierBody

private theorem verifiedPQCVerifier_loopFree : LoopFree verifiedPQCVerifierBody := by
  simp [verifiedPQCVerifierBody, LoopFree]

private theorem verifiedPQCVerifier_tailReturn : TailReturn verifiedPQCVerifierBody := by
  simp [verifiedPQCVerifierBody, TailReturn]

theorem verifiedPQCVerifier_verified (passedChecks : Int) :
    sgenVC (verifiedPQCVerifierSpec passedChecks) := by
  intro st hpre
  change swp verifiedPQCVerifierBody (verifiedPQCVerifierSpec passedChecks).post st
  have hEvalChecks : evalExpr (.var "passed_checks") st = some (.int passedChecks) := by
    simpa [evalExpr] using hpre
  have hEvalFour : evalExpr (.intLit 4) st = some (.int 4) := by
    rfl
  by_cases hEq : passedChecks = 4
  · have hCond : evalExpr (.binop .eq (.var "passed_checks") (.intLit 4)) st = some (.int 1) := by
      rw [evalExpr, evalStaticExpr, hEvalChecks, hEvalFour]
      · change some (CVal.int (if passedChecks = 4 then 1 else 0)) = some (CVal.int 1)
        simp [hEq]
      · intro h
        cases h
      · intro h
        cases h
    have hEvalOne : evalExpr (.intLit 1) st = some (.int 1) := by
      rfl
    simpa [verifiedPQCVerifierBody, swp, verifiedPQCVerifierSpec, hCond, isTruthy, hEvalChecks, hEvalOne, hEq]
  · have hCond : evalExpr (.binop .eq (.var "passed_checks") (.intLit 4)) st = some (.int 0) := by
      rw [evalExpr, evalStaticExpr, hEvalChecks, hEvalFour]
      · change some (CVal.int (if passedChecks = 4 then 1 else 0)) = some (CVal.int 0)
        simp [hEq]
      · intro h
        cases h
      · intro h
        cases h
    have hEvalZero : evalExpr (.intLit 0) st = some (.int 0) := by
      rfl
    simpa [verifiedPQCVerifierBody, swp, verifiedPQCVerifierSpec, hCond, isTruthy, hEvalChecks, hEvalZero, hEq]

theorem verifiedPQCVerifier_executes (passedChecks : Int) {st fuel}
    (hpre : (verifiedPQCVerifierSpec passedChecks).pre st)
    (hfuel : stmtDepth verifiedPQCVerifierBody ≤ fuel) :
    ∃ res, execStmt fuel verifiedPQCVerifierBody st = some res ∧
      match res with
      | .returned v st' => (verifiedPQCVerifierSpec passedChecks).post v st'
      | .normal st' => (verifiedPQCVerifierSpec passedChecks).post CVal.undef st' := by
  have hvc : swp verifiedPQCVerifierBody (verifiedPQCVerifierSpec passedChecks).post st :=
    verifiedPQCVerifier_verified passedChecks st hpre
  exact swp_sound
    verifiedPQCVerifierBody
    verifiedPQCVerifier_loopFree
    verifiedPQCVerifier_tailReturn
    hfuel
    hvc

end HeytingLean.LeanCP.Examples
