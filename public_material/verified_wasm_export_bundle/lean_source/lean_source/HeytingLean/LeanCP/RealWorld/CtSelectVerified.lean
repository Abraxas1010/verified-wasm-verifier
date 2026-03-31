import HeytingLean.LeanCP.RealWorld.CtEqVerified
import HeytingLean.LeanCP.VCG.SWPSound
import Mathlib.Tactic

namespace HeytingLean.LeanCP.RealWorld

open HeytingLean.LeanCP

set_option linter.unnecessarySimpa false

/-- Branch-free conditional select on the current LeanCP scalar surface. -/
def ctSelectExpr : CExpr :=
  .binop .add (.var "b")
    (.binop .mul (.var "flag") (.binop .sub (.var "a") (.var "b")))

def ctSelectBody : CStmt :=
  .ret ctSelectExpr

private theorem evalBinOp_mul_int_int' (a b : Int) :
    evalBinOp .mul (.int a) (.int b) = some (.int (a * b)) := by
  rfl

private theorem evalBinOp_add_int_int' (a b : Int) :
    evalBinOp .add (.int a) (.int b) = some (.int (a + b)) := by
  rfl

def ctSelectSpec (flag a b : Int) : SFunSpec where
  name := "ct_select"
  params := [("flag", .int), ("a", .int), ("b", .int)]
  retType := .int
  pre := fun st =>
    st.lookupVar "flag" = some (.int flag) ∧
    st.lookupVar "a" = some (.int a) ∧
    st.lookupVar "b" = some (.int b) ∧
    (flag = 0 ∨ flag = 1)
  post := fun ret _ => ret = .int (if flag = 0 then b else a)
  body := ctSelectBody

theorem ctSelect_noBranch : NoBranch ctSelectBody := by
  simp [NoBranch, ctSelectBody]

theorem ctSelect_correct (flag a b : Int) : sgenVC (ctSelectSpec flag a b) := by
  intro st hpre
  rcases hpre with ⟨hFlag, hA, hB, hBit⟩
  have hEvalFlag : evalExpr (.var "flag") st = some (.int flag) := by
    simpa [evalExpr] using hFlag
  have hEvalA : evalExpr (.var "a") st = some (.int a) := by
    simpa [evalExpr] using hA
  have hEvalB : evalExpr (.var "b") st = some (.int b) := by
    simpa [evalExpr] using hB
  rcases hBit with rfl | rfl
  · change swp ctSelectBody (ctSelectSpec 0 a b).post st
    have hEval : evalExpr ctSelectExpr st = some (.int b) := by
      calc
        evalExpr ctSelectExpr st
            = evalBinOp .add (.int b) (.int (0 * (a - b))) := by
                simp [ctSelectExpr, evalExpr, evalStaticExpr, hFlag, hA, hB,
                  evalBinOp_mul_int_int']
        _ = some (.int b) := by
              simp [evalBinOp_add_int_int']
    simpa [ctSelectBody, swp, ctSelectSpec, hEval]
  · have hSel : b + 1 * (a - b) = a := by ring
    change swp ctSelectBody (ctSelectSpec 1 a b).post st
    have hEval : evalExpr ctSelectExpr st = some (.int a) := by
      calc
        evalExpr ctSelectExpr st
            = evalBinOp .add (.int b) (.int (1 * (a - b))) := by
                simp [ctSelectExpr, evalExpr, evalStaticExpr, hFlag, hA, hB,
                  evalBinOp_mul_int_int']
        _ = some (.int a) := by
              simp [evalBinOp_add_int_int', hSel]
    simpa [ctSelectBody, swp, ctSelectSpec, hEval]

end HeytingLean.LeanCP.RealWorld
