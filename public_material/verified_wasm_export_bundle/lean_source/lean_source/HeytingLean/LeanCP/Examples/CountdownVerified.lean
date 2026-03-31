import HeytingLean.LeanCP.VCG.SWhile
import HeytingLean.LeanCP.Core.VarLemmas

/-!
# LeanCP Example: Verified Countdown Loop

Bounded state-sensitive verification of a simple countdown loop. This is the
first consumer of `swhileWP_sound`, exercising the loop-rule surface directly.
-/

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

def countdownCond : CExpr := .var "n"

def countdownBody : CStmt :=
  .assign (.var "n") (.binop .sub (.var "n") (.intLit 1))

def countdownAnn : HProp := HProp.fact True

def countdownProgram : CStmt :=
  .whileInv countdownCond countdownAnn countdownBody

def countdownPre : SProp := fun st =>
  st.lookupVar "n" = some (.int 2)

def countdownInv : SProp := fun st =>
  st.lookupVar "n" = some (.int 2) ∨
    st.lookupVar "n" = some (.int 1) ∨
    st.lookupVar "n" = some (.int 0)

def countdownPost : CVal → SProp := fun _ st =>
  st.lookupVar "n" = some (.int 0)

private theorem countdown_loopFree : LoopFree countdownBody := by
  simp [countdownBody, LoopFree]

private theorem countdown_noReturn : NoReturn countdownBody := by
  simp [countdownBody, NoReturn]

theorem countdown_verified :
    ∀ st, countdownPre st → swhileWP 2 countdownCond countdownInv countdownBody countdownPost st := by
  intro st hpre
  let st1 := st.updateVar "n" (.int 1)
  let st2 := st1.updateVar "n" (.int 0)

  have hlookup1 : st1.lookupVar "n" = some (.int 1) := by
    simpa [st1] using lookupVar_updateVar_eq st "n" (.int 1)
  have hlookup2 : st2.lookupVar "n" = some (.int 0) := by
    simpa [st2] using lookupVar_updateVar_eq st1 "n" (.int 0)
  have hlookupStart : st.lookupVar "n" = some (.int 2) := hpre

  have hEvalCond0 : evalExpr countdownCond st2 = some (.int 0) := by
    simpa [countdownCond, evalExpr, evalStaticExpr] using hlookup2
  have hInv0 : countdownInv st2 := by
    exact Or.inr (Or.inr hlookup2)
  have hPost0 : countdownPost CVal.undef st2 := hlookup2
  have hStep0 : countdownInv st2 ∧ isTruthy (.int 0) = false ∧ countdownPost CVal.undef st2 := by
    refine ⟨hInv0, ?_⟩
    simp [isTruthy, hPost0]
  have hLoop0 : swhileWP 0 countdownCond countdownInv countdownBody countdownPost st2 := by
    simpa [swhileWP, hEvalCond0] using hStep0

  have hEvalCond1 : evalExpr countdownCond st1 = some (.int 1) := by
    simpa [countdownCond, evalExpr, evalStaticExpr] using hlookup1
  have hInv1 : countdownInv st1 := by
    exact Or.inr (Or.inl hlookup1)
  have hEvalRhs1 :
      evalExpr (.binop .sub (.var "n") (.intLit 1)) st1 = some (.int 0) := by
    simpa [evalExpr, evalStaticExpr, hlookup1] using
      (show evalBinOp .sub (.int 1) (.int 1) = some (.int 0) by
        rfl)
  have hBody1 :
      swp countdownBody (fun _ => swhileWP 0 countdownCond countdownInv countdownBody countdownPost) st1 := by
    simpa [countdownBody, swp, hEvalRhs1, st2] using hLoop0
  have hLoop1 : swhileWP 1 countdownCond countdownInv countdownBody countdownPost st1 := by
    simpa [swhileWP, hEvalCond1] using And.intro hInv1 hBody1

  have hInv2 : countdownInv st := by
    exact Or.inl hpre
  have hEvalCond2 : evalExpr countdownCond st = some (.int 2) := by
    simpa [countdownCond, evalExpr, evalStaticExpr] using hlookupStart
  have hEvalRhs2 :
      evalExpr (.binop .sub (.var "n") (.intLit 1)) st = some (.int 1) := by
    simpa [evalExpr, evalStaticExpr, hlookupStart] using
      (show evalBinOp .sub (.int 2) (.int 1) = some (.int 1) by
        rfl)
  have hBody2 :
      swp countdownBody (fun _ => swhileWP 1 countdownCond countdownInv countdownBody countdownPost) st := by
    simpa [countdownBody, swp, hEvalRhs2, st1] using hLoop1
  simpa [swhileWP, hEvalCond2] using And.intro hInv2 hBody2

theorem countdown_executes (st : CState) (hpre : countdownPre st) :
    ∃ st',
      execStmt (swhileFuel countdownBody 2) countdownProgram st = some (.normal st') ∧
      countdownPost CVal.undef st' := by
  exact swhileWP_sound countdownCond countdownInv countdownAnn countdownBody
    countdown_loopFree countdown_noReturn (countdown_verified st hpre)

end HeytingLean.LeanCP.Examples
