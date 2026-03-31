import HeytingLean.LeanCP.VCG.EndToEndSoundness
import HeytingLean.LeanCP.VCG.SMTSmoke
import HeytingLean.LeanCP.Examples.CountdownVerified
import HeytingLean.LeanCP.Examples.CallerVerified

namespace HeytingLean.LeanCP

open HeytingLean.LeanCP.Examples

def arithPhase6Input (n : Int) : VerifyInput where
  name := "arith_phase6"
  mode := .swp
  body := arithReturnBody
  pre := (arithReturnSpec n).pre
  post := (arithReturnSpec n).post

def arithPhase6Bundle (n : Int) : VCBundle :=
  { pre := swp arithReturnBody (arithReturnSpec n).post
    vcs :=
      [{ name := vcName "arith_phase6" [] "main"
         kind := .main
         origin := mkOrigin [] "function"
         goal := ∀ st, (arithReturnSpec n).pre st → swp arithReturnBody (arithReturnSpec n).post st
         autoClass := .manual }] }

private theorem arithPhase6_bundle_ok (n : Int) :
    generateBundle (arithPhase6Input n) = Except.ok (arithPhase6Bundle n) := by
  rfl

private theorem arithPhase6_vcs_valid (n : Int) :
    VCListValid (arithPhase6Bundle n).vcs := by
  intro vc hmem
  simp [arithPhase6Bundle] at hmem
  rcases hmem with rfl
  simpa [arithReturnBody] using arith_return_smt_z3 n

example (n : Int) :
    ∀ st, (arithReturnSpec n).pre st →
      ∃ res,
        execStmt (stmtDepth arithReturnBody) arithReturnBody st = some res ∧
          match res with
          | .returned v st' => (arithReturnSpec n).post v st'
          | .normal st' => (arithReturnSpec n).post CVal.undef st' := by
  intro st hpre
  exact verifyInput_sound_swp_loopFree (arithPhase6Input n)
    (bundle := arithPhase6Bundle n) (fuel := stmtDepth arithReturnBody)
    rfl
    (by simp [arithPhase6Input, arithReturnBody, LoopFree])
    (by simp [arithPhase6Input, arithReturnBody, TailReturn])
    (arithPhase6_bundle_ok n) (by rfl) (arithPhase6_vcs_valid n) st hpre

def countdownPhase6Input : VerifyInput where
  name := "countdown_phase6"
  mode := .swp
  body := countdownProgram
  pre := countdownPre
  post := countdownPost
  loops := [{ path := [], inv := countdownInv, fuelHint := 2 }]

def countdownPhase6Bundle : VCBundle :=
  { pre := swhileWP 2 countdownCond countdownInv countdownBody countdownPost
    vcs :=
      [ { name := vcName "countdown_phase6" [] "main"
          kind := .main
          origin := mkOrigin [] "function"
          goal := ∀ st, countdownPre st → swhileWP 2 countdownCond countdownInv countdownBody countdownPost st
          autoClass := .manual }
      , { name := vcName "countdown_phase6" [] "loop_init"
          kind := .loopInit
          origin := mkOrigin [] "while"
          goal := ∀ st, countdownPre st → countdownInv st
          autoClass := .manual }
      , { name := vcName "countdown_phase6" [] "loop_step"
          kind := .loopStep
          origin := mkOrigin [] "while"
          goal := ∀ st, countdownInv st →
            match evalExpr countdownCond st with
            | some v =>
                if isTruthy v then
                  swp countdownBody (fun _ => swhileWP 1 countdownCond countdownInv countdownBody countdownPost) st
                else
                  True
            | none => False
          autoClass := .manual }
      , { name := vcName "countdown_phase6" [] "loop_exit"
          kind := .loopExit
          origin := mkOrigin [] "while"
          goal := ∀ st, countdownInv st →
            match evalExpr countdownCond st with
            | some v => if isTruthy v then True else countdownPost CVal.undef st
            | none => False
          autoClass := .manual } ] }

private theorem countdownPhase6_bundle_ok :
    generateBundle countdownPhase6Input = Except.ok countdownPhase6Bundle := by
  rfl

private theorem countdown_step_from_two (st : CState)
    (h2 : st.lookupVar "n" = some (.int 2)) :
    swp countdownBody (fun _ => swhileWP 1 countdownCond countdownInv countdownBody countdownPost) st := by
  let st1 := st.updateVar "n" (.int 1)
  let st2 := st1.updateVar "n" (.int 0)
  have hlookup1 : st1.lookupVar "n" = some (.int 1) := by
    simpa [st1] using lookupVar_updateVar_eq st "n" (.int 1)
  have hlookup2 : st2.lookupVar "n" = some (.int 0) := by
    simpa [st2] using lookupVar_updateVar_eq st1 "n" (.int 0)
  have hEvalCond0 : evalExpr countdownCond st2 = some (.int 0) := by
    simpa [countdownCond, evalExpr, evalStaticExpr] using hlookup2
  have hLoop0 : swhileWP 0 countdownCond countdownInv countdownBody countdownPost st2 := by
    have hInv0 : countdownInv st2 := by exact Or.inr (Or.inr hlookup2)
    have hPost0 : countdownPost CVal.undef st2 := hlookup2
    have hStep0 : countdownInv st2 ∧ isTruthy (.int 0) = false ∧ countdownPost CVal.undef st2 := by
      refine ⟨hInv0, ?_⟩
      simp [isTruthy, hPost0]
    simpa [swhileWP, hEvalCond0] using hStep0
  have hEvalRhs : evalExpr (.binop .sub (.var "n") (.intLit 1)) st = some (.int 1) := by
    simpa [evalExpr, evalStaticExpr, h2] using
      (show evalBinOp .sub (.int 2) (.int 1) = some (.int 1) by rfl)
  have hLoop1 : swhileWP 1 countdownCond countdownInv countdownBody countdownPost st1 := by
    have hInv1 : countdownInv st1 := by exact Or.inr (Or.inl hlookup1)
    have hBody1 :
        swp countdownBody (fun _ => swhileWP 0 countdownCond countdownInv countdownBody countdownPost) st1 := by
      simpa [countdownBody, swp, st2] using hLoop0
    have hEvalCond1 : evalExpr countdownCond st1 = some (.int 1) := by
      simpa [countdownCond, evalExpr, evalStaticExpr] using hlookup1
    simpa [swhileWP, hEvalCond1] using And.intro hInv1 hBody1
  simpa [countdownBody, swp, hEvalRhs, st1] using hLoop1

private theorem countdown_step_from_one (st : CState)
    (h1 : st.lookupVar "n" = some (.int 1)) :
    swp countdownBody (fun _ => swhileWP 1 countdownCond countdownInv countdownBody countdownPost) st := by
  let st1 := st.updateVar "n" (.int 0)
  have hlookup1 : st1.lookupVar "n" = some (.int 0) := by
    simpa [st1] using lookupVar_updateVar_eq st "n" (.int 0)
  have hLoop0 : swhileWP 0 countdownCond countdownInv countdownBody countdownPost st1 := by
    have hEvalCond0 : evalExpr countdownCond st1 = some (.int 0) := by
      simpa [countdownCond, evalExpr, evalStaticExpr] using hlookup1
    have hInv0 : countdownInv st1 := by exact Or.inr (Or.inr hlookup1)
    have hPost0 : countdownPost CVal.undef st1 := hlookup1
    have hStep0 : countdownInv st1 ∧ isTruthy (.int 0) = false ∧ countdownPost CVal.undef st1 := by
      refine ⟨hInv0, ?_⟩
      simp [isTruthy, hPost0]
    simpa [swhileWP, hEvalCond0] using hStep0
  have hEvalRhs : evalExpr (.binop .sub (.var "n") (.intLit 1)) st = some (.int 0) := by
    simpa [evalExpr, evalStaticExpr, h1] using
      (show evalBinOp .sub (.int 1) (.int 1) = some (.int 0) by rfl)
  simpa [countdownBody, swp, hEvalRhs, st1] using hLoop0

private theorem countdownPhase6_vcs_valid :
    VCListValid countdownPhase6Bundle.vcs := by
  intro vc hmem
  simp [countdownPhase6Bundle] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact countdown_verified
  · intro st hpre
    exact Or.inl hpre
  · intro st hinv
    rcases hinv with h2 | h1 | h0
    · have hEval : evalExpr countdownCond st = some (.int 2) := by
        simpa [countdownCond, evalExpr, evalStaticExpr] using h2
      have htruth : isTruthy (.int 2) = true := by simp [isTruthy]
      simpa [hEval, htruth] using countdown_step_from_two st h2
    · have hEval : evalExpr countdownCond st = some (.int 1) := by
        simpa [countdownCond, evalExpr, evalStaticExpr] using h1
      have htruth : isTruthy (.int 1) = true := by simp [isTruthy]
      simpa [hEval, htruth] using countdown_step_from_one st h1
    · have hEval : evalExpr countdownCond st = some (.int 0) := by
        simpa [countdownCond, evalExpr, evalStaticExpr] using h0
      simpa [hEval, isTruthy]
  · intro st hinv
    rcases hinv with h2 | h1 | h0
    · have hEval : evalExpr countdownCond st = some (.int 2) := by
        simpa [countdownCond, evalExpr, evalStaticExpr] using h2
      simpa [hEval, isTruthy]
    · have hEval : evalExpr countdownCond st = some (.int 1) := by
        simpa [countdownCond, evalExpr, evalStaticExpr] using h1
      simpa [hEval, isTruthy]
    · have hEval : evalExpr countdownCond st = some (.int 0) := by
        simpa [countdownCond, evalExpr, evalStaticExpr] using h0
      have htruth : isTruthy (.int 0) = false := by simp [isTruthy]
      simpa [hEval, htruth] using h0

example :
    ∀ st, countdownPre st →
      ∃ st',
        execStmt (swhileFuel countdownBody 2) countdownProgram st = some (.normal st') ∧
          countdownPost CVal.undef st' := by
  intro st hpre
  exact verifyInput_sound_swp_normal countdownPhase6Input
    (cond := countdownCond) (ann := countdownAnn) (body := countdownBody)
    (hint := { path := [], inv := countdownInv, fuelHint := 2 })
    (bundle := countdownPhase6Bundle) (fuel := swhileFuel countdownBody 2)
    rfl rfl rfl
    (by simp [LoopFree, countdownBody])
    (by simp [NoReturn, countdownBody])
    countdownPhase6_bundle_ok
    (by rfl)
    countdownPhase6_vcs_valid
    st hpre

def retCallBody : CStmt := .ret (.call "increment" [.var "p"])

def retCallSpec (addr : Nat) (n : Int) : SFunSpec where
  name := "ret_call"
  params := [("p", .ptr .int)]
  retType := .int
  pre := (callerSpec addr n).pre
  post := fun ret st =>
    ret = .int (n + 1) ∧
    st.lookupVar "p" = some (CVal.ptrAddr (addr : PtrVal)) ∧
    st.heap.read addr = some (.int (n + 1))
  body := retCallBody

def retCallInput (addr : Nat) (n : Int) : VerifyInput where
  name := "ret_call_phase6"
  mode := .swpFull
  body := retCallBody
  pre := (retCallSpec addr n).pre
  post := (retCallSpec addr n).post
  funEnv := callerFunEnv addr n

def retCallBundle (addr : Nat) (n : Int) : VCBundle :=
  { pre := swpCall (callerFunEnv addr n) "increment" [.var "p"] (retCallSpec addr n).post
    vcs :=
      [ { name := vcName "ret_call_phase6" [] "main"
          kind := .main
          origin := mkOrigin [] "function"
          goal := ∀ st, (retCallSpec addr n).pre st →
            swpCall (callerFunEnv addr n) "increment" [.var "p"] (retCallSpec addr n).post st
          autoClass := .manual }
      , { name := vcName "ret_call_phase6" [] "call_return"
          kind := .callBoundary
          origin := mkOrigin [] "call.return.increment"
          goal := ∀ st, (retCallSpec addr n).pre st →
            swpCall (callerFunEnv addr n) "increment" [.var "p"] (retCallSpec addr n).post st
          autoClass := .manual } ] }

private theorem retCall_bundle_ok (addr : Nat) (n : Int) :
    generateBundle (retCallInput addr n) = Except.ok (retCallBundle addr n) := by
  rfl

private theorem retCall_boundary_valid (addr : Nat) (n : Int) :
    ∀ st, (retCallSpec addr n).pre st →
      swpCall (callerFunEnv addr n) "increment" [.var "p"] (retCallSpec addr n).post st := by
  intro st hpre
  rcases hpre with ⟨hp, hheap⟩
  apply swpCall_intro (funEnv := callerFunEnv addr n) (fname := "increment")
    (args := [.var "p"]) (spec := incrementSpec addr n)
    (vals := [CVal.ptrAddr (addr : PtrVal)]) (Q := (retCallSpec addr n).post)
  · rfl
  · simp [evalArgs, hp]
  · simp [incrementSpec]
  · refine ⟨?_, hheap⟩
    simp [callEntryState, incrementSpec, bindCallEnv, CState.lookupVar]
  · intro ret callee hpost
    rcases hpost with ⟨hret, hpCallee, hheapCallee⟩
    refine ⟨hret, ?_, ?_⟩
    · simpa [restoreCallerState, CState.lookupVar] using hp
    · simpa [restoreCallerState] using hheapCallee

private theorem retCall_vcs_valid (addr : Nat) (n : Int) :
    VCListValid (retCallBundle addr n).vcs := by
  intro vc hmem
  simp [retCallBundle] at hmem
  rcases hmem with rfl | rfl
  · exact retCall_boundary_valid addr n
  · exact retCall_boundary_valid addr n

example (addr : Nat) (n : Int) :
    ∀ st, (retCallSpec addr n).pre st →
      ∃ res,
        execStmtFull (callerFunEnv addr n) (callDepth (callerFunEnv addr n) "increment" + 1) retCallBody st = some res ∧
          match res with
          | .returned v st' => (retCallSpec addr n).post v st'
          | .normal st' => (retCallSpec addr n).post CVal.undef st' := by
  intro st hpre
  exact verifyInput_sound_swpFull_loopFree (retCallInput addr n) (callerFunEnv_sound addr n)
    (bundle := retCallBundle addr n) (fuel := callDepth (callerFunEnv addr n) "increment")
    rfl
    (by simp [retCallInput, retCallBody, LoopFree])
    (by simp [retCallInput, retCallBody, TailReturn])
    (retCall_bundle_ok addr n) (by rfl) (retCall_vcs_valid addr n) st hpre

end HeytingLean.LeanCP
