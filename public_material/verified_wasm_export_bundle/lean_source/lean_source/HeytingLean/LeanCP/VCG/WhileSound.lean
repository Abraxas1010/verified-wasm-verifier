import HeytingLean.LeanCP.VCG.SWPSound

/-!
# LeanCP Unbounded While Soundness

Fuel-indexed execution remains the operational semantics, but the user-facing
rules in this module are partial-correctness theorems: if a while-loop
terminates normally, the invariant and exit postcondition hold. No iteration
bound appears in the theorem hypotheses.
-/

namespace HeytingLean.LeanCP

set_option linter.unnecessarySimpa false

private theorem some_normal_injective {st₁ st₂ : CState}
    (h : some (ExecResult.normal st₁) = some (ExecResult.normal st₂)) : st₁ = st₂ := by
  injection h with hNormal
  injection hNormal with hState

private theorem swp_exec_normal_sound (body : CStmt) (hloop : LoopFree body) (hnr : NoReturn body) :
    ∀ {Q st fuel st'},
      swp body Q st →
      execStmt fuel body st = some (.normal st') →
      Q CVal.undef st' := by
  intro Q st fuel st' hswp hexec
  induction body generalizing Q st fuel st' with
  | skip =>
      cases fuel with
      | zero =>
          simp [execStmt] at hexec
      | succ fuel' =>
          have hEq : st = st' := by
            have hSome : some (ExecResult.normal st) = some (ExecResult.normal st') := by
              simpa [execStmt] using hexec
            exact some_normal_injective hSome
          simpa [hEq] using hswp
  | ret e =>
      cases hnr
  | assign lhs rhs =>
      cases fuel with
      | zero =>
          simp [execStmt] at hexec
      | succ fuel' =>
          cases lhs with
          | var x =>
              cases hEval : evalExpr rhs st with
              | none =>
                  simp [execStmt, hEval] at hexec
              | some v =>
                  have hq : Q CVal.undef (st.updateVar x v) := by
                    simpa [swp, hEval] using hswp
                  have hEq : st.updateVar x v = st' := by
                    have hSome :
                        some (ExecResult.normal (st.updateVar x v)) =
                          some (ExecResult.normal st') := by
                      simpa [execStmt, hEval] using hexec
                    exact some_normal_injective hSome
                  simpa [hEq] using hq
          | deref p =>
              cases hPtr : evalExpr p st with
              | none =>
                  simp [execStmt, hPtr] at hexec
              | some pv =>
                  cases pv with
                  | int n =>
                      simp [execStmt, hPtr] at hexec
                  | uint n sz =>
                      simp [execStmt, hPtr] at hexec
                  | null =>
                      simp [execStmt, hPtr] at hexec
                  | undef =>
                      simp [execStmt, hPtr] at hexec
                  | structVal fields =>
                      simp [execStmt, hPtr] at hexec
                  | unionVal tag inner =>
                      simp [execStmt, hPtr] at hexec
                  | float v =>
                      simp [execStmt, hPtr] at hexec
                  | ptr block offset =>
                      cases hEval : evalExpr rhs st with
                      | none =>
                          simp [execStmt, hPtr, hEval] at hexec
                      | some v =>
                          have hpair : (∃ vOld, st.readPtr { block := block, offset := offset } = some vOld) ∧
                              ∃ st'', st.writePtr { block := block, offset := offset } v = some st'' ∧
                                Q CVal.undef st'' := by
                            simpa [swp, hPtr, hEval] using hswp
                          rcases hpair with ⟨_vOld, st'', hwrite, hq⟩
                          have hEq : st'' = st' := by
                            have hSome :
                                some (ExecResult.normal st'') =
                                  some (ExecResult.normal st') := by
                              simpa [execStmt, hPtr, hEval, hwrite] using hexec
                            exact some_normal_injective hSome
                          simpa [hEq] using hq
          | fieldAccess p field =>
              cases hPtr : evalExpr p st with
              | none =>
                  simp [execStmt, hPtr] at hexec
              | some pv =>
                  cases pv with
                  | int n =>
                      simp [execStmt, hPtr] at hexec
                  | uint n sz =>
                      simp [execStmt, hPtr] at hexec
                  | null =>
                      simp [execStmt, hPtr] at hexec
                  | undef =>
                      simp [execStmt, hPtr] at hexec
                  | structVal fields =>
                      simp [execStmt, hPtr] at hexec
                  | unionVal tag inner =>
                      simp [execStmt, hPtr] at hexec
                  | float v =>
                      simp [execStmt, hPtr] at hexec
                  | ptr block offset =>
                      cases hEval : evalExpr rhs st with
                      | none =>
                          simp [execStmt, hPtr, hEval] at hexec
                      | some v =>
                          have hpair : ∃ slot vOld st'',
                              PtrVal.addOffset { block := block, offset := offset }
                                (Int.ofNat (fieldOffset field)) = some slot ∧
                              st.readPtr slot = some vOld ∧
                              st.writePtr slot v = some st'' ∧
                              Q CVal.undef st'' := by
                            simpa [swp, hPtr, hEval] using hswp
                          rcases hpair with ⟨slot, _vOld, st'', hslot, _hread, hwrite, hq⟩
                          have hEq : st'' = st' := by
                            have hexec' := hexec
                            simp [execStmt, hPtr, hEval] at hexec'
                            change ((PtrVal.addOffset { block := block, offset := offset }
                              (Int.ofNat (fieldOffset field))).bind
                              (fun slot => Option.map ExecResult.normal (st.writePtr slot v))) =
                              some (ExecResult.normal st') at hexec'
                            rw [hslot] at hexec'
                            simp [Option.bind, hwrite] at hexec'
                            exact hexec'
                          simpa [hEq] using hq
          | intLit n =>
              cases hswp
          | floatLit v =>
              cases hswp
          | null =>
              cases hswp
          | sizeOf ty =>
              cases hswp
          | cast ty e =>
              cases hswp
          | binop op e1 e2 =>
              cases hswp
          | addrOf x =>
              cases hswp
          | arrayAccess arr idx =>
              cases hswp
          | call fname args =>
              cases hswp
  | seq s1 s2 ih1 ih2 =>
      rcases hloop with ⟨hloop1, hloop2⟩
      rcases hnr with ⟨hnr1, hnr2⟩
      cases fuel with
      | zero =>
          simp [execStmt] at hexec
      | succ fuel' =>
          cases hExec1 : execStmt fuel' s1 st with
          | none =>
              simp [execStmt, hExec1] at hexec
          | some res =>
              cases res with
              | returned v st1 =>
                  simp [execStmt, hExec1] at hexec
              | normal st1 =>
                  have hmid : swp s2 Q st1 := by
                    have hseq : swp s1 (fun _ => swp s2 Q) st := by
                      simpa [swp] using hswp
                    exact ih1 hloop1 hnr1 hseq hExec1
                  have hExec2 : execStmt fuel' s2 st1 = some (.normal st') := by
                    simpa [execStmt, hExec1] using hexec
                  exact ih2 hloop2 hnr2 hmid hExec2
  | ite cond th el ihTh ihEl =>
      rcases hloop with ⟨hloopTh, hloopEl⟩
      rcases hnr with ⟨hnrTh, hnrEl⟩
      cases fuel with
      | zero =>
          simp [execStmt] at hexec
      | succ fuel' =>
          cases hCond : evalExpr cond st with
          | none =>
              simp [execStmt, hCond] at hexec
          | some v =>
              cases hTruth : isTruthy v with
              | true =>
                  have hbranch : swp th Q st := by
                    simpa [swp, hCond, hTruth] using hswp
                  have hExecTh : execStmt fuel' th st = some (.normal st') := by
                    simpa [execStmt, hCond, hTruth] using hexec
                  exact ihTh hloopTh hnrTh hbranch hExecTh
              | false =>
                  have hbranch : swp el Q st := by
                    simpa [swp, hCond, hTruth] using hswp
                  have hExecEl : execStmt fuel' el st = some (.normal st') := by
                    simpa [execStmt, hCond, hTruth] using hexec
                  exact ihEl hloopEl hnrEl hbranch hExecEl
  | block decls body ih =>
      cases fuel with
      | zero =>
          simp [execStmt] at hexec
      | succ fuel' =>
          have hblock : swp body (fun ret st'' => Q ret (restoreBlockState st st'' decls))
              (enterBlockState st decls) := by
            simpa [swp] using hswp
          cases hExecBody : execStmt fuel' body (enterBlockState st decls) with
          | none =>
              simp [execStmt, hExecBody] at hexec
          | some res =>
              cases res with
              | returned v stBody =>
                  simp [execStmt, hExecBody] at hexec
              | normal stBody =>
                  have hq : Q CVal.undef (restoreBlockState st stBody decls) := by
                    exact ih (Q := fun ret st'' => Q ret (restoreBlockState st st'' decls))
                      hloop hnr hblock hExecBody
                  have hEq : restoreBlockState st stBody decls = st' := by
                    have hSome :
                        some (ExecResult.normal (restoreBlockState st stBody decls)) =
                          some (ExecResult.normal st') := by
                      simpa [execStmt, hExecBody] using hexec
                    exact some_normal_injective hSome
                  simpa [hEq] using hq
  | switch e tag caseBody default =>
      cases hloop
  | forLoop init cond step body =>
      cases hloop
  | «break» =>
      cases hloop
  | «continue» =>
      cases hloop
  | whileInv cond inv body ih =>
      cases hloop
  | alloc x cells =>
      cases fuel with
      | zero =>
          simp [execStmt] at hexec
      | succ fuel' =>
          let stAlloc : CState := st.allocCells x cells
          have hq : Q CVal.undef stAlloc := by
            simpa [swp, stAlloc] using hswp
          have hEq : stAlloc = st' := by
            have hSome : some (ExecResult.normal stAlloc) = some (ExecResult.normal st') := by
              simpa [execStmt, stAlloc] using hexec
            exact some_normal_injective hSome
          simpa [hEq] using hq
  | free e cells =>
      cases fuel with
      | zero =>
          simp [execStmt] at hexec
      | succ fuel' =>
          cases hEval : evalExpr e st with
          | none =>
              simp [execStmt, hEval] at hexec
          | some v =>
              cases v with
              | int n =>
                  simp [execStmt, hEval] at hexec
              | uint n sz =>
                  simp [execStmt, hEval] at hexec
              | null =>
                  simp [execStmt, hEval] at hexec
              | undef =>
                  simp [execStmt, hEval] at hexec
              | structVal fields =>
                  simp [execStmt, hEval] at hexec
              | unionVal tag inner =>
                  simp [execStmt, hEval] at hexec
              | float v =>
                  simp [execStmt, hEval] at hexec
              | ptr block offset =>
                  rcases (show ∃ flatAddr, st.resolvePtr { block := block, offset := offset } = some flatAddr ∧
                      Q CVal.undef (st.freeCells flatAddr cells) by
                    simpa [swp, hEval] using hswp) with ⟨flatAddr, hresolve, hq⟩
                  have hEq : st.freeCells flatAddr cells = st' := by
                    have hSome :
                        some (ExecResult.normal (st.freeCells flatAddr cells)) =
                          some (ExecResult.normal st') := by
                      simpa [execStmt, hEval, hresolve, CState.freeCells] using hexec
                    exact some_normal_injective hSome
                  simpa [hEq] using hq
  | decl x ty =>
      cases fuel with
      | zero =>
          simp [execStmt] at hexec
      | succ fuel' =>
          have hq : Q CVal.undef (st.updateVar x CVal.undef) := by
            simpa [swp] using hswp
          have hEq : st.updateVar x CVal.undef = st' := by
            have hSome :
                some (ExecResult.normal (st.updateVar x CVal.undef)) =
                  some (ExecResult.normal st') := by
              simpa [execStmt] using hexec
            exact some_normal_injective hSome
          simpa [hEq] using hq

/-- Internal trace-recursive loop theorem: if a while-loop terminates normally,
its invariant still holds and the final guard evaluation is falsy. -/
private theorem while_partial_sound_core
    (guard : CExpr) (ann : HProp) (inv : SProp) (body : CStmt)
    (hloop : LoopFree body) (hnr : NoReturn body)
    (hpres : ∀ st, inv st →
      (∃ v, evalExpr guard st = some v ∧ isTruthy v = true) →
      swp body (fun _ => inv) st) :
    ∀ {fuel st st'},
      inv st →
      execStmt fuel (.whileInv guard ann body) st = some (.normal st') →
      inv st' ∧ ∃ v, evalExpr guard st' = some v ∧ isTruthy v = false
  | 0, _st, _st', _hinv, hexec => by
      simp [execStmt] at hexec
  | fuel + 1, st, st', hinv, hexec => by
      cases hCond : evalExpr guard st with
      | none =>
          simp [execStmt, hCond] at hexec
      | some v =>
          cases hTruth : isTruthy v with
          | false =>
              have hEq : st = st' := by
                have hSome : some (ExecResult.normal st) = some (ExecResult.normal st') := by
                  simpa [execStmt, hCond, hTruth] using hexec
                exact some_normal_injective hSome
              refine ⟨by simpa [hEq] using hinv, ?_⟩
              refine ⟨v, ?_, hTruth⟩
              simpa [hEq] using hCond
          | true =>
              cases hExecBody : execStmt fuel body st with
              | none =>
                  simp [execStmt, hCond, hTruth, hExecBody] at hexec
              | some res =>
                  cases res with
                  | returned ret stBody =>
                      simp [execStmt, hCond, hTruth, hExecBody] at hexec
                  | normal stBody =>
                      have hBodyWP : swp body (fun _ => inv) st := by
                        exact hpres st hinv ⟨v, hCond, hTruth⟩
                      have hInvBody : inv stBody := by
                        exact swp_exec_normal_sound body hloop hnr hBodyWP hExecBody
                      have hExecLoop : execStmt fuel (.whileInv guard ann body) stBody =
                          some (.normal st') := by
                        simpa [execStmt, hCond, hTruth, hExecBody] using hexec
                      exact while_partial_sound_core guard ann inv body hloop hnr hpres hInvBody hExecLoop
termination_by fuel _ _ _ _ => fuel

/-- Unbounded partial-correctness while rule. If the loop terminates normally,
the invariant holds in the final state. -/
theorem while_partial_sound
    (guard : CExpr) (inv : SProp) (body : CStmt)
    (hloop : LoopFree body) (hnr : NoReturn body)
    (hpres : ∀ st, inv st →
      (∃ v, evalExpr guard st = some v ∧ isTruthy v = true) →
      swp body (fun _ => inv) st) :
    ∀ {ann st fuel st'},
      inv st →
      execStmt fuel (.whileInv guard ann body) st = some (.normal st') →
      inv st' := by
  intro ann st fuel st' hinv hexec
  have hExecTrue : execStmt fuel (.whileInv guard HProp.htrue body) st = some (.normal st') := by
    rw [← execStmt_whileInv_inv_irrelevant fuel guard body ann HProp.htrue st]
    exact hexec
  exact (while_partial_sound_core guard HProp.htrue inv body hloop hnr hpres hinv hExecTrue).1

/-- Standard Hoare-style while rule: normal termination yields the exit
postcondition once the invariant and falsy exit guard are discharged. -/
theorem while_hoare_sound
    (guard : CExpr) (inv : SProp) (body : CStmt) (Q : CVal → SProp)
    (hloop : LoopFree body) (hnr : NoReturn body)
    (hpres : ∀ st, inv st →
      (∃ v, evalExpr guard st = some v ∧ isTruthy v = true) →
      swp body (fun _ => inv) st)
    (hexit : ∀ st, inv st →
      (∃ v, evalExpr guard st = some v ∧ isTruthy v = false) →
      Q CVal.undef st) :
    ∀ {ann st fuel st'},
      inv st →
      execStmt fuel (.whileInv guard ann body) st = some (.normal st') →
      Q CVal.undef st' := by
  intro ann st fuel st' hinv hexec
  have hExecTrue : execStmt fuel (.whileInv guard HProp.htrue body) st = some (.normal st') := by
    rw [← execStmt_whileInv_inv_irrelevant fuel guard body ann HProp.htrue st]
    exact hexec
  rcases while_partial_sound_core guard HProp.htrue inv body hloop hnr hpres hinv hExecTrue with
    ⟨hInv', hExitFalse⟩
  exact hexit st' hInv' hExitFalse

end HeytingLean.LeanCP
