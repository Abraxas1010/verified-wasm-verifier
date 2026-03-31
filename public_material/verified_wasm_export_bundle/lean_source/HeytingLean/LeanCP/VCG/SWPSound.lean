import HeytingLean.LeanCP.VCG.SWP

/-!
# LeanCP State-Sensitive WP Soundness

Soundness for the loop-free, tail-return fragment of the state-sensitive
weakest-precondition generator.
-/

namespace HeytingLean.LeanCP

set_option linter.unnecessarySimpa false

def LoopFree : CStmt → Prop
  | .skip => True
  | .ret _ => True
  | .assign _ _ => True
  | .seq s1 s2 => LoopFree s1 ∧ LoopFree s2
  | .ite _ th el => LoopFree th ∧ LoopFree el
  | .block _ body => LoopFree body
  | .switch _ _ _ _ => False
  | .forLoop _ _ _ _ => False
  | .break => False
  | .continue => False
  | .whileInv _ _ _ => False
  | .alloc _ _ => True
  | .free _ _ => True
  | .decl _ _ => True

def NoReturn : CStmt → Prop
  | .skip => True
  | .ret _ => False
  | .assign _ _ => True
  | .seq s1 s2 => NoReturn s1 ∧ NoReturn s2
  | .ite _ th el => NoReturn th ∧ NoReturn el
  | .block _ body => NoReturn body
  | .switch _ _ _ _ => False
  | .forLoop _ _ _ _ => False
  | .break => False
  | .continue => False
  | .whileInv _ _ _ => False
  | .alloc _ _ => True
  | .free _ _ => True
  | .decl _ _ => True

def TailReturn : CStmt → Prop
  | .skip => True
  | .ret _ => True
  | .assign _ _ => True
  | .seq s1 s2 => TailReturn s1 ∧ TailReturn s2 ∧ NoReturn s1
  | .ite _ th el => TailReturn th ∧ TailReturn el
  | .block _ body => TailReturn body
  | .switch _ _ _ _ => False
  | .forLoop _ _ _ _ => False
  | .break => False
  | .continue => False
  | .whileInv _ _ _ => False
  | .alloc _ _ => True
  | .free _ _ => True
  | .decl _ _ => True

def stmtDepth : CStmt → Nat
  | .skip => 1
  | .ret _ => 1
  | .assign _ _ => 1
  | .seq s1 s2 => max (stmtDepth s1) (stmtDepth s2) + 1
  | .ite _ th el => max (stmtDepth th) (stmtDepth el) + 1
  | .block _ body => stmtDepth body + 1
  | .switch _ _ _ default => stmtDepth default + 1
  | .forLoop init _ step body => max (stmtDepth init) (max (stmtDepth step) (stmtDepth body)) + 2
  | .break => 1
  | .continue => 1
  | .whileInv _ _ _ => 1
  | .alloc _ _ => 1
  | .free _ _ => 1
  | .decl _ _ => 1

theorem stmtDepth_pos (s : CStmt) : 1 ≤ stmtDepth s := by
  cases s <;> simp [stmtDepth]

theorem swp_sound_normal (body : CStmt) (hloop : LoopFree body) (hnr : NoReturn body) :
    ∀ {Q st fuel},
      stmtDepth body ≤ fuel →
      swp body Q st →
      ∃ st', execStmt fuel body st = some (.normal st') ∧ Q CVal.undef st' := by
  intro Q st fuel hfuel hswp
  induction body generalizing Q st fuel with
  | skip =>
      cases fuel with
      | zero =>
          cases (Nat.not_succ_le_zero _ hfuel)
      | succ fuel' =>
          exact ⟨st, by simp [execStmt], hswp⟩
  | ret e =>
      cases hnr
  | assign lhs rhs =>
      cases fuel with
      | zero =>
          cases (Nat.not_succ_le_zero _ hfuel)
      | succ fuel' =>
          cases lhs with
          | var x =>
              cases hEval : evalExpr rhs st with
              | none =>
                  have : False := by simpa [swp, hEval] using hswp
                  cases this
              | some v =>
                  have hq : Q CVal.undef (st.updateVar x v) := by
                    simpa [swp, hEval] using hswp
                  exact ⟨st.updateVar x v, by simp [execStmt, hEval], hq⟩
          | deref p =>
              cases hP : evalExpr p st with
              | none =>
                  have : False := by simpa [swp, hP] using hswp
                  cases this
              | some pv =>
                  cases pv with
                  | int n =>
                      have : False := by simpa [swp, hP] using hswp
                      cases this
                  | uint n sz =>
                      have : False := by simpa [swp, hP] using hswp
                      cases this
                  | float v =>
                      have : False := by simpa [swp, hP] using hswp
                      cases this
                  | null =>
                      have : False := by simpa [swp, hP] using hswp
                      cases this
                  | undef =>
                      have : False := by simpa [swp, hP] using hswp
                      cases this
                  | structVal fields =>
                      have : False := by simpa [swp, hP] using hswp
                      cases this
                  | unionVal tag v' =>
                      have : False := by simpa [swp, hP] using hswp
                      cases this
                  | ptr block offset =>
                      let addr : PtrVal := { block := block, offset := offset }
                      cases hE : evalExpr rhs st with
                      | none =>
                          have : False := by simpa [swp, hP, hE] using hswp
                          cases this
                      | some v =>
                          have hpair : (∃ vOld, st.readPtr addr = some vOld) ∧
                              ∃ st', st.writePtr addr v = some st' ∧ Q CVal.undef st' := by
                            simpa [swp, hP, hE] using hswp
                          rcases hpair with ⟨_vOld, st', hwrite, hq⟩
                          refine ⟨st', ?_, hq⟩
                          simp [execStmt, hP, hE, addr, hwrite]
          | fieldAccess p field =>
              cases hP : evalExpr p st with
              | none =>
                  have : False := by simpa [swp, hP] using hswp
                  cases this
              | some pv =>
                  cases pv with
                  | int n =>
                      have : False := by simpa [swp, hP] using hswp
                      cases this
                  | uint n sz =>
                      have : False := by simpa [swp, hP] using hswp
                      cases this
                  | float v =>
                      have : False := by simpa [swp, hP] using hswp
                      cases this
                  | null =>
                      have : False := by simpa [swp, hP] using hswp
                      cases this
                  | undef =>
                      have : False := by simpa [swp, hP] using hswp
                      cases this
                  | structVal fields =>
                      have : False := by simpa [swp, hP] using hswp
                      cases this
                  | unionVal tag v' =>
                      have : False := by simpa [swp, hP] using hswp
                      cases this
                  | ptr block offset =>
                      let addr : PtrVal := { block := block, offset := offset }
                      cases hE : evalExpr rhs st with
                      | none =>
                          have : False := by simpa [swp, hP, hE] using hswp
                          cases this
                      | some v =>
                          have hpair : ∃ slot vOld st',
                              PtrVal.addOffset addr (Int.ofNat (fieldOffset field)) = some slot ∧
                              st.readPtr slot = some vOld ∧
                              st.writePtr slot v = some st' ∧
                              Q CVal.undef st' := by
                            simpa [swp, hP, hE] using hswp
                          rcases hpair with ⟨slot, _vOld, st', hslot, _hread, hwrite, hq⟩
                          refine ⟨st', ?_, hq⟩
                          simp [execStmt, hP, hE]
                          change ((PtrVal.addOffset addr (Int.ofNat (fieldOffset field))).bind
                            (fun slot => Option.map ExecResult.normal (st.writePtr slot v))) =
                            some (ExecResult.normal st')
                          rw [hslot]
                          simp [Option.bind, hwrite]
          | intLit _ =>
              cases hswp
          | floatLit v =>
              cases hswp
          | sizeOf _ =>
              cases hswp
          | cast _ _ =>
              cases hswp
          | null =>
              cases hswp
          | binop _ _ _ =>
              cases hswp
          | arrayAccess _ _ =>
              cases hswp
          | addrOf _ =>
              cases hswp
          | call _ _ =>
              cases hswp
  | seq s1 s2 ih1 ih2 =>
      rcases hloop with ⟨hloop1, hloop2⟩
      rcases hnr with ⟨hnr1, hnr2⟩
      cases fuel with
      | zero =>
          cases (Nat.not_succ_le_zero _ hfuel)
      | succ fuel' =>
          have hmax : max (stmtDepth s1) (stmtDepth s2) ≤ fuel' := by
            simpa [stmtDepth] using hfuel
          have hfuel1 : stmtDepth s1 ≤ fuel' := le_trans (Nat.le_max_left _ _) hmax
          have hfuel2 : stmtDepth s2 ≤ fuel' := le_trans (Nat.le_max_right _ _) hmax
          rcases ih1 hloop1 hnr1 hfuel1 hswp with ⟨st', hexec1, hmid⟩
          rcases ih2 hloop2 hnr2 hfuel2 hmid with ⟨st'', hexec2, hq⟩
          refine ⟨st'', ?_, hq⟩
          simp [execStmt, hexec1, hexec2]
  | ite cond th el ihTh ihEl =>
      rcases hloop with ⟨hloopTh, hloopEl⟩
      rcases hnr with ⟨hnrTh, hnrEl⟩
      cases fuel with
      | zero =>
          cases (Nat.not_succ_le_zero _ hfuel)
      | succ fuel' =>
          have hmax : max (stmtDepth th) (stmtDepth el) ≤ fuel' := by
            simpa [stmtDepth] using hfuel
          have hfuelTh : stmtDepth th ≤ fuel' := le_trans (Nat.le_max_left _ _) hmax
          have hfuelEl : stmtDepth el ≤ fuel' := le_trans (Nat.le_max_right _ _) hmax
          cases hcond : evalExpr cond st with
          | none =>
              have : False := by simpa [swp, hcond] using hswp
              cases this
          | some v =>
              by_cases htruth : isTruthy v = true
              ·
                have hbranch : swp th Q st := by
                  simpa [swp, hcond, htruth] using hswp
                rcases ihTh hloopTh hnrTh hfuelTh hbranch with ⟨st', hexec, hq⟩
                refine ⟨st', ?_, hq⟩
                simp [execStmt, hcond, htruth, hexec]
              ·
                have hbranch : swp el Q st := by
                  simpa [swp, hcond, htruth] using hswp
                rcases ihEl hloopEl hnrEl hfuelEl hbranch with ⟨st', hexec, hq⟩
                refine ⟨st', ?_, hq⟩
                simp [execStmt, hcond, htruth, hexec]
  | block decls body ih =>
      cases fuel with
      | zero =>
          cases (Nat.not_succ_le_zero _ hfuel)
      | succ fuel' =>
          have hfuelBody : stmtDepth body ≤ fuel' := by
            simpa [stmtDepth] using hfuel
          have hbody :
              swp body (fun ret st' => Q ret (restoreBlockState st st' decls))
                (enterBlockState st decls) := by
            simpa [swp] using hswp
          rcases ih hloop hnr hfuelBody hbody with ⟨st', hexec, hq⟩
          refine ⟨restoreBlockState st st' decls, ?_, hq⟩
          simp [execStmt, hexec]
  | switch e tag caseBody default ihCase ihDefault =>
      cases hloop
  | forLoop init cond step body ih =>
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
          cases (Nat.not_succ_le_zero _ hfuel)
      | succ fuel' =>
          let st' : CState := st.allocCells x cells
          refine ⟨st', ?_, hswp⟩
          simp [st', execStmt]
  | free e cells =>
      cases fuel with
      | zero =>
          cases (Nat.not_succ_le_zero _ hfuel)
      | succ fuel' =>
          cases hEval : evalExpr e st with
          | none =>
              have : False := by simpa [swp, hEval] using hswp
              cases this
          | some v =>
              cases v with
              | int n =>
                  have : False := by simpa [swp, hEval] using hswp
                  cases this
              | uint n sz =>
                  have : False := by simpa [swp, hEval] using hswp
                  cases this
              | float v =>
                  have : False := by simpa [swp, hEval] using hswp
                  cases this
              | null =>
                  have : False := by simpa [swp, hEval] using hswp
                  cases this
              | undef =>
                  have : False := by simpa [swp, hEval] using hswp
                  cases this
              | structVal fields =>
                  have : False := by simpa [swp, hEval] using hswp
                  cases this
              | unionVal tag v' =>
                  have : False := by simpa [swp, hEval] using hswp
                  cases this
              | ptr block offset =>
                  let addr : PtrVal := { block := block, offset := offset }
                  rcases (show ∃ flatAddr, st.resolvePtr addr = some flatAddr ∧ Q CVal.undef (st.freeCells flatAddr cells) by
                    simpa [swp, hEval] using hswp
                  ) with ⟨flatAddr, hresolve, hq⟩
                  refine ⟨st.freeCells flatAddr cells, ?_, hq⟩
                  simp [execStmt, hEval, addr, hresolve, CState.freeCells]
  | decl x ty =>
      cases fuel with
      | zero =>
          cases (Nat.not_succ_le_zero _ hfuel)
      | succ fuel' =>
          exact ⟨st.updateVar x CVal.undef, by simp [execStmt], hswp⟩

theorem swp_sound (body : CStmt) (hloop : LoopFree body) (htail : TailReturn body)
    {Q st fuel} :
    stmtDepth body ≤ fuel →
    swp body Q st →
    ∃ res, execStmt fuel body st = some res ∧
      match res with
      | .returned v st' => Q v st'
      | .normal st' => Q CVal.undef st' := by
  intro hfuel hswp
  induction body generalizing Q st fuel with
  | skip =>
      cases fuel with
      | zero =>
          cases (Nat.not_succ_le_zero _ hfuel)
      | succ fuel' =>
          exact ⟨.normal st, by simp [execStmt], hswp⟩
  | ret e =>
      cases fuel with
      | zero =>
          cases (Nat.not_succ_le_zero _ hfuel)
      | succ fuel' =>
          cases hEval : evalExpr e st with
          | none =>
              have : False := by simpa [swp, hEval] using hswp
              cases this
          | some v =>
              have hq : Q v st := by simpa [swp, hEval] using hswp
              exact ⟨.returned v st, by simp [execStmt, hEval], hq⟩
  | assign lhs rhs =>
      have hnr : NoReturn (.assign lhs rhs) := by simp [NoReturn]
      rcases swp_sound_normal (.assign lhs rhs) hloop hnr hfuel hswp with ⟨st', hexec, hq⟩
      exact ⟨.normal st', hexec, hq⟩
  | seq s1 s2 ih1 ih2 =>
      rcases hloop with ⟨hloop1, hloop2⟩
      rcases htail with ⟨htail1, htail2, hnr1⟩
      cases fuel with
      | zero =>
          cases (Nat.not_succ_le_zero _ hfuel)
      | succ fuel' =>
          have hmax : max (stmtDepth s1) (stmtDepth s2) ≤ fuel' := by
            simpa [stmtDepth] using hfuel
          have hfuel1 : stmtDepth s1 ≤ fuel' := le_trans (Nat.le_max_left _ _) hmax
          have hfuel2 : stmtDepth s2 ≤ fuel' := le_trans (Nat.le_max_right _ _) hmax
          rcases swp_sound_normal s1 hloop1 hnr1 hfuel1 hswp with ⟨st', hexec1, hmid⟩
          rcases ih2 hloop2 htail2 hfuel2 hmid with ⟨res, hexec2, hq⟩
          refine ⟨res, ?_, hq⟩
          simp [execStmt, hexec1, hexec2]
  | ite cond th el ihTh ihEl =>
      rcases hloop with ⟨hloopTh, hloopEl⟩
      rcases htail with ⟨htailTh, htailEl⟩
      cases fuel with
      | zero =>
          cases (Nat.not_succ_le_zero _ hfuel)
      | succ fuel' =>
          have hmax : max (stmtDepth th) (stmtDepth el) ≤ fuel' := by
            simpa [stmtDepth] using hfuel
          have hfuelTh : stmtDepth th ≤ fuel' := le_trans (Nat.le_max_left _ _) hmax
          have hfuelEl : stmtDepth el ≤ fuel' := le_trans (Nat.le_max_right _ _) hmax
          cases hcond : evalExpr cond st with
          | none =>
              have : False := by simpa [swp, hcond] using hswp
              cases this
          | some v =>
              by_cases htruth : isTruthy v = true
              ·
                have hbranch : swp th Q st := by
                  simpa [swp, hcond, htruth] using hswp
                rcases ihTh hloopTh htailTh hfuelTh hbranch with ⟨res, hexec, hq⟩
                refine ⟨res, ?_, hq⟩
                simp [execStmt, hcond, htruth, hexec]
              ·
                have hbranch : swp el Q st := by
                  simpa [swp, hcond, htruth] using hswp
                rcases ihEl hloopEl htailEl hfuelEl hbranch with ⟨res, hexec, hq⟩
                refine ⟨res, ?_, hq⟩
                simp [execStmt, hcond, htruth, hexec]
  | block decls body ih =>
      cases fuel with
      | zero =>
          cases (Nat.not_succ_le_zero _ hfuel)
      | succ fuel' =>
          have hfuelBody : stmtDepth body ≤ fuel' := by
            simpa [stmtDepth] using hfuel
          have hbody :
              swp body (fun ret st' => Q ret (restoreBlockState st st' decls))
                (enterBlockState st decls) := by
            simpa [swp] using hswp
          rcases ih hloop htail hfuelBody hbody with ⟨res, hexec, hq⟩
          cases res with
          | normal st' =>
              refine ⟨.normal (restoreBlockState st st' decls), ?_, hq⟩
              simp [execStmt, hexec]
          | returned v st' =>
              refine ⟨.returned v (restoreBlockState st st' decls), ?_, hq⟩
              simp [execStmt, hexec]
  | switch e tag caseBody default ihCase ihDefault =>
      cases hloop
  | forLoop init cond step body ih =>
      cases hloop
  | «break» =>
      cases hloop
  | «continue» =>
      cases hloop
  | whileInv cond inv body ih =>
      cases hloop
  | alloc x cells =>
      have hnr : NoReturn (.alloc x cells) := by simp [NoReturn]
      rcases swp_sound_normal (.alloc x cells) hloop hnr hfuel hswp with ⟨st', hexec, hq⟩
      exact ⟨.normal st', hexec, hq⟩
  | free e cells =>
      have hnr : NoReturn (.free e cells) := by simp [NoReturn]
      rcases swp_sound_normal (.free e cells) hloop hnr hfuel hswp with ⟨st', hexec, hq⟩
      exact ⟨.normal st', hexec, hq⟩
  | decl x ty =>
      have hnr : NoReturn (.decl x ty) := by simp [NoReturn]
      rcases swp_sound_normal (.decl x ty) hloop hnr hfuel hswp with ⟨st', hexec, hq⟩
      exact ⟨.normal st', hexec, hq⟩

/-- Soundness for `swpMemPost` on normal completion. This transports the
existing loop-free theorem onto Mem-valued postconditions via
`SProp.ofMemHProp`, without claiming that the operational semantics themselves
already execute over `Mem`. -/
theorem swp_sound_normal_memPost (body : CStmt) (hloop : LoopFree body) (hnr : NoReturn body) :
    ∀ {Q st fuel},
      stmtDepth body ≤ fuel →
      swpMemPost body Q st →
      ∃ st', execStmt fuel body st = some (.normal st') ∧ Q CVal.undef (heapToMem st'.heap) := by
  intro Q st fuel hfuel hswp
  rcases swp_sound_normal body hloop hnr (Q := fun v => SProp.ofMemHProp (Q v)) hfuel hswp with
    ⟨st', hexec, hq⟩
  exact ⟨st', hexec, hq⟩

/-- Soundness for `swpMemPost`, transporting the existing tail-return theorem
onto Mem-valued postconditions. -/
theorem swp_sound_memPost (body : CStmt) (hloop : LoopFree body) (htail : TailReturn body)
    {Q st fuel} :
    stmtDepth body ≤ fuel →
    swpMemPost body Q st →
    ∃ res, execStmt fuel body st = some res ∧
      match res with
      | .returned v st' => Q v (heapToMem st'.heap)
      | .normal st' => Q CVal.undef (heapToMem st'.heap) := by
  intro hfuel hswp
  rcases swp_sound body hloop htail (Q := fun v => SProp.ofMemHProp (Q v)) hfuel hswp with
    ⟨res, hexec, hq⟩
  exact ⟨res, hexec, hq⟩

end HeytingLean.LeanCP
