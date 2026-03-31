import HeytingLean.LeanCP.VCG.SymExec
import HeytingLean.LeanCP.VCG.SWhile
import HeytingLean.LeanCP.VCG.WhileSound
import HeytingLean.LeanCP.VCG.SWPCallSound

/-!
# LeanCP End-to-End Soundness

Phase 6 composes the generated VC bundle surface from `SymExec` with the
already-landed operational soundness theorems. This file starts with the
loop-free / tail-return fragment, which is already fully supported by
`swp_sound` and `swpFull_sound`.
-/

namespace HeytingLean.LeanCP

def execFuelFor (mode : VerifyMode) (funEnv : FunEnv) (loops : List LoopHint) :
    CStmt → List Nat → Except VCGenError Nat
  | .seq s1 s2, path => do
      let f1 ← execFuelFor mode funEnv loops s1 (childPath path 0)
      let f2 ← execFuelFor mode funEnv loops s2 (childPath path 1)
      pure (max f1 f2 + 1)
  | .ite _ th el, path => do
      let fTh ← execFuelFor mode funEnv loops th (childPath path 0)
      let fEl ← execFuelFor mode funEnv loops el (childPath path 1)
      pure (max fTh fEl + 1)
  | .block _ body, path => do
      let f ← execFuelFor mode funEnv loops body (childPath path 0)
      pure (f + 1)
  | .whileInv _ _ body, path => do
      let some hint := findLoopHint? loops path
        | throw (.missingLoopHint path)
      match mode with
      | .swp => pure (swhileFuel body hint.fuelHint)
      | .swpFull => pure (swhileFuelFull funEnv body hint.fuelHint)
  | stmt, _path =>
      match mode with
      | .swp => pure (stmtDepth stmt)
      | .swpFull => pure (stmtDepthFull funEnv stmt)

theorem generateBundle_pre_eq (input : VerifyInput) :
    ∀ {bundle},
      generateBundle input = Except.ok bundle →
      requiredPre input.mode input.funEnv input.loops input.body input.post [] = Except.ok bundle.pre := by
  intro bundle hgen
  unfold generateBundle at hgen
  cases hvalid : validateLoopHints input.body input.loops with
  | error err =>
      simp [hvalid] at hgen
      cases hgen
  | ok _ =>
      simp [hvalid] at hgen
      cases hpre : requiredPre input.mode input.funEnv input.loops input.body input.post [] with
      | error err =>
          simp [hpre] at hgen
          cases hgen
      | ok pre =>
          cases hlocals :
              collectLocalVCs input.name input.mode input.funEnv input.loops
                input.body input.pre input.post [] with
          | error err =>
              simp [hpre, hlocals] at hgen
              cases hgen
          | ok locals =>
              simp [hpre, hlocals] at hgen
              injection hgen with hbundle
              have hpreEq : pre = bundle.pre := by
                simpa using congrArg VCBundle.pre hbundle
              simpa [hpreEq] using hpre

theorem requiredPre_eq_surfacePre_loopFree
    (mode : VerifyMode) (funEnv : FunEnv) (loops : List LoopHint) :
    ∀ {stmt Q path},
      LoopFree stmt →
      requiredPre mode funEnv loops stmt Q path =
        Except.ok (surfacePre mode funEnv stmt Q)
  | .skip, Q, path, hloop => by
      cases mode <;> rfl
  | .ret e, Q, path, hloop => by
      cases mode <;> rfl
  | .assign lhs rhs, Q, path, hloop => by
      cases mode <;> rfl
  | .seq s1 s2, Q, path, hloop => by
      rcases hloop with ⟨h1, h2⟩
      cases mode
      · unfold requiredPre surfacePre
        rw [requiredPre_eq_surfacePre_loopFree (.swp) funEnv loops
            (stmt := s2) (Q := Q) (path := childPath path 1) h2]
        change requiredPre .swp funEnv loops s1 (fun _ => swp s2 Q) (childPath path 0) =
          Except.ok (swp s1 (fun _ => swp s2 Q))
        exact requiredPre_eq_surfacePre_loopFree (.swp) funEnv loops
          (stmt := s1) (Q := fun _ => swp s2 Q) (path := childPath path 0) h1
      · unfold requiredPre surfacePre
        rw [requiredPre_eq_surfacePre_loopFree (.swpFull) funEnv loops
            (stmt := s2) (Q := Q) (path := childPath path 1) h2]
        change requiredPre .swpFull funEnv loops s1 (fun _ => swpFull funEnv s2 Q)
            (childPath path 0) =
          Except.ok (swpFull funEnv s1 (fun _ => swpFull funEnv s2 Q))
        exact requiredPre_eq_surfacePre_loopFree (.swpFull) funEnv loops
          (stmt := s1) (Q := fun _ => swpFull funEnv s2 Q) (path := childPath path 0) h1
  | .ite cond th el, Q, path, hloop => by
      rcases hloop with ⟨hth, hel⟩
      cases mode
      · unfold requiredPre surfacePre
        rw [requiredPre_eq_surfacePre_loopFree (.swp) funEnv loops
            (stmt := th) (Q := Q) (path := childPath path 0) hth]
        rw [requiredPre_eq_surfacePre_loopFree (.swp) funEnv loops
            (stmt := el) (Q := Q) (path := childPath path 1) hel]
        rfl
      · unfold requiredPre surfacePre
        rw [requiredPre_eq_surfacePre_loopFree (.swpFull) funEnv loops
            (stmt := th) (Q := Q) (path := childPath path 0) hth]
        rw [requiredPre_eq_surfacePre_loopFree (.swpFull) funEnv loops
            (stmt := el) (Q := Q) (path := childPath path 1) hel]
        rfl
  | .block decls body, Q, path, hloop => by
      cases mode <;> rfl
  | .switch e tag caseBody default, Q, path, hloop => by
      cases hloop
  | .forLoop init cond step body, Q, path, hloop => by
      cases hloop
  | .break, Q, path, hloop => by
      cases hloop
  | .continue, Q, path, hloop => by
      cases hloop
  | .whileInv cond inv body, Q, path, hloop => by
      cases hloop
  | .alloc x cells, Q, path, hloop => by
      cases mode <;> rfl
  | .free e cells, Q, path, hloop => by
      cases mode <;> rfl
  | .decl x ty, Q, path, hloop => by
      cases mode <;> rfl

theorem execFuelFor_eq_surface_loopFree
    (mode : VerifyMode) (funEnv : FunEnv) (loops : List LoopHint) :
    ∀ {stmt path},
      LoopFree stmt →
      execFuelFor mode funEnv loops stmt path =
        Except.ok (match mode with
          | .swp => stmtDepth stmt
          | .swpFull => stmtDepthFull funEnv stmt)
  | .skip, path, hloop => by
      cases mode <;> rfl
  | .ret e, path, hloop => by
      cases mode <;> rfl
  | .assign lhs rhs, path, hloop => by
      cases mode <;> rfl
  | .seq s1 s2, path, hloop => by
      rcases hloop with ⟨h1, h2⟩
      cases mode
      · unfold execFuelFor
        rw [execFuelFor_eq_surface_loopFree (.swp) funEnv loops
            (stmt := s1) (path := childPath path 0) h1]
        rw [execFuelFor_eq_surface_loopFree (.swp) funEnv loops
            (stmt := s2) (path := childPath path 1) h2]
        rfl
      · unfold execFuelFor
        rw [execFuelFor_eq_surface_loopFree (.swpFull) funEnv loops
            (stmt := s1) (path := childPath path 0) h1]
        rw [execFuelFor_eq_surface_loopFree (.swpFull) funEnv loops
            (stmt := s2) (path := childPath path 1) h2]
        rfl
  | .ite cond th el, path, hloop => by
      rcases hloop with ⟨hth, hel⟩
      cases mode
      · unfold execFuelFor
        rw [execFuelFor_eq_surface_loopFree (.swp) funEnv loops
            (stmt := th) (path := childPath path 0) hth]
        rw [execFuelFor_eq_surface_loopFree (.swp) funEnv loops
            (stmt := el) (path := childPath path 1) hel]
        rfl
      · unfold execFuelFor
        rw [execFuelFor_eq_surface_loopFree (.swpFull) funEnv loops
            (stmt := th) (path := childPath path 0) hth]
        rw [execFuelFor_eq_surface_loopFree (.swpFull) funEnv loops
            (stmt := el) (path := childPath path 1) hel]
        rfl
  | .block decls body, path, hloop => by
      cases mode
      · simp [execFuelFor, stmtDepth,
          execFuelFor_eq_surface_loopFree (.swp) funEnv loops (stmt := body) (path := childPath path 0) hloop]
      · simp [execFuelFor, stmtDepthFull,
          execFuelFor_eq_surface_loopFree (.swpFull) funEnv loops (stmt := body) (path := childPath path 0) hloop]
  | .switch e tag caseBody default, path, hloop => by
      cases hloop
  | .forLoop init cond step body, path, hloop => by
      cases hloop
  | .break, path, hloop => by
      cases hloop
  | .continue, path, hloop => by
      cases hloop
  | .whileInv cond inv body, path, hloop => by
      cases hloop
  | .alloc x cells, path, hloop => by
      cases mode <;> rfl
  | .free e cells, path, hloop => by
      cases mode <;> rfl
  | .decl x ty, path, hloop => by
      cases mode <;> rfl

theorem requiredPre_root_while_swp
    (funEnv : FunEnv) (loops : List LoopHint) (cond : CExpr) (ann : HProp)
    (body : CStmt) (Q : CVal → SProp) (hint : LoopHint)
    (hhint : findLoopHint? loops [] = some hint) :
    requiredPre .swp funEnv loops (.whileInv cond ann body) Q [] =
      Except.ok (swhileWP hint.fuelHint cond hint.inv body Q) := by
  simp [requiredPre, whileSurface, hhint, pure]
  rfl

theorem requiredPre_root_while_swpFull
    (funEnv : FunEnv) (loops : List LoopHint) (cond : CExpr) (ann : HProp)
    (body : CStmt) (Q : CVal → SProp) (hint : LoopHint)
    (hhint : findLoopHint? loops [] = some hint) :
    requiredPre .swpFull funEnv loops (.whileInv cond ann body) Q [] =
      Except.ok (swhileWPFull funEnv hint.fuelHint cond hint.inv body Q) := by
  simp [requiredPre, whileSurface, hhint, pure]
  rfl

theorem execFuelFor_root_while_swp
    (funEnv : FunEnv) (loops : List LoopHint) (cond : CExpr) (ann : HProp)
    (body : CStmt) (hint : LoopHint)
    (hhint : findLoopHint? loops [] = some hint) :
    execFuelFor .swp funEnv loops (.whileInv cond ann body) [] =
      Except.ok (swhileFuel body hint.fuelHint) := by
  simp [execFuelFor, hhint, pure]
  rfl

theorem execFuelFor_root_while_swpFull
    (funEnv : FunEnv) (loops : List LoopHint) (cond : CExpr) (ann : HProp)
    (body : CStmt) (hint : LoopHint)
    (hhint : findLoopHint? loops [] = some hint) :
    execFuelFor .swpFull funEnv loops (.whileInv cond ann body) [] =
      Except.ok (swhileFuelFull funEnv body hint.fuelHint) := by
  simp [execFuelFor, hhint, pure]
  rfl

theorem verifyInput_sound_swp_loopFree (input : VerifyInput) :
    ∀ {bundle fuel},
      input.mode = .swp →
      LoopFree input.body →
      TailReturn input.body →
      generateBundle input = Except.ok bundle →
      execFuelFor input.mode input.funEnv input.loops input.body [] = Except.ok fuel →
      VCListValid bundle.vcs →
      ∀ st, input.pre st →
        ∃ res, execStmt fuel input.body st = some res ∧
          match res with
          | .returned v st' => input.post v st'
          | .normal st' => input.post CVal.undef st'
  := by
  intro bundle fuel hmode hloop htail hgen hfuel hvalid st hpre
  have hbundlepre := generateBundle_sound input hgen hvalid st hpre
  have hpreEq := generateBundle_pre_eq input hgen
  rw [hmode] at hpreEq hfuel
  rw [requiredPre_eq_surfacePre_loopFree .swp input.funEnv input.loops
      (stmt := input.body) (Q := input.post) (path := []) hloop] at hpreEq
  rw [execFuelFor_eq_surface_loopFree .swp input.funEnv input.loops
      (stmt := input.body) (path := []) hloop] at hfuel
  injection hpreEq with hPreDef
  injection hfuel with _hFuelDef
  subst fuel
  have hswp : swp input.body input.post st := by
    simpa [surfacePre] using (show surfacePre .swp input.funEnv input.body input.post st from by
      simpa [hPreDef] using hbundlepre)
  exact swp_sound input.body hloop htail (fuel := stmtDepth input.body) (Q := input.post) (st := st)
    (by simp) hswp

theorem verifyInput_sound_swpFull_loopFree (input : VerifyInput) (henv : FunEnvSound input.funEnv) :
    ∀ {bundle fuel},
      input.mode = .swpFull →
      LoopFree input.body →
      TailReturn input.body →
      generateBundle input = Except.ok bundle →
      execFuelFor input.mode input.funEnv input.loops input.body [] = Except.ok fuel →
      VCListValid bundle.vcs →
      ∀ st, input.pre st →
        ∃ res, execStmtFull input.funEnv fuel input.body st = some res ∧
          match res with
          | .returned v st' => input.post v st'
          | .normal st' => input.post CVal.undef st'
  := by
  intro bundle fuel hmode hloop htail hgen hfuel hvalid st hpre
  have hbundlepre := generateBundle_sound input hgen hvalid st hpre
  have hpreEq := generateBundle_pre_eq input hgen
  rw [hmode] at hpreEq hfuel
  rw [requiredPre_eq_surfacePre_loopFree .swpFull input.funEnv input.loops
      (stmt := input.body) (Q := input.post) (path := []) hloop] at hpreEq
  rw [execFuelFor_eq_surface_loopFree .swpFull input.funEnv input.loops
      (stmt := input.body) (path := []) hloop] at hfuel
  injection hpreEq with hPreDef
  injection hfuel with _hFuelDef
  subst fuel
  have hswp : swpFull input.funEnv input.body input.post st := by
    simpa [surfacePre] using (show surfacePre .swpFull input.funEnv input.body input.post st from by
      simpa [hPreDef] using hbundlepre)
  exact swpFull_sound input.funEnv henv input.body hloop htail
    (fuel := stmtDepthFull input.funEnv input.body) (Q := input.post) (st := st)
    (by simp) hswp

theorem verifyInput_sound_swp_normal (input : VerifyInput) :
    ∀ {cond ann body hint bundle fuel},
      input.mode = .swp →
      input.body = .whileInv cond ann body →
      findLoopHint? input.loops [] = some hint →
      LoopFree body →
      NoReturn body →
      generateBundle input = Except.ok bundle →
      execFuelFor input.mode input.funEnv input.loops input.body [] = Except.ok fuel →
      VCListValid bundle.vcs →
      ∀ st, input.pre st →
        ∃ st', execStmt fuel input.body st = some (.normal st') ∧
          input.post CVal.undef st' := by
  intro cond ann body hint bundle fuel hmode hbody hhint hloop hnr hgen hfuel hvalid st hpre
  have hbundlepre := generateBundle_sound input hgen hvalid st hpre
  have hpreEq := generateBundle_pre_eq input hgen
  rw [hmode, hbody] at hpreEq hfuel
  rw [requiredPre_root_while_swp input.funEnv input.loops cond ann body input.post hint hhint] at hpreEq
  rw [execFuelFor_root_while_swp input.funEnv input.loops cond ann body hint hhint] at hfuel
  injection hpreEq with hPreDef
  injection hfuel with _hFuelDef
  subst fuel
  have hwp : swhileWP hint.fuelHint cond hint.inv body input.post st := by
    simpa [hPreDef] using hbundlepre
  simpa [hbody] using (swhileWP_sound cond hint.inv ann body hloop hnr hwp)

theorem verifyInput_sound_swpFull_normal (input : VerifyInput) (henv : FunEnvSound input.funEnv) :
    ∀ {cond ann body hint bundle fuel},
      input.mode = .swpFull →
      input.body = .whileInv cond ann body →
      findLoopHint? input.loops [] = some hint →
      LoopFree body →
      NoReturn body →
      generateBundle input = Except.ok bundle →
      execFuelFor input.mode input.funEnv input.loops input.body [] = Except.ok fuel →
      VCListValid bundle.vcs →
      ∀ st, input.pre st →
        ∃ st', execStmtFull input.funEnv fuel input.body st = some (.normal st') ∧
          input.post CVal.undef st' := by
  intro cond ann body hint bundle fuel hmode hbody hhint hloop hnr hgen hfuel hvalid st hpre
  have hbundlepre := generateBundle_sound input hgen hvalid st hpre
  have hpreEq := generateBundle_pre_eq input hgen
  rw [hmode, hbody] at hpreEq hfuel
  rw [requiredPre_root_while_swpFull input.funEnv input.loops cond ann body input.post hint hhint] at hpreEq
  rw [execFuelFor_root_while_swpFull input.funEnv input.loops cond ann body hint hhint] at hfuel
  injection hpreEq with hPreDef
  injection hfuel with _hFuelDef
  subst fuel
  have hwp : swhileWPFull input.funEnv hint.fuelHint cond hint.inv body input.post st := by
    simpa [hPreDef] using hbundlepre
  simpa [hbody] using
    (swhileWPFull_sound input.funEnv henv cond hint.inv ann body hloop hnr hwp)

end HeytingLean.LeanCP
