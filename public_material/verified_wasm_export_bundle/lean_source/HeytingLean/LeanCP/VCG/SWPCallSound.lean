import HeytingLean.LeanCP.VCG.SWhile

/-!
# LeanCP Operational Calls

This module adds the executable call layer that earlier parity work left open.
The supported operational call sites are the existing AST patterns

- `.assign (.var x) (.call fname args)`
- `.ret (.call fname args)`

The callee runs on a fresh local environment containing only its formal
parameters. On return, the caller environment is restored while preserving the
callee's heap and allocator effects.

This is intentionally narrower than a full side-effecting expression semantics:
nested calls in arbitrary expressions still evaluate to `none` through the old
`evalExpr` surface.

Recursive and mutually recursive callees are handled by
`HeytingLean.LeanCP.VCG.RecCallSound`, which reuses the same `swpCall`,
`callEntryState`, and `restoreCallerState` interfaces while replacing the
operational layer with `execCallRec` / `execStmtRec`.
-/

set_option linter.unnecessarySimpa false

namespace HeytingLean.LeanCP

/-- Evaluate call arguments in the caller state. Arguments themselves remain
pure and use the existing `evalExpr` surface. -/
def evalArgs (args : List CExpr) (st : CState) : Option (List CVal) :=
  args.mapM (fun arg => evalExpr arg st)

/-- Bind formal parameters to evaluated argument values. -/
def bindCallEnv (params : List (String × CType)) (vals : List CVal) : Env :=
  params.zip vals |>.map fun ((name, _), val) => (name, val)

/-- Callee entry state: keep heap/allocator, replace locals with formals. -/
def callEntryState (caller : CState) (spec : SFunSpec) (vals : List CVal) : CState :=
  { heap := caller.heap
    env := bindCallEnv spec.params vals
    nextAddr := caller.nextAddr
    mem := caller.mem
    allocs := caller.allocs }

/-- Restore the caller environment while keeping callee heap effects. -/
def restoreCallerState (caller callee : CState) : CState :=
  { heap := callee.heap
    env := caller.env
    nextAddr := callee.nextAddr
    mem := callee.mem
    allocs := callee.allocs }

/-- Fuel proxy for a direct call site. -/
def callDepth (funEnv : FunEnv) (fname : String) : Nat :=
  match funEnv fname with
  | some spec => stmtDepth spec.body + 1
  | none => 1

/-- A spec-level call rule that is now aligned with actual call entry/exit
states. The precondition is checked on the callee entry state, and the caller
continuation sees the restored caller state after the callee postcondition. -/
def swpCall (funEnv : FunEnv) (fname : String) (args : List CExpr)
    (Q : CVal → SProp) : SProp := fun st =>
  ∃ spec vals,
    funEnv fname = some spec ∧
    evalArgs args st = some vals ∧
    vals.length = spec.params.length ∧
    spec.pre (callEntryState st spec vals) ∧
    (∀ retVal st', spec.post retVal st' → Q retVal (restoreCallerState st st'))

theorem swpCall_intro (funEnv : FunEnv) (fname : String) (args : List CExpr)
    (spec : SFunSpec) (vals : List CVal) (Q : CVal → SProp) {st}
    (hlookup : funEnv fname = some spec)
    (hvals : evalArgs args st = some vals)
    (hlen : vals.length = spec.params.length)
    (hpre : spec.pre (callEntryState st spec vals))
    (hpost : ∀ retVal st', spec.post retVal st' → Q retVal (restoreCallerState st st')) :
    swpCall funEnv fname args Q st := by
  exact ⟨spec, vals, hlookup, hvals, hlen, hpre, hpost⟩

theorem swpCall_elim (funEnv : FunEnv) (fname : String) (args : List CExpr)
    (Q : CVal → SProp) {st} :
    swpCall funEnv fname args Q st →
    ∃ spec vals,
      funEnv fname = some spec ∧
      evalArgs args st = some vals ∧
      vals.length = spec.params.length ∧
      spec.pre (callEntryState st spec vals) ∧
      (∀ retVal st', spec.post retVal st' → Q retVal (restoreCallerState st st')) := by
  intro h
  exact h

/-- Execute a supported call. -/
def execCall (funEnv : FunEnv) (fuel : Nat) (fname : String)
    (args : List CExpr) (caller : CState) : Option (CVal × CState) := do
  let spec ← funEnv fname
  let vals ← evalArgs args caller
  if _hlen : vals.length = spec.params.length then
    let entry := callEntryState caller spec vals
    match ← execStmt fuel spec.body entry with
    | .returned ret callee =>
        some (ret, restoreCallerState caller callee)
    | .normal callee =>
        some (.undef, restoreCallerState caller callee)
  else
    none

/-- Call-aware operational semantics. All non-call clauses coincide with
`execStmt`; only the two supported call-site patterns are new. -/
def execStmtFull (funEnv : FunEnv) : Nat → CStmt → CState → Option ExecResult
  | 0, _, _ => none
  | _, .skip, st => some (.normal st)
  | fuel + 1, .ret (.call fname args), st => do
      let (ret, st') ← execCall funEnv fuel fname args st
      some (.returned ret st')
  | _, .ret e, st => do
      let v ← evalExpr e st
      some (.returned v st)
  | _, .alloc x cells, st =>
      some (.normal (st.allocCells x cells))
  | _, .free e cells, st => do
      let v ← evalExpr e st
      match v with
      | .ptr block offset =>
          let addr : PtrVal := { block := block, offset := offset }
          let flatAddr ← st.resolvePtr addr
          some (.normal (st.freeCells flatAddr cells))
      | _ => none
  | _, .decl x _, st =>
      some (.normal (st.updateVar x CVal.undef))
  | fuel + 1, .block decls body, st => do
      let entry := enterBlockState st decls
      match ← execStmtFull funEnv fuel body entry with
      | .normal st' => some (.normal (restoreBlockState st st' decls))
      | .returned v st' => some (.returned v (restoreBlockState st st' decls))
  | fuel + 1, .switch e tag caseBody default, st => do
      let v ← evalExpr e st
      match v with
      | .int n => if n = tag then execStmtFull funEnv fuel caseBody st else execStmtFull funEnv fuel default st
      | _ => none
  | fuel + 1, .forLoop init cond step body, st =>
      execStmtFull funEnv fuel (desugarFor init cond step body) st
  | _, .break, _ => none
  | _, .continue, _ => none
  | fuel + 1, .assign (.var x) (.call fname args), st => do
      let (ret, st') ← execCall funEnv fuel fname args st
      some (.normal (st'.updateVar x ret))
  | _ + 1, .assign lhs rhs, st => do
      let v ← evalExpr rhs st
      match lhs with
      | .var x => some (.normal (st.updateVar x v))
      | .deref p => do
          let pv ← evalExpr p st
          match pv with
          | .ptr block offset =>
              let addr : PtrVal := { block := block, offset := offset }
              ExecResult.normal <$> st.writePtr addr v
          | _ => none
      | .fieldAccess p field => do
          let pv ← evalExpr p st
          match pv with
          | .ptr block offset => do
              let addr : PtrVal := { block := block, offset := offset }
              let slot ← PtrVal.addOffset addr (Int.ofNat (fieldOffset field))
              ExecResult.normal <$> st.writePtr slot v
          | _ => none
      | _ => none
  | fuel + 1, .seq s1 s2, st => do
      match ← execStmtFull funEnv fuel s1 st with
      | .normal st' => execStmtFull funEnv fuel s2 st'
      | .returned v st' => some (.returned v st')
  | fuel + 1, .ite cond th el, st => do
      let v ← evalExpr cond st
      if isTruthy v then execStmtFull funEnv fuel th st
      else execStmtFull funEnv fuel el st
  | fuel + 1, .whileInv cond inv body, st => do
      let v ← evalExpr cond st
      if isTruthy v then
        match ← execStmtFull funEnv fuel body st with
        | .normal st' => execStmtFull funEnv fuel (.whileInv cond inv body) st'
        | .returned v' st' => some (.returned v' st')
      else
        some (.normal st)

/-- Call-aware weakest preconditions. Only the supported call sites differ from
the existing `swp`. -/
noncomputable def swpFull (funEnv : FunEnv) : CStmt → (CVal → SProp) → SProp
  | .skip, Q => Q CVal.undef
  | .ret (.call fname args), Q => swpCall funEnv fname args Q
  | .ret e, Q => fun st =>
      match evalExpr e st with
      | some v => Q v st
      | none => False
  | .block decls body, Q => fun st =>
      swpFull funEnv body (fun ret st' => Q ret (restoreBlockState st st' decls)) (enterBlockState st decls)
  | .switch _ _ _ _, _ => fun _ => False
  | .forLoop _ _ _ _, _ => fun _ => False
  | .break, _ => fun _ => False
  | .continue, _ => fun _ => False
  | .decl x _, Q => fun st =>
      Q CVal.undef (st.updateVar x CVal.undef)
  | .assign (.var x) (.call fname args), Q =>
      swpCall funEnv fname args (fun ret st => Q CVal.undef (st.updateVar x ret))
  | .assign (.var x) e, Q => fun st =>
      match evalExpr e st with
      | some v => Q CVal.undef (st.updateVar x v)
      | none => False
  | .assign (.deref p) e, Q => fun st =>
      match evalExpr p st, evalExpr e st with
      | some (.ptr block offset), some v =>
          let addr : PtrVal := { block := block, offset := offset }
          (∃ vOld, st.readPtr addr = some vOld) ∧
          ∃ st', st.writePtr addr v = some st' ∧
            Q CVal.undef st'
      | _, _ => False
  | .assign (.fieldAccess p field) e, Q => fun st =>
      match evalExpr p st, evalExpr e st with
      | some (.ptr block offset), some v =>
          let addr : PtrVal := { block := block, offset := offset }
          ∃ slot vOld st',
            PtrVal.addOffset addr (Int.ofNat (fieldOffset field)) = some slot ∧
            st.readPtr slot = some vOld ∧
            st.writePtr slot v = some st' ∧
            Q CVal.undef st'
      | _, _ => False
  | .assign _ _, _ => fun _ => False
  | .seq s1 s2, Q =>
      swpFull funEnv s1 (fun _ => swpFull funEnv s2 Q)
  | .ite cond th el, Q => fun st =>
      match evalExpr cond st with
      | some v => if isTruthy v then swpFull funEnv th Q st else swpFull funEnv el Q st
      | none => False
  | .alloc x cells, Q => fun st =>
      Q CVal.undef (st.allocCells x cells)
  | .free e cells, Q => fun st =>
      match evalExpr e st with
      | some (.ptr block offset) =>
          let addr : PtrVal := { block := block, offset := offset }
          ∃ flatAddr, st.resolvePtr addr = some flatAddr ∧
            Q CVal.undef (st.freeCells flatAddr cells)
      | _ => False
  | .whileInv _cond inv body, Q => fun st =>
      SProp.ofHProp inv st ∧
        (∀ st', SProp.ofHProp inv st' → swpFull funEnv body (fun _ => SProp.ofHProp inv) st') ∧
        (∀ st', SProp.ofHProp inv st' → Q CVal.undef st')

/-- `swpFull` specialized to Mem-valued postconditions via the Phase 1
compatibility bridge `SProp.ofMemHProp`. This transports postconditions through
the proved bridge without claiming that `execStmtFull` already runs directly
over `Mem`. -/
noncomputable def swpFullMemPost (funEnv : FunEnv) (body : CStmt) (Q : CVal → MemHProp) : SProp :=
  swpFull funEnv body (fun v => SProp.ofMemHProp (Q v))

/-- Call-aware VC surface. -/
def sgenVCFull (funEnv : FunEnv) (spec : SFunSpec) : Prop :=
  ∀ st, spec.pre st → swpFull funEnv spec.body spec.post st

/-- Call-aware bounded while rule: same rule shape as `swhileWP`, but the body
is symbolically executed through `swpFull`. -/
noncomputable def swhileWPFull (funEnv : FunEnv) :
    Nat → CExpr → SProp → CStmt → (CVal → SProp) → SProp
  | 0, cond, inv, _body, Q => fun st =>
      inv st ∧
        match evalExpr cond st with
        | some v => if isTruthy v then False else Q CVal.undef st
        | none => False
  | iters + 1, cond, inv, body, Q => fun st =>
      inv st ∧
        match evalExpr cond st with
        | some v =>
            if isTruthy v then
              swpFull funEnv body (fun _ => swhileWPFull funEnv iters cond inv body Q) st
            else
              Q CVal.undef st
        | none => False

/-- A small fuel proxy for the supported call sites. Used by the soundness
theorems (`swpFull_sound`, `swhileWPFull_sound`) proved below. -/
def stmtDepthFull (funEnv : FunEnv) : CStmt → Nat
  | .skip => 1
  | .ret (.call fname _) => callDepth funEnv fname
  | .ret _ => 1
  | .assign (.var _) (.call fname _) => callDepth funEnv fname
  | .assign _ _ => 1
  | .seq s1 s2 => max (stmtDepthFull funEnv s1) (stmtDepthFull funEnv s2) + 1
  | .ite _ th el => max (stmtDepthFull funEnv th) (stmtDepthFull funEnv el) + 1
  | .block _ body => stmtDepthFull funEnv body + 1
  | .switch _ _ _ default => stmtDepthFull funEnv default + 1
  | .forLoop init _ step body =>
      max (stmtDepthFull funEnv init) (max (stmtDepthFull funEnv step) (stmtDepthFull funEnv body)) + 2
  | .break => 1
  | .continue => 1
  | .whileInv _ _ _ => 1
  | .alloc _ _ => 1
  | .free _ _ => 1
  | .decl _ _ => 1

def swhileFuelFull (funEnv : FunEnv) (body : CStmt) (iters : Nat) : Nat :=
  stmtDepthFull funEnv body + iters + 1

theorem stmtDepthFull_ne_zero (funEnv : FunEnv) (body : CStmt) :
    stmtDepthFull funEnv body ≠ 0 := by
  cases body with
  | skip =>
      simp [stmtDepthFull]
  | ret e =>
      cases e with
      | sizeOf ty =>
          simp [stmtDepthFull]
      | cast ty e =>
          simp [stmtDepthFull]
      | intLit n =>
          simp [stmtDepthFull]
      | floatLit v =>
          simp [stmtDepthFull]
      | null =>
          simp [stmtDepthFull]
      | var x =>
          simp [stmtDepthFull]
      | binop op e1 e2 =>
          simp [stmtDepthFull]
      | deref p =>
          simp [stmtDepthFull]
      | arrayAccess arr idx =>
          simp [stmtDepthFull]
      | addrOf x =>
          simp [stmtDepthFull]
      | fieldAccess p field =>
          simp [stmtDepthFull]
      | call fname args =>
          cases hlookup : funEnv fname <;> simp [stmtDepthFull, callDepth, hlookup]
  | assign lhs rhs =>
      cases lhs with
      | var x =>
          cases rhs with
          | sizeOf ty =>
              simp [stmtDepthFull]
          | cast ty e =>
              simp [stmtDepthFull]
          | intLit n =>
              simp [stmtDepthFull]
          | floatLit v =>
              simp [stmtDepthFull]
          | null =>
              simp [stmtDepthFull]
          | var y =>
              simp [stmtDepthFull]
          | binop op e1 e2 =>
              simp [stmtDepthFull]
          | deref p =>
              simp [stmtDepthFull]
          | arrayAccess arr idx =>
              simp [stmtDepthFull]
          | addrOf y =>
              simp [stmtDepthFull]
          | fieldAccess p field =>
              simp [stmtDepthFull]
          | call fname args =>
              cases hlookup : funEnv fname <;> simp [stmtDepthFull, callDepth, hlookup]
      | deref p =>
          cases rhs <;> simp [stmtDepthFull]
      | fieldAccess p field =>
          cases rhs <;> simp [stmtDepthFull]
      | sizeOf ty =>
          cases rhs <;> simp [stmtDepthFull]
      | cast ty e =>
          cases rhs <;> simp [stmtDepthFull]
      | arrayAccess arr idx =>
          cases rhs <;> simp [stmtDepthFull]
      | intLit n =>
          cases rhs <;> simp [stmtDepthFull]
      | floatLit v =>
          cases rhs <;> simp [stmtDepthFull]
      | null =>
          cases rhs <;> simp [stmtDepthFull]
      | binop op e1 e2 =>
          cases rhs <;> simp [stmtDepthFull]
      | addrOf y =>
          cases rhs <;> simp [stmtDepthFull]
      | call fname args =>
          cases rhs <;> simp [stmtDepthFull]
  | seq s1 s2 =>
      simp [stmtDepthFull]
  | ite cond th el =>
      simp [stmtDepthFull]
  | block decls body =>
      simp [stmtDepthFull]
  | switch e tag caseBody default =>
      simp [stmtDepthFull]
  | forLoop init cond step body =>
      simp [stmtDepthFull]
  | «break» =>
      simp [stmtDepthFull]
  | «continue» =>
      simp [stmtDepthFull]
  | whileInv cond inv body =>
      simp [stmtDepthFull]
  | alloc x cells =>
      simp [stmtDepthFull]
  | free e cells =>
      simp [stmtDepthFull]
  | decl x ty =>
      simp [stmtDepthFull]

/-- Statements that must return on every successful execution path. This is
the extra structural hypothesis needed to justify `swpCall`, whose continuation
only talks about postconditions on returned values. -/
def MustReturn : CStmt → Prop
  | .skip => False
  | .ret _ => True
  | .assign _ _ => False
  | .seq s1 s2 => NoReturn s1 ∧ MustReturn s2
  | .ite _ th el => MustReturn th ∧ MustReturn el
  | .block _ body => MustReturn body
  | .switch _ _ _ _ => False
  | .forLoop _ _ _ _ => False
  | .break => False
  | .continue => False
  | .whileInv _ _ _ => False
  | .alloc _ _ => False
  | .free _ _ => False
  | .decl _ _ => False

theorem swp_sound_returned (body : CStmt) (hloop : LoopFree body)
    (htail : TailReturn body) (hret : MustReturn body) :
    ∀ {Q st fuel},
      stmtDepth body ≤ fuel →
      swp body Q st →
      ∃ v st', execStmt fuel body st = some (.returned v st') ∧ Q v st' := by
  intro Q st fuel hfuel hswp
  induction body generalizing Q st fuel with
  | skip =>
      cases hret
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
              refine ⟨v, st, ?_, ?_⟩
              · simp [execStmt, hEval]
              · simpa [swp, hEval] using hswp
  | assign lhs rhs =>
      cases hret
  | seq s1 s2 ih1 ih2 =>
      rcases hloop with ⟨hloop1, hloop2⟩
      rcases htail with ⟨_htail1, htail2, hnr1⟩
      rcases hret with ⟨_hnr1, hret2⟩
      cases fuel with
      | zero =>
          cases (Nat.not_succ_le_zero _ hfuel)
      | succ fuel' =>
          have hmax : max (stmtDepth s1) (stmtDepth s2) ≤ fuel' := by
            simpa [stmtDepth] using hfuel
          have hfuel1 : stmtDepth s1 ≤ fuel' := le_trans (Nat.le_max_left _ _) hmax
          have hfuel2 : stmtDepth s2 ≤ fuel' := le_trans (Nat.le_max_right _ _) hmax
          rcases swp_sound_normal s1 hloop1 hnr1 hfuel1 hswp with ⟨st', hexec1, hmid⟩
          rcases ih2 hloop2 htail2 hret2 hfuel2 hmid with ⟨v, st'', hexec2, hq⟩
          refine ⟨v, st'', ?_, hq⟩
          simp [execStmt, hexec1, hexec2]
  | ite cond th el ihTh ihEl =>
      rcases hloop with ⟨hloopTh, hloopEl⟩
      rcases htail with ⟨htailTh, htailEl⟩
      rcases hret with ⟨hretTh, hretEl⟩
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
                rcases ihTh hloopTh htailTh hretTh hfuelTh hbranch with ⟨ret, st', hexec, hq⟩
                refine ⟨ret, st', ?_, hq⟩
                simp [execStmt, hcond, htruth, hexec]
              ·
                have hbranch : swp el Q st := by
                  simpa [swp, hcond, htruth] using hswp
                rcases ihEl hloopEl htailEl hretEl hfuelEl hbranch with ⟨ret, st', hexec, hq⟩
                refine ⟨ret, st', ?_, hq⟩
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
          rcases ih hloop htail hret hfuelBody hbody with ⟨v, st', hexec, hq⟩
          refine ⟨v, restoreBlockState st st' decls, ?_, hq⟩
          simp [execStmt, hexec]
  | switch e tag caseBody default ihCase ihDefault =>
      cases hret
  | forLoop init cond step body ihInit ihStep ihBody =>
      cases hret
  | «break» =>
      cases hret
  | «continue» =>
      cases hret
  | whileInv cond inv body ih =>
      cases hret
  | alloc x cells =>
      cases hret
  | free e cells =>
      cases hret
  | decl x ty =>
      cases hret

/-- Soundness obligations for callees exposed through `funEnv`. -/
def FunEnvSound (funEnv : FunEnv) : Prop :=
  ∀ fname spec, funEnv fname = some spec →
    LoopFree spec.body ∧ TailReturn spec.body ∧ MustReturn spec.body ∧ sgenVC spec

theorem execCall_sound (funEnv : FunEnv) (henv : FunEnvSound funEnv)
    {fname args Q st fuel} :
    callDepth funEnv fname ≤ fuel + 1 →
    swpCall funEnv fname args Q st →
    ∃ ret st', execCall funEnv fuel fname args st = some (ret, st') ∧ Q ret st' := by
  intro hcallFuel hcall
  rcases swpCall_elim (funEnv := funEnv) (fname := fname) (args := args) (Q := Q) hcall with
    ⟨spec, vals, hlookup, hvals, hlen, hpre, hpost⟩
  rcases henv fname spec hlookup with ⟨hloop, htail, hret, hvc⟩
  have hbodyfuel : stmtDepth spec.body ≤ fuel := by
    have hs : Nat.succ (stmtDepth spec.body) ≤ Nat.succ fuel := by
      simpa [callDepth, hlookup, Nat.add_comm] using hcallFuel
    exact Nat.succ_le_succ_iff.mp hs
  have hbody : swp spec.body spec.post (callEntryState st spec vals) := by
    exact hvc (callEntryState st spec vals) hpre
  rcases swp_sound_returned spec.body hloop htail hret hbodyfuel hbody with
    ⟨ret, callee, hexec, hq⟩
  refine ⟨ret, restoreCallerState st callee, ?_, ?_⟩
  · simp [execCall, hlookup, hvals, hlen, hexec]
  · exact hpost ret callee hq

theorem swpFull_sound_normal (funEnv : FunEnv) (henv : FunEnvSound funEnv)
    (body : CStmt) (hloop : LoopFree body) (hnr : NoReturn body) :
    ∀ {Q st fuel},
      stmtDepthFull funEnv body ≤ fuel →
      swpFull funEnv body Q st →
      ∃ st', execStmtFull funEnv fuel body st = some (.normal st') ∧ Q CVal.undef st' := by
  intro Q st fuel hfuel hswp
  induction body generalizing Q st fuel with
  | skip =>
      cases fuel with
      | zero =>
          cases (Nat.not_succ_le_zero _ hfuel)
      | succ fuel' =>
          exact ⟨st, by simp [execStmtFull], hswp⟩
  | ret e =>
      cases hnr
  | assign lhs rhs =>
      cases fuel with
      | zero =>
          exfalso
          have h0 : stmtDepthFull funEnv (.assign lhs rhs) = 0 := Nat.eq_zero_of_le_zero hfuel
          exact (stmtDepthFull_ne_zero funEnv (.assign lhs rhs)) h0
      | succ fuel' =>
          cases lhs with
          | var x =>
              cases rhs with
              | call fname args =>
                  have hcallFuel : callDepth funEnv fname ≤ fuel' + 1 := by
                    simpa [stmtDepthFull] using hfuel
                  rcases execCall_sound (funEnv := funEnv) henv hcallFuel hswp with
                    ⟨ret, st', hExecCall, hq⟩
                  refine ⟨st'.updateVar x ret, ?_, hq⟩
                  simp [execStmtFull, hExecCall]
              | sizeOf ty =>
                  have hswp' : swp (.assign (.var x) (.sizeOf ty)) Q st := by
                    simpa [swpFull, swp] using hswp
                  rcases swp_sound_normal (.assign (.var x) (.sizeOf ty))
                      (by simp [LoopFree]) (by simp [NoReturn]) (fuel := fuel' + 1)
                      (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                    ⟨st', hexec, hq⟩
                  exact ⟨st', by simpa [execStmtFull, execStmt] using hexec, hq⟩
              | cast ty e =>
                  have hswp' : swp (.assign (.var x) (.cast ty e)) Q st := by
                    simpa [swpFull, swp] using hswp
                  rcases swp_sound_normal (.assign (.var x) (.cast ty e))
                      (by simp [LoopFree]) (by simp [NoReturn]) (fuel := fuel' + 1)
                      (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                    ⟨st', hexec, hq⟩
                  exact ⟨st', by simpa [execStmtFull, execStmt] using hexec, hq⟩
              | intLit n =>
                  have hswp' : swp (.assign (.var x) (.intLit n)) Q st := by
                    simpa [swpFull, swp] using hswp
                  rcases swp_sound_normal (.assign (.var x) (.intLit n))
                      (by simp [LoopFree]) (by simp [NoReturn]) (fuel := fuel' + 1)
                      (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                    ⟨st', hexec, hq⟩
                  exact ⟨st', by simpa [execStmtFull, execStmt] using hexec, hq⟩
              | floatLit v =>
                  have hswp' : swp (.assign (.var x) (.floatLit v)) Q st := by
                    simpa [swpFull, swp] using hswp
                  rcases swp_sound_normal (.assign (.var x) (.floatLit v))
                      (by simp [LoopFree]) (by simp [NoReturn]) (fuel := fuel' + 1)
                      (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                    ⟨st', hexec, hq⟩
                  exact ⟨st', by simpa [execStmtFull, execStmt] using hexec, hq⟩
              | null =>
                  have hswp' : swp (.assign (.var x) .null) Q st := by
                    simpa [swpFull, swp] using hswp
                  rcases swp_sound_normal (.assign (.var x) .null)
                      (by simp [LoopFree]) (by simp [NoReturn]) (fuel := fuel' + 1)
                      (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                    ⟨st', hexec, hq⟩
                  exact ⟨st', by simpa [execStmtFull, execStmt] using hexec, hq⟩
              | var y =>
                  have hswp' : swp (.assign (.var x) (.var y)) Q st := by
                    simpa [swpFull, swp] using hswp
                  rcases swp_sound_normal (.assign (.var x) (.var y))
                      (by simp [LoopFree]) (by simp [NoReturn]) (fuel := fuel' + 1)
                      (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                    ⟨st', hexec, hq⟩
                  exact ⟨st', by simpa [execStmtFull, execStmt] using hexec, hq⟩
              | binop op e1 e2 =>
                  have hswp' : swp (.assign (.var x) (.binop op e1 e2)) Q st := by
                    simpa [swpFull, swp] using hswp
                  rcases swp_sound_normal (.assign (.var x) (.binop op e1 e2))
                      (by simp [LoopFree]) (by simp [NoReturn]) (fuel := fuel' + 1)
                      (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                    ⟨st', hexec, hq⟩
                  exact ⟨st', by simpa [execStmtFull, execStmt] using hexec, hq⟩
              | deref p =>
                  have hswp' : swp (.assign (.var x) (.deref p)) Q st := by
                    simpa [swpFull, swp] using hswp
                  rcases swp_sound_normal (.assign (.var x) (.deref p))
                      (by simp [LoopFree]) (by simp [NoReturn]) (fuel := fuel' + 1)
                      (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                    ⟨st', hexec, hq⟩
                  exact ⟨st', by simpa [execStmtFull, execStmt] using hexec, hq⟩
              | arrayAccess arr idx =>
                  have hswp' : swp (.assign (.var x) (.arrayAccess arr idx)) Q st := by
                    simpa [swpFull, swp] using hswp
                  rcases swp_sound_normal (.assign (.var x) (.arrayAccess arr idx))
                      (by simp [LoopFree]) (by simp [NoReturn]) (fuel := fuel' + 1)
                      (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                    ⟨st', hexec, hq⟩
                  exact ⟨st', by simpa [execStmtFull, execStmt] using hexec, hq⟩
              | addrOf y =>
                  have hswp' : swp (.assign (.var x) (.addrOf y)) Q st := by
                    simpa [swpFull, swp] using hswp
                  rcases swp_sound_normal (.assign (.var x) (.addrOf y))
                      (by simp [LoopFree]) (by simp [NoReturn]) (fuel := fuel' + 1)
                      (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                    ⟨st', hexec, hq⟩
                  exact ⟨st', by simpa [execStmtFull, execStmt] using hexec, hq⟩
              | fieldAccess p field =>
                  have hswp' : swp (.assign (.var x) (.fieldAccess p field)) Q st := by
                    simpa [swpFull, swp] using hswp
                  rcases swp_sound_normal (.assign (.var x) (.fieldAccess p field))
                      (by simp [LoopFree]) (by simp [NoReturn]) (fuel := fuel' + 1)
                      (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                    ⟨st', hexec, hq⟩
                  exact ⟨st', by simpa [execStmtFull, execStmt] using hexec, hq⟩
          | deref p =>
              have hswp' : swp (.assign (.deref p) rhs) Q st := by
                simpa [swpFull, swp] using hswp
              rcases swp_sound_normal (.assign (.deref p) rhs)
                  (by simp [LoopFree]) (by simp [NoReturn]) (fuel := fuel' + 1)
                  (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                ⟨st', hexec, hq⟩
              exact ⟨st', by simpa [execStmtFull, execStmt] using hexec, hq⟩
          | fieldAccess p field =>
              have hswp' : swp (.assign (.fieldAccess p field) rhs) Q st := by
                simpa [swpFull, swp] using hswp
              rcases swp_sound_normal (.assign (.fieldAccess p field) rhs)
                  (by simp [LoopFree]) (by simp [NoReturn]) (fuel := fuel' + 1)
                  (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                ⟨st', hexec, hq⟩
              exact ⟨st', by simpa [execStmtFull, execStmt] using hexec, hq⟩
          | sizeOf ty =>
              have hswp' : swp (.assign (.sizeOf ty) rhs) Q st := by
                simpa [swpFull, swp] using hswp
              rcases swp_sound_normal (.assign (.sizeOf ty) rhs)
                  (by simp [LoopFree]) (by simp [NoReturn]) (fuel := fuel' + 1)
                  (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                ⟨st', hexec, hq⟩
              exact ⟨st', by simpa [execStmtFull, execStmt] using hexec, hq⟩
          | cast ty e =>
              have hswp' : swp (.assign (.cast ty e) rhs) Q st := by
                simpa [swpFull, swp] using hswp
              rcases swp_sound_normal (.assign (.cast ty e) rhs)
                  (by simp [LoopFree]) (by simp [NoReturn]) (fuel := fuel' + 1)
                  (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                ⟨st', hexec, hq⟩
              exact ⟨st', by simpa [execStmtFull, execStmt] using hexec, hq⟩
          | arrayAccess arr idx =>
              have hswp' : swp (.assign (.arrayAccess arr idx) rhs) Q st := by
                simpa [swpFull, swp] using hswp
              rcases swp_sound_normal (.assign (.arrayAccess arr idx) rhs)
                  (by simp [LoopFree]) (by simp [NoReturn]) (fuel := fuel' + 1)
                  (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                ⟨st', hexec, hq⟩
              exact ⟨st', by simpa [execStmtFull, execStmt] using hexec, hq⟩
          | intLit n =>
              have hswp' : swp (.assign (.intLit n) rhs) Q st := by
                simpa [swpFull, swp] using hswp
              rcases swp_sound_normal (.assign (.intLit n) rhs)
                  (by simp [LoopFree]) (by simp [NoReturn]) (fuel := fuel' + 1)
                  (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                ⟨st', hexec, hq⟩
              exact ⟨st', by simpa [execStmtFull, execStmt] using hexec, hq⟩
          | floatLit v =>
              have hswp' : swp (.assign (.floatLit v) rhs) Q st := by
                simpa [swpFull, swp] using hswp
              rcases swp_sound_normal (.assign (.floatLit v) rhs)
                  (by simp [LoopFree]) (by simp [NoReturn]) (fuel := fuel' + 1)
                  (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                ⟨st', hexec, hq⟩
              exact ⟨st', by simpa [execStmtFull, execStmt] using hexec, hq⟩
          | null =>
              have hswp' : swp (.assign .null rhs) Q st := by
                simpa [swpFull, swp] using hswp
              rcases swp_sound_normal (.assign .null rhs)
                  (by simp [LoopFree]) (by simp [NoReturn]) (fuel := fuel' + 1)
                  (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                ⟨st', hexec, hq⟩
              exact ⟨st', by simpa [execStmtFull, execStmt] using hexec, hq⟩
          | binop op e1 e2 =>
              have hswp' : swp (.assign (.binop op e1 e2) rhs) Q st := by
                simpa [swpFull, swp] using hswp
              rcases swp_sound_normal (.assign (.binop op e1 e2) rhs)
                  (by simp [LoopFree]) (by simp [NoReturn]) (fuel := fuel' + 1)
                  (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                ⟨st', hexec, hq⟩
              exact ⟨st', by simpa [execStmtFull, execStmt] using hexec, hq⟩
          | addrOf y =>
              have hswp' : swp (.assign (.addrOf y) rhs) Q st := by
                simpa [swpFull, swp] using hswp
              rcases swp_sound_normal (.assign (.addrOf y) rhs)
                  (by simp [LoopFree]) (by simp [NoReturn]) (fuel := fuel' + 1)
                  (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                ⟨st', hexec, hq⟩
              exact ⟨st', by simpa [execStmtFull, execStmt] using hexec, hq⟩
          | call fname args =>
              have hswp' : swp (.assign (.call fname args) rhs) Q st := by
                simpa [swpFull, swp] using hswp
              rcases swp_sound_normal (.assign (.call fname args) rhs)
                  (by simp [LoopFree]) (by simp [NoReturn]) (fuel := fuel' + 1)
                  (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                ⟨st', hexec, hq⟩
              exact ⟨st', by simpa [execStmtFull, execStmt] using hexec, hq⟩
  | seq s1 s2 ih1 ih2 =>
      rcases hloop with ⟨hloop1, hloop2⟩
      rcases hnr with ⟨hnr1, hnr2⟩
      cases fuel with
      | zero =>
          cases (Nat.not_succ_le_zero _ hfuel)
      | succ fuel' =>
          have hmax : max (stmtDepthFull funEnv s1) (stmtDepthFull funEnv s2) ≤ fuel' := by
            simpa [stmtDepthFull] using hfuel
          have hfuel1 : stmtDepthFull funEnv s1 ≤ fuel' := le_trans (Nat.le_max_left _ _) hmax
          have hfuel2 : stmtDepthFull funEnv s2 ≤ fuel' := le_trans (Nat.le_max_right _ _) hmax
          rcases ih1 hloop1 hnr1 hfuel1 hswp with ⟨st', hexec1, hmid⟩
          rcases ih2 hloop2 hnr2 hfuel2 hmid with ⟨st'', hexec2, hq⟩
          refine ⟨st'', ?_, hq⟩
          simp [execStmtFull, hexec1, hexec2]
  | ite cond th el ihTh ihEl =>
      rcases hloop with ⟨hloopTh, hloopEl⟩
      rcases hnr with ⟨hnrTh, hnrEl⟩
      cases fuel with
      | zero =>
          cases (Nat.not_succ_le_zero _ hfuel)
      | succ fuel' =>
          have hmax : max (stmtDepthFull funEnv th) (stmtDepthFull funEnv el) ≤ fuel' := by
            simpa [stmtDepthFull] using hfuel
          have hfuelTh : stmtDepthFull funEnv th ≤ fuel' := le_trans (Nat.le_max_left _ _) hmax
          have hfuelEl : stmtDepthFull funEnv el ≤ fuel' := le_trans (Nat.le_max_right _ _) hmax
          cases hcond : evalExpr cond st with
          | none =>
              have : False := by simpa [swpFull, hcond] using hswp
              cases this
          | some v =>
              by_cases htruth : isTruthy v = true
              ·
                have hbranch : swpFull funEnv th Q st := by
                  simpa [swpFull, hcond, htruth] using hswp
                rcases ihTh hloopTh hnrTh hfuelTh hbranch with ⟨st', hexec, hq⟩
                refine ⟨st', ?_, hq⟩
                simp [execStmtFull, hcond, htruth, hexec]
              ·
                have hbranch : swpFull funEnv el Q st := by
                  simpa [swpFull, hcond, htruth] using hswp
                rcases ihEl hloopEl hnrEl hfuelEl hbranch with ⟨st', hexec, hq⟩
                refine ⟨st', ?_, hq⟩
                simp [execStmtFull, hcond, htruth, hexec]
  | block decls body ih =>
      cases fuel with
      | zero =>
          cases (Nat.not_succ_le_zero _ hfuel)
      | succ fuel' =>
          have hfuelBody : stmtDepthFull funEnv body ≤ fuel' := by
            simpa [stmtDepthFull] using hfuel
          have hbody :
              swpFull funEnv body (fun ret st' => Q ret (restoreBlockState st st' decls))
                (enterBlockState st decls) := by
            simpa [swpFull] using hswp
          rcases ih hloop hnr hfuelBody hbody with ⟨st', hexec, hq⟩
          refine ⟨restoreBlockState st st' decls, ?_, hq⟩
          simp [execStmtFull, hexec]
  | switch e tag caseBody default ihCase ihDefault =>
      cases hloop
  | forLoop init cond step body ihInit ihStep ihBody =>
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
          exact ⟨st', by simp [st', execStmtFull], hswp⟩
  | free e cells =>
      cases fuel with
      | zero =>
          cases (Nat.not_succ_le_zero _ hfuel)
      | succ fuel' =>
          cases hEval : evalExpr e st with
          | none =>
              have : False := by simpa [swpFull, hEval] using hswp
              cases this
          | some v =>
              cases v with
              | int n =>
                  have : False := by simpa [swpFull, hEval] using hswp
                  cases this
              | uint n sz =>
                  have : False := by simpa [swpFull, hEval] using hswp
                  cases this
              | null =>
                  have : False := by simpa [swpFull, hEval] using hswp
                  cases this
              | undef =>
                  have : False := by simpa [swpFull, hEval] using hswp
                  cases this
              | structVal fields =>
                  have : False := by simpa [swpFull, hEval] using hswp
                  cases this
              | unionVal tag v' =>
                  have : False := by simpa [swpFull, hEval] using hswp
                  cases this
              | float v' =>
                  have : False := by simpa [swpFull, hEval] using hswp
                  cases this
              | ptr block offset =>
                  let addr : PtrVal := { block := block, offset := offset }
                  rcases (show ∃ flatAddr, st.resolvePtr addr = some flatAddr ∧ Q CVal.undef (st.freeCells flatAddr cells) by
                    simpa [swpFull, hEval] using hswp) with ⟨flatAddr, hresolve, hq⟩
                  refine ⟨st.freeCells flatAddr cells, ?_, hq⟩
                  simp [execStmtFull, hEval, addr, hresolve, CState.freeCells]
  | decl x ty =>
      cases fuel with
      | zero =>
          cases (Nat.not_succ_le_zero _ hfuel)
      | succ fuel' =>
          exact ⟨st.updateVar x CVal.undef, by simp [execStmtFull], hswp⟩

theorem swpFull_sound (funEnv : FunEnv) (henv : FunEnvSound funEnv)
    (body : CStmt) (hloop : LoopFree body) (htail : TailReturn body)
    {Q st fuel} :
    stmtDepthFull funEnv body ≤ fuel →
    swpFull funEnv body Q st →
    ∃ res, execStmtFull funEnv fuel body st = some res ∧
      match res with
      | .returned v st' => Q v st'
      | .normal st' => Q CVal.undef st' := by
  intro hfuel hswp
  induction body generalizing Q st fuel with
  | skip =>
      rcases swpFull_sound_normal funEnv henv .skip (by simp [LoopFree]) (by simp [NoReturn]) hfuel hswp with
        ⟨st', hexec, hq⟩
      exact ⟨.normal st', hexec, hq⟩
  | ret e =>
      cases fuel with
      | zero =>
          exfalso
          have h0 : stmtDepthFull funEnv (.ret e) = 0 := Nat.eq_zero_of_le_zero hfuel
          exact (stmtDepthFull_ne_zero funEnv (.ret e)) h0
      | succ fuel' =>
          cases e with
          | sizeOf ty =>
              have hswp' : swp (.ret (.sizeOf ty)) Q st := by
                simpa [swpFull, swp] using hswp
              rcases swp_sound (.ret (.sizeOf ty)) (by simp [LoopFree]) (by simp [TailReturn])
                  (fuel := fuel' + 1) (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                ⟨res, hexec, hq⟩
              exact ⟨res, by simpa [execStmtFull, execStmt] using hexec, hq⟩
          | cast ty e =>
              have hswp' : swp (.ret (.cast ty e)) Q st := by
                simpa [swpFull, swp] using hswp
              rcases swp_sound (.ret (.cast ty e)) (by simp [LoopFree]) (by simp [TailReturn])
                  (fuel := fuel' + 1) (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                ⟨res, hexec, hq⟩
              exact ⟨res, by simpa [execStmtFull, execStmt] using hexec, hq⟩
          | call fname args =>
              have hcallFuel : callDepth funEnv fname ≤ fuel' + 1 := by
                simpa [stmtDepthFull] using hfuel
              rcases execCall_sound (funEnv := funEnv) henv hcallFuel hswp with
                ⟨ret, st', hExecCall, hq⟩
              exact ⟨.returned ret st', by simp [execStmtFull, hExecCall], hq⟩
          | intLit n =>
              have hswp' : swp (.ret (.intLit n)) Q st := by
                simpa [swpFull, swp] using hswp
              rcases swp_sound (.ret (.intLit n)) (by simp [LoopFree]) (by simp [TailReturn])
                  (fuel := fuel' + 1) (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                ⟨res, hexec, hq⟩
              exact ⟨res, by simpa [execStmtFull, execStmt] using hexec, hq⟩
          | floatLit v =>
              have hswp' : swp (.ret (.floatLit v)) Q st := by
                simpa [swpFull, swp] using hswp
              rcases swp_sound (.ret (.floatLit v)) (by simp [LoopFree]) (by simp [TailReturn])
                  (fuel := fuel' + 1) (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                ⟨res, hexec, hq⟩
              exact ⟨res, by simpa [execStmtFull, execStmt] using hexec, hq⟩
          | null =>
              have hswp' : swp (.ret .null) Q st := by
                simpa [swpFull, swp] using hswp
              rcases swp_sound (.ret .null) (by simp [LoopFree]) (by simp [TailReturn])
                  (fuel := fuel' + 1) (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                ⟨res, hexec, hq⟩
              exact ⟨res, by simpa [execStmtFull, execStmt] using hexec, hq⟩
          | var x =>
              have hswp' : swp (.ret (.var x)) Q st := by
                simpa [swpFull, swp] using hswp
              rcases swp_sound (.ret (.var x)) (by simp [LoopFree]) (by simp [TailReturn])
                  (fuel := fuel' + 1) (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                ⟨res, hexec, hq⟩
              exact ⟨res, by simpa [execStmtFull, execStmt] using hexec, hq⟩
          | binop op e1 e2 =>
              have hswp' : swp (.ret (.binop op e1 e2)) Q st := by
                simpa [swpFull, swp] using hswp
              rcases swp_sound (.ret (.binop op e1 e2)) (by simp [LoopFree]) (by simp [TailReturn])
                  (fuel := fuel' + 1) (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                ⟨res, hexec, hq⟩
              exact ⟨res, by simpa [execStmtFull, execStmt] using hexec, hq⟩
          | deref p =>
              have hswp' : swp (.ret (.deref p)) Q st := by
                simpa [swpFull, swp] using hswp
              rcases swp_sound (.ret (.deref p)) (by simp [LoopFree]) (by simp [TailReturn])
                  (fuel := fuel' + 1) (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                ⟨res, hexec, hq⟩
              exact ⟨res, by simpa [execStmtFull, execStmt] using hexec, hq⟩
          | arrayAccess arr idx =>
              have hswp' : swp (.ret (.arrayAccess arr idx)) Q st := by
                simpa [swpFull, swp] using hswp
              rcases swp_sound (.ret (.arrayAccess arr idx)) (by simp [LoopFree]) (by simp [TailReturn])
                  (fuel := fuel' + 1) (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                ⟨res, hexec, hq⟩
              exact ⟨res, by simpa [execStmtFull, execStmt] using hexec, hq⟩
          | addrOf x =>
              have hswp' : swp (.ret (.addrOf x)) Q st := by
                simpa [swpFull, swp] using hswp
              rcases swp_sound (.ret (.addrOf x)) (by simp [LoopFree]) (by simp [TailReturn])
                  (fuel := fuel' + 1) (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                ⟨res, hexec, hq⟩
              exact ⟨res, by simpa [execStmtFull, execStmt] using hexec, hq⟩
          | fieldAccess p field =>
              have hswp' : swp (.ret (.fieldAccess p field)) Q st := by
                simpa [swpFull, swp] using hswp
              rcases swp_sound (.ret (.fieldAccess p field)) (by simp [LoopFree]) (by simp [TailReturn])
                  (fuel := fuel' + 1) (Q := Q) (st := st) (by simp [stmtDepth]) hswp' with
                ⟨res, hexec, hq⟩
              exact ⟨res, by simpa [execStmtFull, execStmt] using hexec, hq⟩
  | assign lhs rhs =>
      have hnr : NoReturn (.assign lhs rhs) := by simp [NoReturn]
      rcases swpFull_sound_normal funEnv henv (.assign lhs rhs) hloop hnr hfuel hswp with
        ⟨st', hexec, hq⟩
      exact ⟨.normal st', hexec, hq⟩
  | seq s1 s2 ih1 ih2 =>
      rcases hloop with ⟨hloop1, hloop2⟩
      rcases htail with ⟨_htail1, htail2, hnr1⟩
      have hnr1' : NoReturn s1 := hnr1
      cases fuel with
      | zero =>
          cases (Nat.not_succ_le_zero _ hfuel)
      | succ fuel' =>
          have hmax : max (stmtDepthFull funEnv s1) (stmtDepthFull funEnv s2) ≤ fuel' := by
            simpa [stmtDepthFull] using hfuel
          have hfuel1 : stmtDepthFull funEnv s1 ≤ fuel' := le_trans (Nat.le_max_left _ _) hmax
          have hfuel2 : stmtDepthFull funEnv s2 ≤ fuel' := le_trans (Nat.le_max_right _ _) hmax
          rcases swpFull_sound_normal funEnv henv s1 hloop1 hnr1' hfuel1 hswp with
            ⟨st', hexec1, hmid⟩
          rcases ih2 hloop2 htail2 hfuel2 hmid with ⟨res, hexec2, hq⟩
          refine ⟨res, ?_, hq⟩
          simp [execStmtFull, hexec1, hexec2]
  | ite cond th el ihTh ihEl =>
      rcases hloop with ⟨hloopTh, hloopEl⟩
      rcases htail with ⟨htailTh, htailEl⟩
      cases fuel with
      | zero =>
          cases (Nat.not_succ_le_zero _ hfuel)
      | succ fuel' =>
          have hmax : max (stmtDepthFull funEnv th) (stmtDepthFull funEnv el) ≤ fuel' := by
            simpa [stmtDepthFull] using hfuel
          have hfuelTh : stmtDepthFull funEnv th ≤ fuel' := le_trans (Nat.le_max_left _ _) hmax
          have hfuelEl : stmtDepthFull funEnv el ≤ fuel' := le_trans (Nat.le_max_right _ _) hmax
          cases hcond : evalExpr cond st with
          | none =>
              have : False := by simpa [swpFull, hcond] using hswp
              cases this
          | some v =>
              by_cases htruth : isTruthy v = true
              ·
                have hbranch : swpFull funEnv th Q st := by
                  simpa [swpFull, hcond, htruth] using hswp
                rcases ihTh hloopTh htailTh hfuelTh hbranch with ⟨res, hexec, hq⟩
                refine ⟨res, ?_, hq⟩
                simp [execStmtFull, hcond, htruth, hexec]
              ·
                have hbranch : swpFull funEnv el Q st := by
                  simpa [swpFull, hcond, htruth] using hswp
                rcases ihEl hloopEl htailEl hfuelEl hbranch with ⟨res, hexec, hq⟩
                refine ⟨res, ?_, hq⟩
                simp [execStmtFull, hcond, htruth, hexec]
  | block decls body ih =>
      cases fuel with
      | zero =>
          cases (Nat.not_succ_le_zero _ hfuel)
      | succ fuel' =>
          have hfuelBody : stmtDepthFull funEnv body ≤ fuel' := by
            simpa [stmtDepthFull] using hfuel
          have hbody :
              swpFull funEnv body (fun ret st' => Q ret (restoreBlockState st st' decls))
                (enterBlockState st decls) := by
            simpa [swpFull] using hswp
          rcases ih hloop htail hfuelBody hbody with ⟨res, hexec, hq⟩
          cases res with
          | normal st' =>
              refine ⟨.normal (restoreBlockState st st' decls), ?_, hq⟩
              simp [execStmtFull, hexec]
          | returned v st' =>
              refine ⟨.returned v (restoreBlockState st st' decls), ?_, hq⟩
              simp [execStmtFull, hexec]
  | switch e tag caseBody default ihCase ihDefault =>
      cases hloop
  | forLoop init cond step body ihInit ihStep ihBody =>
      cases hloop
  | «break» =>
      cases hloop
  | «continue» =>
      cases hloop
  | whileInv cond inv body ih =>
      cases hloop
  | alloc x cells =>
      have hnr : NoReturn (.alloc x cells) := by simp [NoReturn]
      rcases swpFull_sound_normal funEnv henv (.alloc x cells) hloop hnr hfuel hswp with
        ⟨st', hexec, hq⟩
      exact ⟨.normal st', hexec, hq⟩
  | free e cells =>
      have hnr : NoReturn (.free e cells) := by simp [NoReturn]
      rcases swpFull_sound_normal funEnv henv (.free e cells) hloop hnr hfuel hswp with
        ⟨st', hexec, hq⟩
      exact ⟨.normal st', hexec, hq⟩
  | decl x ty =>
      have hnr : NoReturn (.decl x ty) := by simp [NoReturn]
      rcases swpFull_sound_normal funEnv henv (.decl x ty) hloop hnr hfuel hswp with
        ⟨st', hexec, hq⟩
      exact ⟨.normal st', hexec, hq⟩

theorem swhileWPFull_sound (funEnv : FunEnv) (henv : FunEnvSound funEnv)
    (cond : CExpr) (inv : SProp) (ann : HProp) (body : CStmt)
    (hloop : LoopFree body) (hnr : NoReturn body) :
    ∀ {iters Q st},
      swhileWPFull funEnv iters cond inv body Q st →
      ∃ st', execStmtFull funEnv (swhileFuelFull funEnv body iters) (.whileInv cond ann body) st =
        some (.normal st') ∧ Q CVal.undef st' := by
  intro iters
  induction iters with
  | zero =>
      intro Q st hwp
      rcases hwp with ⟨_hinv, hstep⟩
      cases hcond : evalExpr cond st with
      | none =>
          simp [hcond] at hstep
      | some v =>
          cases htruth : isTruthy v with
          | true =>
              simp [hcond, htruth] at hstep
          | false =>
              refine ⟨st, ?_, ?_⟩
              · change execStmtFull funEnv (Nat.succ (stmtDepthFull funEnv body)) (.whileInv cond ann body) st =
                  some (.normal st)
                simp [execStmtFull, hcond, htruth]
              · simpa [swhileWPFull, hcond, htruth] using hstep
  | succ iters ih =>
      intro Q st hwp
      rcases hwp with ⟨_hinv, hstep⟩
      cases hcond : evalExpr cond st with
      | none =>
          simp [hcond] at hstep
      | some v =>
          cases htruth : isTruthy v with
          | true =>
              have hbody : swpFull funEnv body (fun _ => swhileWPFull funEnv iters cond inv body Q) st := by
                simpa [swhileWPFull, hcond, htruth] using hstep
              have hfuel :
                  stmtDepthFull funEnv body ≤ stmtDepthFull funEnv body + iters + 1 := by
                calc
                  stmtDepthFull funEnv body ≤ stmtDepthFull funEnv body + (iters + 1) := Nat.le_add_right _ _
                  _ = stmtDepthFull funEnv body + iters + 1 := by simp [Nat.add_assoc]
              rcases swpFull_sound_normal funEnv henv body hloop hnr hfuel hbody with
                ⟨st', hexecBody, hcont⟩
              rcases ih hcont with ⟨st'', hexecLoop, hq⟩
              refine ⟨st'', ?_, hq⟩
              change execStmtFull funEnv (Nat.succ (stmtDepthFull funEnv body + iters + 1))
                  (.whileInv cond ann body) st = some (.normal st'')
              simp [execStmtFull, hcond, htruth, hexecBody]
              simpa [swhileFuelFull, execStmtFull, Nat.add_assoc] using hexecLoop
          | false =>
              refine ⟨st, ?_, ?_⟩
              · change execStmtFull funEnv (Nat.succ (stmtDepthFull funEnv body + iters + 1))
                  (.whileInv cond ann body) st = some (.normal st)
                simp [execStmtFull, hcond, htruth]
              · simpa [swhileWPFull, hcond, htruth] using hstep

/-- Soundness for `swpFullMemPost` on normal completion. -/
theorem swpFull_sound_normal_memPost (funEnv : FunEnv) (henv : FunEnvSound funEnv)
    (body : CStmt) (hloop : LoopFree body) (hnr : NoReturn body) :
    ∀ {Q st fuel},
      stmtDepthFull funEnv body ≤ fuel →
      swpFullMemPost funEnv body Q st →
      ∃ st', execStmtFull funEnv fuel body st = some (.normal st') ∧
        Q CVal.undef (heapToMem st'.heap) := by
  intro Q st fuel hfuel hswp
  rcases swpFull_sound_normal funEnv henv body hloop hnr
      (Q := fun v => SProp.ofMemHProp (Q v)) hfuel hswp with ⟨st', hexec, hq⟩
  exact ⟨st', hexec, hq⟩

/-- Soundness for `swpFullMemPost`, transporting the existing tail-return
theorem onto Mem-valued postconditions. -/
theorem swpFull_sound_memPost (funEnv : FunEnv) (henv : FunEnvSound funEnv)
    (body : CStmt) (hloop : LoopFree body) (htail : TailReturn body) :
    ∀ {Q st fuel},
      stmtDepthFull funEnv body ≤ fuel →
      swpFullMemPost funEnv body Q st →
      ∃ res, execStmtFull funEnv fuel body st = some res ∧
        match res with
        | .returned v st' => Q v (heapToMem st'.heap)
        | .normal st' => Q CVal.undef (heapToMem st'.heap) := by
  intro Q st fuel hfuel hswp
  rcases swpFull_sound funEnv henv body hloop htail
      (Q := fun v => SProp.ofMemHProp (Q v)) hfuel hswp with ⟨res, hexec, hq⟩
  exact ⟨res, hexec, hq⟩

/-- Soundness for `swhileWPFull` specialized to Mem-valued postconditions. -/
theorem swhileWPFull_sound_memPost (funEnv : FunEnv) (henv : FunEnvSound funEnv)
    (cond : CExpr) (inv : SProp) (ann : HProp) (body : CStmt)
    (hloop : LoopFree body) (hnr : NoReturn body) :
    ∀ {iters} {Q : CVal → MemHProp} {st},
      swhileWPFull funEnv iters cond inv body (fun v => SProp.ofMemHProp (Q v)) st →
      ∃ st', execStmtFull funEnv (swhileFuelFull funEnv body iters) (.whileInv cond ann body) st =
        some (.normal st') ∧ Q CVal.undef (heapToMem st'.heap) := by
  intro iters Q st hwp
  rcases swhileWPFull_sound funEnv henv cond inv ann body hloop hnr hwp with
    ⟨st', hexec, hq⟩
  exact ⟨st', hexec, hq⟩

end HeytingLean.LeanCP
