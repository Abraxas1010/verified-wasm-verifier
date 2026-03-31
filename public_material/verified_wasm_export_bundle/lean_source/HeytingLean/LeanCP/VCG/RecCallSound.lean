import HeytingLean.LeanCP.VCG.SWPCallSound

/-!
# LeanCP Recursive Call Soundness

`SWPCallSound` closes the honest non-recursive call fragment: direct callees are
executed with the base `execStmt` semantics, so recursive bodies are out of
scope there by construction.

This module adds a separate recursive operational layer:

- `execCallRec` / `execStmtRec` execute call sites by mutual recursion
- `FunEnvSoundRec` packages a termination measure together with per-function
  recursive execution soundness
- `execCall_rec_sound` connects `swpCall` to the recursive operational layer

The key design choice is to keep `swpCall` / `swpFull` unchanged. Recursive
soundness is a stronger contract on the function environment, not a rebranding
of the old non-recursive semantics.
-/

namespace HeytingLean.LeanCP

/-- Termination measure used to justify recursive calls. -/
structure TermMeasure where
  measure : String → CState → Nat

/-- Statements whose operational clauses avoid the direct-call extensions of
`execStmtFull` / `execStmtRec`. On this fragment the two semantics should agree
definitionally up to recursive unfolding. -/
def NoDirectCalls : CStmt → Prop
  | .skip => True
  | .ret (.call _ _) => False
  | .ret _ => True
  | .assign (.var _) (.call _ _) => False
  | .assign _ _ => True
  | .seq s1 s2 => NoDirectCalls s1 ∧ NoDirectCalls s2
  | .ite _ th el => NoDirectCalls th ∧ NoDirectCalls el
  | .block _ body => NoDirectCalls body
  | .switch _ _ _ _ => False
  | .forLoop _ _ _ _ => False
  | .break => False
  | .continue => False
  | .whileInv _ _ body => NoDirectCalls body
  | .alloc _ _ => True
  | .free _ _ => True
  | .decl _ _ => True

mutual

/-- Execute a supported call, allowing recursive callees through `execStmtRec`. -/
def execCallRec (funEnv : FunEnv) : Nat → String → List CExpr → CState → Option (CVal × CState)
  | 0, _, _, _ => none
  | fuel + 1, fname, args, caller => do
      let spec ← funEnv fname
      let vals ← evalArgs args caller
      if _hlen : vals.length = spec.params.length then
        let entry := callEntryState caller spec vals
        match ← execStmtRec funEnv fuel spec.body entry with
        | .returned ret callee =>
            some (ret, restoreCallerState caller callee)
        | .normal callee =>
            some (.undef, restoreCallerState caller callee)
      else
        none
termination_by fuel _ _ _ => fuel

/-- Call-aware big-step semantics with recursive calls enabled. -/
def execStmtRec (funEnv : FunEnv) : Nat → CStmt → CState → Option ExecResult
  | 0, _, _ => none
  | _, .skip, st => some (.normal st)
  | fuel + 1, .ret (.call fname args), st => do
      let (ret, st') ← execCallRec funEnv fuel fname args st
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
      match ← execStmtRec funEnv fuel body entry with
      | .normal st' => some (.normal (restoreBlockState st st' decls))
      | .returned v st' => some (.returned v (restoreBlockState st st' decls))
  | fuel + 1, .switch e tag caseBody default, st => do
      let v ← evalExpr e st
      match v with
      | .int n => if n = tag then execStmtRec funEnv fuel caseBody st else execStmtRec funEnv fuel default st
      | _ => none
  | fuel + 1, .forLoop init cond step body, st =>
      execStmtRec funEnv fuel (desugarFor init cond step body) st
  | _, .break, _ => none
  | _, .continue, _ => none
  | fuel + 1, .assign (.var x) (.call fname args), st => do
      let (ret, st') ← execCallRec funEnv fuel fname args st
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
      match ← execStmtRec funEnv fuel s1 st with
      | .normal st' => execStmtRec funEnv fuel s2 st'
      | .returned v st' => some (.returned v st')
  | fuel + 1, .ite cond th el, st => do
      let v ← evalExpr cond st
      if isTruthy v then execStmtRec funEnv fuel th st
      else execStmtRec funEnv fuel el st
  | fuel + 1, .whileInv cond inv body, st => do
      let v ← evalExpr cond st
      if isTruthy v then
        match ← execStmtRec funEnv fuel body st with
        | .normal st' => execStmtRec funEnv fuel (.whileInv cond inv body) st'
        | .returned v' st' => some (.returned v' st')
      else
        some (.normal st)
termination_by fuel _ _ => fuel

end

/-- On the loop-free, no-direct-call fragment, the recursive operational layer
agrees with `execStmtFull`. This is the shared fragment that both Phase 2 and
Phase 3 already rely on operationally. -/
theorem execStmtRec_agrees_execStmtFull_loopFree (funEnv : FunEnv) :
    ∀ fuel stmt st, LoopFree stmt → NoDirectCalls stmt →
      execStmtRec funEnv fuel stmt st = execStmtFull funEnv fuel stmt st := by
  intro fuel
  induction fuel with
  | zero =>
      intro stmt st hloop hstmt
      cases stmt <;> simp [LoopFree, execStmtRec, execStmtFull] at hloop ⊢
  | succ fuel ih =>
      intro stmt st hloop hstmt
      cases stmt with
      | skip =>
          simp [execStmtRec, execStmtFull]
      | ret e =>
          cases e <;> simp [NoDirectCalls] at hstmt
          all_goals
            simp [execStmtRec, execStmtFull]
      | assign lhs rhs =>
          cases lhs <;> cases rhs <;> simp [NoDirectCalls] at hstmt
          all_goals
            first | (simp [execStmtRec, execStmtFull]; try rfl)
      | seq s1 s2 =>
          rcases hloop with ⟨hloop1, hloop2⟩
          rcases hstmt with ⟨h1, h2⟩
          have hs1 := ih s1 st hloop1 h1
          rw [execStmtRec, execStmtFull, hs1]
          cases hres : execStmtFull funEnv fuel s1 st <;> simp
          case some res =>
            cases res with
            | normal st' =>
                simpa [execStmtRec, execStmtFull] using ih s2 st' hloop2 h2
            | returned v st' =>
                simp
      | ite cond th el =>
          rcases hloop with ⟨hloopTh, hloopEl⟩
          rcases hstmt with ⟨hth, hel⟩
          cases hcond : evalExpr cond st with
          | none =>
              simp [execStmtRec, execStmtFull, hcond]
          | some v =>
            cases htruth : isTruthy v with
            | false =>
                simpa [execStmtRec, execStmtFull, hcond, htruth] using
                  ih el st hloopEl hel
            | true =>
                simpa [execStmtRec, execStmtFull, hcond, htruth] using
                  ih th st hloopTh hth
      | block decls body =>
          have hbody := ih body (enterBlockState st decls) hloop hstmt
          rw [execStmtRec, execStmtFull, hbody]
          cases hres : execStmtFull funEnv fuel body (enterBlockState st decls) <;> simp
          case some res =>
            cases res <;> simp [restoreBlockState]
      | switch e tag caseBody default =>
          cases hloop
      | forLoop init cond step body =>
          cases hloop
      | «break» =>
          cases hloop
      | «continue» =>
          cases hloop
      | whileInv cond inv body =>
          cases hloop
      | alloc x cells =>
          simp [execStmtRec, execStmtFull]
      | free e cells =>
          simp [execStmtRec, execStmtFull]
          rfl
      | decl x ty =>
          simp [execStmtRec, execStmtFull]

/-- Recursive environment soundness packages:
1. a termination measure over call-entry states, and
2. a proof that every function body returns a post-state when executed with the
   exact fuel prescribed by that measure.

The intended construction is well-founded induction on `term.measure fname st`.
-/
structure FunEnvSoundRec (funEnv : FunEnv) where
  term : TermMeasure
  exec_sound :
    ∀ fname spec, funEnv fname = some spec →
      ∀ {st}, spec.pre st →
        ∃ ret st',
          execStmtRec funEnv (term.measure fname st) spec.body st = some (.returned ret st') ∧
          spec.post ret st'

/-- Recursive call soundness, explicit form. The caller provides the exact
callee lookup / argument evaluation facts extracted from `swpCall`. -/
theorem execCall_rec_sound (funEnv : FunEnv) (henv : FunEnvSoundRec funEnv)
    {fname args st spec vals} {Q : CVal → SProp}
    (hlookup : funEnv fname = some spec)
    (hvals : evalArgs args st = some vals)
    (hlen : vals.length = spec.params.length)
    (hpre : spec.pre (callEntryState st spec vals))
    (hpost : ∀ retVal st', spec.post retVal st' → Q retVal (restoreCallerState st st')) :
    ∃ ret st',
      execCallRec funEnv (henv.term.measure fname (callEntryState st spec vals) + 1) fname args st =
        some (ret, st') ∧
      Q ret st' := by
  rcases henv.exec_sound fname spec hlookup hpre with ⟨ret, callee, hexec, hq⟩
  refine ⟨ret, restoreCallerState st callee, ?_, ?_⟩
  · simp [execCallRec, hlookup, hvals, hlen, hexec]
  · exact hpost ret callee hq

/-- `swpCall`-driven wrapper around `execCall_rec_sound`. -/
theorem swpCall_execCall_rec_sound (funEnv : FunEnv) (henv : FunEnvSoundRec funEnv)
    {fname args st} {Q : CVal → SProp} :
    swpCall funEnv fname args Q st →
    ∃ spec vals ret st',
      funEnv fname = some spec ∧
      evalArgs args st = some vals ∧
      vals.length = spec.params.length ∧
      spec.pre (callEntryState st spec vals) ∧
      execCallRec funEnv (henv.term.measure fname (callEntryState st spec vals) + 1) fname args st =
        some (ret, st') ∧
      Q ret st' := by
  intro hcall
  rcases swpCall_elim (funEnv := funEnv) (fname := fname) (args := args) (Q := Q) hcall with
    ⟨spec, vals, hlookup, hvals, hlen, hpre, hpost⟩
  rcases execCall_rec_sound (funEnv := funEnv) (henv := henv) hlookup hvals hlen hpre hpost with
    ⟨ret, st', hexec, hq⟩
  exact ⟨spec, vals, ret, st', hlookup, hvals, hlen, hpre, hexec, hq⟩

end HeytingLean.LeanCP
