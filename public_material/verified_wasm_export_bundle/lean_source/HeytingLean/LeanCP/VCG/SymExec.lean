import HeytingLean.LeanCP.VCG.WP
import HeytingLean.LeanCP.VCG.SWPCallSound

/-!
# LeanCP Symbolic VC Generation

Phase 4's symbolic execution layer is translational: it does not invent a new
semantics. It packages proof obligations over the already-landed state-sensitive
surfaces (`swp`, `swpFull`, `swhileWP`, `swhileWPFull`) into a structured VC
format that downstream tactics and benchmark harnesses can consume.

This module is intentionally fail-closed:

- loop hints must resolve to real `whileInv` nodes,
- every loop in the traversed program must have a matching hint,
- call-aware generation must be requested explicitly via `VerifyMode.swpFull`.
-/

namespace HeytingLean.LeanCP

inductive VerifyMode where
  | swp
  | swpFull
  deriving DecidableEq, Repr, Inhabited

inductive VCKind where
  | main
  | seqBoundary
  | branchThen
  | branchElse
  | loopInit
  | loopStep
  | loopExit
  | callBoundary
  deriving DecidableEq, Repr, Inhabited

inductive VCAutoClass where
  | structural
  | pure
  | manual
  deriving DecidableEq, Repr, Inhabited

structure VCOrigin where
  path : List Nat
  label : String
  deriving DecidableEq, Repr, Inhabited

structure VC where
  name : String
  kind : VCKind
  origin : VCOrigin
  goal : Prop
  autoClass : VCAutoClass := .manual

structure VCPreview where
  name : String
  kind : VCKind
  origin : VCOrigin
  autoClass : VCAutoClass
  deriving DecidableEq, Repr, Inhabited

def VC.preview (vc : VC) : VCPreview :=
  { name := vc.name
    kind := vc.kind
    origin := vc.origin
    autoClass := vc.autoClass }

structure LoopHint where
  path : List Nat
  inv : SProp
  fuelHint : Nat

structure VerifyInput where
  name : String
  mode : VerifyMode
  body : CStmt
  pre : SProp
  post : CVal → SProp
  funEnv : FunEnv := fun _ => none
  loops : List LoopHint := []

inductive VCGenError where
  | missingLoopHint (path : List Nat)
  | badLoopHint (path : List Nat)
  deriving DecidableEq, Repr, Inhabited

structure VCBundle where
  pre : SProp
  vcs : List VC

def mkOrigin (path : List Nat) (label : String) : VCOrigin :=
  { path := path, label := label }

def childPath (path : List Nat) (idx : Nat) : List Nat :=
  path ++ [idx]

def vcName (base : String) (path : List Nat) (suffix : String) : String :=
  let segs := path.map toString
  let pathStr :=
    match segs with
    | [] => "root"
    | _ => String.intercalate "_" segs
  s!"{base}_{suffix}_{pathStr}"

def statementAtPath : CStmt → List Nat → Option CStmt
  | stmt, [] => some stmt
  | .seq s1 _s2, 0 :: rest => statementAtPath s1 rest
  | .seq _s1 s2, 1 :: rest => statementAtPath s2 rest
  | .ite _ th _el, 0 :: rest => statementAtPath th rest
  | .ite _ _th el, 1 :: rest => statementAtPath el rest
  | .whileInv _ _ body, 0 :: rest => statementAtPath body rest
  | .block _ body, 0 :: rest => statementAtPath body rest
  | .switch _ _ caseBody _default, 0 :: rest => statementAtPath caseBody rest
  | .switch _ _ _caseBody default, 1 :: rest => statementAtPath default rest
  | .forLoop init _ _step _body, 0 :: rest => statementAtPath init rest
  | .forLoop _init _ _step body, 2 :: rest => statementAtPath body rest
  | .forLoop _init _ step _body, 1 :: rest => statementAtPath step rest
  | _, _ => none

def loopPaths : CStmt → List (List Nat)
  | stmt =>
      let rec go (path : List Nat) : CStmt → List (List Nat)
        | .seq s1 s2 => go (childPath path 0) s1 ++ go (childPath path 1) s2
        | .ite _ th el => go (childPath path 0) th ++ go (childPath path 1) el
        | .whileInv _ _ body => path :: go (childPath path 0) body
        | .block _ body => go (childPath path 0) body
        | .switch _ _ caseBody default =>
            go (childPath path 0) caseBody ++ go (childPath path 1) default
        | .forLoop init _ step body =>
            go (childPath path 0) init ++
            go (childPath path 1) step ++
            go (childPath path 2) body
        | _ => []
      go [] stmt

def findLoopHint? (hints : List LoopHint) (path : List Nat) : Option LoopHint :=
  hints.find? (fun hint => hint.path = path)

def validateLoopHints (stmt : CStmt) (hints : List LoopHint) : Except VCGenError Unit := do
  for path in loopPaths stmt do
    if findLoopHint? hints path |>.isNone then
      throw (.missingLoopHint path)
  for hint in hints do
    match statementAtPath stmt hint.path with
    | some (.whileInv _ _ _) => pure ()
    | _ => throw (.badLoopHint hint.path)

noncomputable def surfacePre (mode : VerifyMode) (funEnv : FunEnv) (stmt : CStmt)
    (Q : CVal → SProp) : SProp :=
  match mode with
  | .swp => swp stmt Q
  | .swpFull => swpFull funEnv stmt Q

noncomputable def whileSurface (mode : VerifyMode) (funEnv : FunEnv) (fuel : Nat)
    (cond : CExpr) (inv : SProp) (body : CStmt) (Q : CVal → SProp) : SProp :=
  match mode with
  | .swp => swhileWP fuel cond inv body Q
  | .swpFull => swhileWPFull funEnv fuel cond inv body Q

noncomputable def whileContinuePost (mode : VerifyMode) (funEnv : FunEnv) (fuel : Nat)
    (cond : CExpr) (inv : SProp) (body : CStmt) (Q : CVal → SProp) : CVal → SProp :=
  fun _ =>
    match fuel with
    | 0 => whileSurface mode funEnv 0 cond inv body Q
    | fuel' + 1 => whileSurface mode funEnv fuel' cond inv body Q

noncomputable def requiredPre (mode : VerifyMode) (funEnv : FunEnv) (loops : List LoopHint)
    : CStmt → (CVal → SProp) → List Nat → Except VCGenError SProp
  | .seq s1 s2, Q, path => do
      let q2 ← requiredPre mode funEnv loops s2 Q (childPath path 1)
      requiredPre mode funEnv loops s1 (fun _ => q2) (childPath path 0)
  | .ite cond th el, Q, path => do
      let qTh ← requiredPre mode funEnv loops th Q (childPath path 0)
      let qEl ← requiredPre mode funEnv loops el Q (childPath path 1)
      pure (fun st =>
        match evalExpr cond st with
        | some v => if isTruthy v then qTh st else qEl st
        | none => False)
  | .whileInv cond _ann body, Q, path => do
      let some hint := findLoopHint? loops path
        | throw (.missingLoopHint path)
      pure (whileSurface mode funEnv hint.fuelHint cond hint.inv body Q)
  | stmt, Q, _path =>
      pure (surfacePre mode funEnv stmt Q)

noncomputable def branchThenPre (currentPre : SProp) (cond : CExpr) : SProp :=
  fun st =>
    currentPre st ∧
      match evalExpr cond st with
      | some v => isTruthy v = true
      | none => False

noncomputable def branchElsePre (currentPre : SProp) (cond : CExpr) : SProp :=
  fun st =>
    currentPre st ∧
      match evalExpr cond st with
      | some v => isTruthy v = false
      | none => False

noncomputable def callBoundaryPre (funEnv : FunEnv) (stmt : CStmt)
    (Q : CVal → SProp) : Option SProp :=
  match stmt with
  | .assign (.var x) (.call fname args) =>
      some (swpCall funEnv fname args (fun ret st => Q CVal.undef (st.updateVar x ret)))
  | .ret (.call fname args) =>
      some (swpCall funEnv fname args Q)
  | _ => none

noncomputable def collectLocalVCs (base : String) (mode : VerifyMode) (funEnv : FunEnv)
    (loops : List LoopHint) : CStmt → SProp → (CVal → SProp) → List Nat → Except VCGenError (List VC)
  | .seq s1 s2, currentPre, Q, path => do
      let q2 ← requiredPre mode funEnv loops s2 Q (childPath path 1)
      let leftVC : VC :=
        { name := vcName base path "seq_boundary"
          kind := .seqBoundary
          origin := mkOrigin path "seq"
          goal := ∀ st, currentPre st → q2 st
          autoClass := .manual }
      let vcs1 ← collectLocalVCs base mode funEnv loops s1 currentPre (fun _ => q2) (childPath path 0)
      let vcs2 ← collectLocalVCs base mode funEnv loops s2 q2 Q (childPath path 1)
      pure (leftVC :: vcs1 ++ vcs2)
  | .ite cond th el, currentPre, Q, path => do
      let vcsTh ← collectLocalVCs base mode funEnv loops th (branchThenPre currentPre cond) Q (childPath path 0)
      let vcsEl ← collectLocalVCs base mode funEnv loops el (branchElsePre currentPre cond) Q (childPath path 1)
      let thVC : VC :=
        { name := vcName base (childPath path 0) "branch_then"
          kind := .branchThen
          origin := mkOrigin (childPath path 0) "ite.then"
          goal := ∀ st, branchThenPre currentPre cond st → True
          autoClass := .pure }
      let elVC : VC :=
        { name := vcName base (childPath path 1) "branch_else"
          kind := .branchElse
          origin := mkOrigin (childPath path 1) "ite.else"
          goal := ∀ st, branchElsePre currentPre cond st → True
          autoClass := .pure }
      pure (thVC :: elVC :: vcsTh ++ vcsEl)
  | .assign (.var x) (.call fname args), currentPre, Q, path =>
      let boundary : VC :=
        { name := vcName base path "call_assign"
          kind := .callBoundary
          origin := mkOrigin path s!"call.assign.{fname}"
          goal := ∀ st, currentPre st →
            swpCall funEnv fname args (fun ret st' => Q CVal.undef (st'.updateVar x ret)) st
          autoClass := .manual }
      pure [boundary]
  | .ret (.call fname args), currentPre, Q, path =>
      let boundary : VC :=
        { name := vcName base path "call_return"
          kind := .callBoundary
          origin := mkOrigin path s!"call.return.{fname}"
          goal := ∀ st, currentPre st → swpCall funEnv fname args Q st
          autoClass := .manual }
      pure [boundary]
  | .whileInv cond _ann body, currentPre, Q, path => do
      let some hint := findLoopHint? loops path
        | throw (.missingLoopHint path)
      let bodyPost := whileContinuePost mode funEnv hint.fuelHint cond hint.inv body Q
      let bodyPre ← requiredPre mode funEnv loops body bodyPost (childPath path 0)
      let initVC : VC :=
        { name := vcName base path "loop_init"
          kind := .loopInit
          origin := mkOrigin path "while"
          goal := ∀ st, currentPre st → hint.inv st
          autoClass := .manual }
      let stepVC : VC :=
        { name := vcName base path "loop_step"
          kind := .loopStep
          origin := mkOrigin path "while"
          goal := ∀ st, hint.inv st →
            match evalExpr cond st with
            | some v => if isTruthy v then bodyPre st else True
            | none => False
          autoClass := .manual }
      let exitVC : VC :=
        { name := vcName base path "loop_exit"
          kind := .loopExit
          origin := mkOrigin path "while"
          goal := ∀ st, hint.inv st →
            match evalExpr cond st with
            | some v => if isTruthy v then True else Q CVal.undef st
            | none => False
          autoClass := .manual }
      let bodyVCs ← collectLocalVCs base mode funEnv loops body bodyPre bodyPost (childPath path 0)
      pure (initVC :: stepVC :: exitVC :: bodyVCs)
  | .block _ _body, _currentPre, _Q, _path => pure []
  | .switch _ _ _ _, _currentPre, _Q, _path => pure []
  | .forLoop _ _ _ _, _currentPre, _Q, _path => pure []
  | _, _, _, _ => pure []

def collectLocalPreviews (base : String) (loops : List LoopHint) :
    CStmt → List Nat → Except VCGenError (List VCPreview)
  | .seq s1 s2, path => do
      let left ← collectLocalPreviews base loops s1 (childPath path 0)
      let right ← collectLocalPreviews base loops s2 (childPath path 1)
      let here : VCPreview :=
        { name := vcName base path "seq_boundary"
          kind := .seqBoundary
          origin := mkOrigin path "seq"
          autoClass := .manual }
      pure (here :: left ++ right)
  | .ite _ th el, path => do
      let thPreviews ← collectLocalPreviews base loops th (childPath path 0)
      let elPreviews ← collectLocalPreviews base loops el (childPath path 1)
      let thVC : VCPreview :=
        { name := vcName base (childPath path 0) "branch_then"
          kind := .branchThen
          origin := mkOrigin (childPath path 0) "ite.then"
          autoClass := .pure }
      let elVC : VCPreview :=
        { name := vcName base (childPath path 1) "branch_else"
          kind := .branchElse
          origin := mkOrigin (childPath path 1) "ite.else"
          autoClass := .pure }
      pure (thVC :: elVC :: thPreviews ++ elPreviews)
  | .whileInv _ _ body, path => do
      let some _hint := findLoopHint? loops path
        | throw (.missingLoopHint path)
      let bodyPreviews ← collectLocalPreviews base loops body (childPath path 0)
      let initVC : VCPreview :=
        { name := vcName base path "loop_init"
          kind := .loopInit
          origin := mkOrigin path "while"
          autoClass := .manual }
      let stepVC : VCPreview :=
        { name := vcName base path "loop_step"
          kind := .loopStep
          origin := mkOrigin path "while"
          autoClass := .manual }
      let exitVC : VCPreview :=
        { name := vcName base path "loop_exit"
          kind := .loopExit
          origin := mkOrigin path "while"
          autoClass := .manual }
      pure (initVC :: stepVC :: exitVC :: bodyPreviews)
  | .assign (.var _) (.call fname _), path =>
      pure [{ name := vcName base path "call_assign"
              kind := .callBoundary
              origin := mkOrigin path s!"call.assign.{fname}"
              autoClass := .manual }]
  | .ret (.call fname _), path =>
      pure [{ name := vcName base path "call_return"
              kind := .callBoundary
              origin := mkOrigin path s!"call.return.{fname}"
              autoClass := .manual }]
  | _, _ => pure []

noncomputable def generateBundle (input : VerifyInput) : Except VCGenError VCBundle := do
  validateLoopHints input.body input.loops
  let mainPre ← requiredPre input.mode input.funEnv input.loops input.body input.post []
  let main : VC :=
    { name := vcName input.name [] "main"
      kind := .main
      origin := mkOrigin [] "function"
      goal := ∀ st, input.pre st → mainPre st
      autoClass := .manual }
  let locals ← collectLocalVCs input.name input.mode input.funEnv input.loops
    input.body input.pre input.post []
  pure { pre := mainPre, vcs := main :: locals }

noncomputable def generateVCs (input : VerifyInput) : Except VCGenError (List VC) := do
  let bundle ← generateBundle input
  pure bundle.vcs

def generateVCPreviews (input : VerifyInput) : Except VCGenError (List VCPreview) := do
  validateLoopHints input.body input.loops
  let locals ← collectLocalPreviews input.name input.loops input.body []
  let main : VCPreview :=
    { name := vcName input.name [] "main"
      kind := .main
      origin := mkOrigin [] "function"
      autoClass := .manual }
  pure (main :: locals)

def countKind (kind : VCKind) (vcs : List VCPreview) : Nat :=
  vcs.countP (fun vc => vc.kind = kind)

def VCListValid (vcs : List VC) : Prop :=
  ∀ vc, vc ∈ vcs → vc.goal

theorem generateBundle_head_main (input : VerifyInput) :
    ∀ {bundle},
      generateBundle input = Except.ok bundle →
      ∃ mainPre locals,
        bundle.pre = mainPre ∧
        bundle.vcs =
          { name := vcName input.name [] "main"
            kind := .main
            origin := mkOrigin [] "function"
            goal := ∀ st, input.pre st → mainPre st
            autoClass := .manual } :: locals := by
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
      | ok mainPre =>
          simp [hpre] at hgen
          cases hlocals :
              collectLocalVCs input.name input.mode input.funEnv input.loops
                input.body input.pre input.post [] with
          | error err =>
              simp [hlocals] at hgen
              cases hgen
          | ok locals =>
              simp [hlocals] at hgen
              cases hgen
              exact ⟨mainPre, locals, rfl, rfl⟩

theorem generateBundle_sound (input : VerifyInput) :
    ∀ {bundle},
      generateBundle input = Except.ok bundle →
      VCListValid bundle.vcs →
      ∀ st, input.pre st → bundle.pre st := by
  intro bundle hgen hvalid st hpre
  rcases generateBundle_head_main input hgen with ⟨mainPre, locals, hpreEq, hvcs⟩
  rw [hvcs] at hvalid
  have hmain : ∀ st, input.pre st → mainPre st := by
    exact hvalid _ (List.mem_cons.mpr (Or.inl rfl))
  rw [hpreEq]
  exact hmain st hpre

/-- Legacy heap-only VC wrapper kept for compatibility. -/
structure ProofObligation where
  name : String
  goal : Prop

def collectVCs (spec : CFunSpec) : List ProofObligation :=
  [{ name := s!"{spec.name}_vc_main",
     goal := genVC spec }]

end HeytingLean.LeanCP
