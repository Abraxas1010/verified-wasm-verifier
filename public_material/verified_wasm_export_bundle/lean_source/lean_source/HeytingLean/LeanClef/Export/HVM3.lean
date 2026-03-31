import HeytingLean.LoF.ICC.Syntax

/-!
# ICC.Term → HVM3 Text Emitter

Emit verified ICC terms as HVM3 source text for GPU-parallel
interaction net reduction.

HVM3 enforces linearity: each lambda variable must be used exactly once.
- 0 uses → `λ_ body` (erasure)
- 1 use  → `λx body` (linear)
- 2+ uses → `λx !&L{a b} = x; body` with distinct names per occurrence

ICC terms use de Bruijn indices; HVM3 uses named variables. The emitter
translates indices to fresh names and inserts dup/erase annotations
based on variable occurrence counts.

## Linearity handling

For a lambda whose body uses the bound variable N times:
- N=0: emit `λ_` (erasure)
- N=1: emit `λx` (linear)
- N≥2: generate N fresh names (v_0 … v_{N-1}), emit a dup chain
  `!&L0{v_0 t0} = x; !&L1{v_1 t1} = t0; … !&L{v_{N-2} v_{N-1}} = t_{N-3}; body`
  and emit the body consuming one name per occurrence (left-to-right).

The context maps each de Bruijn index to a QUEUE of names. Each `.var idx`
emission pops the first available name from the queue for that index.
-/

namespace HeytingLean.LeanClef.Export.HVM3

open HeytingLean.LoF.ICC

/-- Count occurrences of a specific de Bruijn index in a term.
    0 → erasure, 1 → linear, 2+ → duplication. -/
def varUseCount : Term → Nat → Nat
  | .var idx, target => if idx == target then 1 else 0
  | .lam body, target => varUseCount body (target + 1)
  | .app fn arg, target => varUseCount fn target + varUseCount arg target
  | .bridge body, target => varUseCount body (target + 1)
  | .ann val typ, target => varUseCount val target + varUseCount typ target

/-- Emitter state: fresh variable counter, fresh dup label counter. -/
structure EmitState where
  nextVar : Nat := 0
  nextLabel : Nat := 0

def freshVar (s : EmitState) : String × EmitState :=
  (s!"x{s.nextVar}", { s with nextVar := s.nextVar + 1 })

def freshLabel (s : EmitState) : Nat × EmitState :=
  (s.nextLabel, { s with nextLabel := s.nextLabel + 1 })

/-- Generate N fresh variable names. -/
def freshVars (s : EmitState) (n : Nat) : List String × EmitState :=
  match n with
  | 0 => ([], s)
  | n + 1 =>
    let (name, s') := freshVar s
    let (rest, s'') := freshVars s' n
    (name :: rest, s'')

/-- Context entry: a queue of names for a single de Bruijn index.
    Each variable occurrence consumes the first name from the queue. -/
abbrev VarCtx := List (List String)

/-- Look up the FIRST available name for a de Bruijn index, returning
    the updated context with that name consumed. -/
def consumeVar (ctx : VarCtx) (idx : Nat) : String × VarCtx :=
  match idx, ctx with
  | _, [] => (s!"FREE_{idx}", ctx)
  | 0, [] :: rest => (s!"FREE_0", [] :: rest)
  | 0, (name :: names) :: rest => (name, names :: rest)
  | n + 1, entry :: rest =>
    let (name, rest') := consumeVar rest n
    (name, entry :: rest')

/-- Build a dup chain for N copies of a variable.
    For `original` with copies [v0, v1, …, v_{N-1}], emits:
    `!&L0{v0 t0} = original; !&L1{v1 t1} = t0; … !&L{v_{N-2} v_{N-1}} = t_{N-3};`
    Returns the chain prefix string and the updated state. -/
def buildDupChain (original : String) (copies : List String) (st : EmitState)
    : String × EmitState :=
  match copies with
  | [] => ("", st)
  | [_single] => ("", st)  -- 1 copy needs no dup
  | [a, b] =>
    let (lbl, st') := freshLabel st
    (s!"!&{lbl}\{{a} {b}} = {original}; ", st')
  | a :: rest =>
    let (lbl, st') := freshLabel st
    let tmpName := s!"{original}_tmp{lbl}"
    let (restChain, st'') := buildDupChain tmpName rest st'
    (s!"!&{lbl}\{{a} {tmpName}} = {original}; {restChain}", st'')

/-- Emit a single ICC term as HVM3 text.

    The context maps each de Bruijn index to a QUEUE of names (innermost
    binder at index 0 = head of list). Each `.var` emission CONSUMES
    one name from the queue, ensuring distinct names for duplicate uses.

    Returns (hvm3_text, updated_context, updated_state). -/
def emitHVM3Core : Term → VarCtx → EmitState → String × VarCtx × EmitState
  | .var idx, ctx, st =>
    let (name, ctx') := consumeVar ctx idx
    (name, ctx', st)

  | .lam body, ctx, st =>
    let uses := varUseCount body 0
    if uses == 0 then
      -- Erasure: no names needed for index 0
      let (bodyText, ctx', st') := emitHVM3Core body ([] :: ctx) st
      -- Pop the entry we pushed
      let ctx'' := match ctx' with | _ :: rest => rest | [] => []
      (s!"λ_ {bodyText}", ctx'', st')
    else if uses == 1 then
      -- Linear: one name for index 0
      let (varName, st') := freshVar st
      let (bodyText, ctx', st'') := emitHVM3Core body ([varName] :: ctx) st'
      let ctx'' := match ctx' with | _ :: rest => rest | [] => []
      (s!"λ{varName} {bodyText}", ctx'', st'')
    else
      -- Duplication: generate `uses` fresh names, build dup chain
      let (varName, st') := freshVar st
      let (copies, st'') := freshVars st' uses
      let (dupChain, st''') := buildDupChain varName copies st''
      let (bodyText, ctx', st4) := emitHVM3Core body (copies :: ctx) st'''
      let ctx'' := match ctx' with | _ :: rest => rest | [] => []
      (s!"λ{varName} {dupChain}{bodyText}", ctx'', st4)

  | .app fn arg, ctx, st =>
    let (fnText, ctx', st') := emitHVM3Core fn ctx st
    let (argText, ctx'', st'') := emitHVM3Core arg ctx' st'
    (s!"({fnText} {argText})", ctx'', st'')

  | .bridge body, ctx, st =>
    -- Bridge compiles to lambda at runtime
    let uses := varUseCount body 0
    if uses == 0 then
      let (bodyText, ctx', st') := emitHVM3Core body ([] :: ctx) st
      let ctx'' := match ctx' with | _ :: rest => rest | [] => []
      (s!"λ_ {bodyText}", ctx'', st')
    else if uses == 1 then
      let (varName, st') := freshVar st
      let (bodyText, ctx', st'') := emitHVM3Core body ([varName] :: ctx) st'
      let ctx'' := match ctx' with | _ :: rest => rest | [] => []
      (s!"λ{varName} {bodyText}", ctx'', st'')
    else
      let (varName, st') := freshVar st
      let (copies, st'') := freshVars st' uses
      let (dupChain, st''') := buildDupChain varName copies st''
      let (bodyText, ctx', st4) := emitHVM3Core body (copies :: ctx) st'''
      let ctx'' := match ctx' with | _ :: rest => rest | [] => []
      (s!"λ{varName} {dupChain}{bodyText}", ctx'', st4)

  | .ann val _typ, ctx, st =>
    -- Annotation: erase the type, keep the value at runtime
    emitHVM3Core val ctx st

/-- Emit an ICC term as a complete HVM3 program with `@main` definition. -/
def emitHVM3 (t : Term) : String :=
  let (body, _, _) := emitHVM3Core t [] {}
  s!"@main = {body}\n"

/-- Emit an ICC term as an HVM3 definition with a custom name. -/
def emitHVM3Named (name : String) (t : Term) : String :=
  let (body, _, _) := emitHVM3Core t [] {}
  s!"@{name} = {body}\n"

end HeytingLean.LeanClef.Export.HVM3
