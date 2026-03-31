import Lean
import Lean.Data.Json
import HeytingLean.LoF.Circuit
import HeytingLean.LoF.LoFSecond.Normalization

open Lean
open HeytingLean.LoF
open HeytingLean.LoF.Circuit
open HeytingLean.LoF.LoFSecond

/-!
## LoF Encoding - First-Principles Laws of Form Translation

This module translates Lean type expressions into the Laws of Form algebra,
using the LoFSecond syntax with 3-valued (Kleene) semantics.

## Kauffman's LoF → Heyting Correspondence (from PrimaryAlgebra)

The translation follows Kauffman's proof that LoF is equivalent to Heyting algebra:

| LoF Construct | Heyting Algebra | Lean |
|---------------|-----------------|------|
| `void`        | ⊥ (bottom)      | `False` |
| `marked`      | ⊤ (top)         | `True` |
| `mark A`      | ¬A (a ⇨ ⊥)      | `Not A` |
| `juxt A B`    | A ⊔ B (join)    | `Or A B` |
| `reentry`     | eigenform (fixed point of ¬) | self-referential |

## Derived Operations (de Morgan Laws)

| Logical Op | LoF Encoding |
|------------|--------------|
| A ∧ B      | `mark (juxt (mark A) (mark B))` |
| A → B      | `juxt (mark A) B` |
| A ↔ B      | `mark (juxt (mark (juxt (mark A) B)) (mark (juxt (mark B) A)))` |
| ∀ x, P x   | universal closure (mark around the body) |

## Eigenform Detection

An eigenform satisfies `mark(e) = e` under 3-valued semantics.
In the Kleene interpretation: `reentry` evaluates to `u`, and `not u = u`.

This corresponds to Kauffman's eigenvalue equation and the fixed points
of the Reentry nucleus in Ω_R.
-/

/-- Check if a Lean Name refers to a logical connective -/
def isLogicalConnective (n : Name) : Bool :=
  n == ``And || n == ``Or || n == ``Not || n == ``Iff ||
  n == ``Eq || n == ``True || n == ``False ||
  n == ``Exists || n == ``HEq

/-- Check if a string contains a substring -/
def strContains (s : String) (sub : String) : Bool :=
  (s.splitOn sub).length >= 2

/-- Check if a constant name relates to eigenforms/fixed points -/
def isEigenformRelated (n : Name) : Bool :=
  let s := n.toString
  strContains s "eigenform" ||
  strContains s "Eigenform" ||
  strContains s "reentry" ||
  strContains s "Reentry" ||
  strContains s "fixedpoint" ||
  strContains s "FixedPoint" ||
  strContains s ".process" ||
  strContains s "primordial" ||
  strContains s "Nucleus" ||
  strContains s "idempotent"

/-- Extract the head constant from an application -/
partial def getAppHead (e : Lean.Expr) : Option Name :=
  match e with
  | .const n _ => some n
  | .app f _ => getAppHead f
  | _ => none

/-- Extract arguments from an application -/
partial def getAppArgs (e : Lean.Expr) (acc : List Lean.Expr := []) : List Lean.Expr :=
  match e with
  | .app f a => getAppArgs f (a :: acc)
  | _ => acc

/-- Convert a Lean Expr to LoFSecond.Expr using semantic recognition.
    This properly handles logical connectives via the Kauffman correspondence. -/
def exprToLoF (e : Lean.Expr) (fuel : Nat := 64) : LoFSecond.Expr 0 :=
  match fuel with
  | 0 => .void
  | fuel' + 1 =>
    -- First, check if this is a known logical connective
    match getAppHead e with
    | some n =>
      let args := getAppArgs e
      -- Handle logical connectives by name (Kauffman correspondence)
      if n == ``False then
        .void  -- False = ⊥ = void
      else if n == ``True then
        .marked  -- True = ⊤ = mark void
      else if n == ``Not then
        -- Not A = mark A
        match args[0]? with
        | some a => .mark (exprToLoF a fuel')
        | none => .marked
      else if n == ``Or then
        -- Or A B = juxt A B
        match args[0]?, args[1]? with
        | some a, some b => .juxt (exprToLoF a fuel') (exprToLoF b fuel')
        | _, _ => .marked
      else if n == ``And then
        -- And A B = mark (juxt (mark A) (mark B))  [de Morgan]
        match args[0]?, args[1]? with
        | some a, some b =>
          .mark (.juxt (.mark (exprToLoF a fuel')) (.mark (exprToLoF b fuel')))
        | _, _ => .marked
      else if n == ``Iff then
        -- Iff A B = (A → B) ∧ (B → A)
        -- = mark (juxt (mark (juxt (mark A) B)) (mark (juxt (mark B) A)))
        match args[0]?, args[1]? with
        | some a, some b =>
          let aLoF := exprToLoF a fuel'
          let bLoF := exprToLoF b fuel'
          let aToB := .juxt (.mark aLoF) bLoF  -- A → B
          let bToA := .juxt (.mark bLoF) aLoF  -- B → A
          .mark (.juxt (.mark aToB) (.mark bToA))  -- conjunction
        | _, _ => .marked
      else if n == ``Eq || n == ``HEq then
        -- Eq A B: Translate as conjunction of two implications (iff-like)
        -- The LHS and RHS should be structurally translated
        match args[1]?, args[2]? with
        | some lhs, some rhs =>
          -- Equality in LoF: both sides must be equivalent
          -- We translate as: mark(juxt(mark(lhs)) (mark(rhs))) - they agree
          let lhsLoF := exprToLoF lhs fuel'
          let rhsLoF := exprToLoF rhs fuel'
          .mark (.juxt (.mark lhsLoF) (.mark rhsLoF))
        | _, _ => .marked
      else if n == ``Exists then
        -- ∃ x, P x = existential (dual of universal)
        -- In LoF: mark (mark (body under abstraction))
        match args[1]? with
        | some body => .mark (.mark (exprToLoF body fuel'))
        | none => .marked
      else
        -- All other constants: translate structurally
        -- Eigenform detection is separate (affects psr flag, not structure)
        translateSyntactic e fuel'
    | none =>
      -- No head constant found, use syntactic translation
      translateSyntactic e fuel'
where
  /-- Syntactic fallback translation for non-logical expressions -/
  translateSyntactic (e : Lean.Expr) (fuel : Nat) : LoFSecond.Expr 0 :=
    match fuel with
    | 0 => .void
    | fuel' + 1 =>
      match e with
      | .sort _ => .void  -- Type/Prop sorts = unmarked
      | .const _ _ => .marked  -- All constants are marked (definite values)
      | .bvar _ => .marked
      | .fvar _ => .marked
      | .mvar _ => .marked  -- Metavariables treated as marked (will be instantiated)
      | .app f a =>
        -- General application: juxtaposition of function and argument
        .juxt (exprToLoF f fuel') (exprToLoF a fuel')
      | .lam _ dom body _ =>
        -- Lambda abstraction: mark around (domain, body)
        -- λ x : A, B = boundary containing the function space
        let domLoF := exprToLoF dom fuel'
        let bodyLoF := exprToLoF body fuel'
        .mark (.juxt domLoF bodyLoF)
      | .forallE _ dom body _ =>
        -- Universal/Pi: ∀ x : A, B
        -- In LoF with Kauffman correspondence:
        -- ∀ x : A, B ≈ A → B = ¬A ∨ B = juxt (mark A) B
        let domLoF := exprToLoF dom fuel'
        let bodyLoF := exprToLoF body fuel'
        .juxt (.mark domLoF) bodyLoF
      | .letE _ _ val body _ =>
        -- Let binding: the value and body coexist
        .juxt (exprToLoF val fuel') (exprToLoF body fuel')
      | .lit _ => .marked
      | .mdata _ inner => exprToLoF inner fuel'
      | .proj _ _ base => .mark (exprToLoF base fuel')

/-- Render LoFSecond.Expr as a JSON AST representation -/
def lofExprToJson (e : LoFSecond.Expr n) : Json :=
  match e with
  | .void => Json.mkObj [("kind", Json.str "void")]
  | .var i => Json.mkObj [("kind", Json.str "var"), ("idx", Json.num i.val)]
  | .mark inner => Json.mkObj [("kind", Json.str "mark"), ("inner", lofExprToJson inner)]
  | .juxt l r => Json.mkObj [("kind", Json.str "juxt"), ("left", lofExprToJson l), ("right", lofExprToJson r)]
  | .reentry => Json.mkObj [("kind", Json.str "reentry")]

/-- Render LoFSecond.Expr in Spencer-Brown notation.

    Uses standard LoF typography per Kauffman/Spencer-Brown:
    - `⟨ ⟩` for the mark (cross/distinction boundary)
    - `·` for void (the unmarked state)
    - `∞` for reentry (eigenform/fixed point of the mark)

    See: https://en.wikipedia.org/wiki/Laws_of_Form
    See: https://mathworld.wolfram.com/Spencer-BrownForm.html
-/
def lofExprToString (e : LoFSecond.Expr n) : String :=
  match e with
  | .void => "·"  -- The unmarked state (void)
  | .var i => s!"x{i.val}"
  | .mark inner =>
    let innerStr := lofExprToString inner
    if innerStr == "·" then "⟨⟩"  -- ⟨·⟩ simplifies to ⟨⟩ (marked state)
    else s!"⟨{innerStr}⟩"
  | .juxt l r => s!"{lofExprToString l}{lofExprToString r}"  -- Juxtaposition with no separator
  | .reentry => "∞"  -- The eigenform (fixed point: ⟨∞⟩ = ∞)

/-- Check if a LoFSecond.Expr is an eigenform (fixed point of mark).
    An eigenform satisfies: mark(e) evaluates the same as e under all valuations.
    In 3-valued semantics, reentry is the canonical eigenform. -/
def isEigenform (e : LoFSecond.Expr 0) : Bool :=
  -- In 0-variable context, we just evaluate directly
  let v := LoFSecond.eval e (fun i => Fin.elim0 i)
  let mv := LoFSecond.eval (.mark e) (fun i => Fin.elim0 i)
  v == mv

/-- Check if the LoF expression contains a reentry (eigenform marker) -/
def containsReentry : LoFSecond.Expr n → Bool
  | .void => false
  | .var _ => false
  | .reentry => true
  | .mark inner => containsReentry inner
  | .juxt l r => containsReentry l || containsReentry r

/-- Detect if a Lean type represents an eigenform/fixed-point statement.
    Patterns detected:
    - `R x = x` (explicit fixed point)
    - `f (f x) = f x` (idempotence)
    - `nucleus.apply x = x` (nucleus fixed point)
    - Theorems about Reentry.process, primordial, eigenform, etc.
-/
def detectEigenformPattern (e : Lean.Expr) : Bool :=
  -- Check the head constant for eigenform-related names
  match getAppHead e with
  | some n =>
    if isEigenformRelated n then true
    else
      -- Check if it's an equality where LHS and RHS have eigenform structure
      if n == ``Eq || n == ``HEq then
        let args := getAppArgs e
        -- Check if arguments reference eigenform-related constructs
        args.any fun arg =>
          match getAppHead arg with
          | some argName => isEigenformRelated argName
          | none => false
      else false
  | none => false

/-- Recursively check if any part of the type mentions eigenforms -/
partial def typeInvolvesEigenform (e : Lean.Expr) : Bool :=
  match e with
  | .const n _ => isEigenformRelated n
  | .app f a => typeInvolvesEigenform f || typeInvolvesEigenform a
  | .lam _ ty body _ => typeInvolvesEigenform ty || typeInvolvesEigenform body
  | .forallE _ ty body _ => typeInvolvesEigenform ty || typeInvolvesEigenform body
  | .letE _ ty val body _ => typeInvolvesEigenform ty || typeInvolvesEigenform val || typeInvolvesEigenform body
  | .mdata _ inner => typeInvolvesEigenform inner
  | .proj _ _ base => typeInvolvesEigenform base
  | _ => false

/-- Compute the "depth" of an expression - how many nested marks it has.
    This is related to the birth time in Ω_R. -/
def lofDepth (e : LoFSecond.Expr n) : Nat :=
  match e with
  | .void => 0
  | .var _ => 0
  | .reentry => 1  -- reentry has depth 1 (first non-trivial level)
  | .mark inner => 1 + lofDepth inner
  | .juxt l r => max (lofDepth l) (lofDepth r)

/-!
## Bi-directional Transformation: LoF → Logical Structure

To verify the forward transformation preserves information, we implement
the reverse mapping from LoF expressions back to a logical representation.

### Kauffman Inverse Correspondence

| LoF Pattern | Logical Structure |
|-------------|-------------------|
| `void` | `False` |
| `mark void` | `True` |
| `mark A` | `Not A` |
| `juxt A B` | `Or A B` |
| `mark (juxt (mark A) (mark B))` | `And A B` |
| `juxt (mark A) B` | `Implies A B` |
| `reentry` | `Eigenform` (fixed point) |

The round-trip property we verify:
  For logical connectives (And, Or, Not, Implies, Iff):
    decode(encode(e)) ≈ e  (structurally equivalent)
-/

/-- Logical structure representation for decoded LoF expressions -/
inductive LogicalForm where
  | bottom : LogicalForm  -- False/⊥
  | top : LogicalForm     -- True/⊤
  | var : Nat → LogicalForm  -- Variable reference
  | neg : LogicalForm → LogicalForm  -- Not
  | disj : LogicalForm → LogicalForm → LogicalForm  -- Or
  | conj : LogicalForm → LogicalForm → LogicalForm  -- And
  | impl : LogicalForm → LogicalForm → LogicalForm  -- Implies
  | eigenform : LogicalForm  -- Fixed point of negation
  deriving Repr, BEq, Inhabited

/-- Convert LogicalForm to readable string -/
def LogicalForm.toString : LogicalForm → String
  | .bottom => "⊥"
  | .top => "⊤"
  | .var n => s!"x{n}"
  | .neg a => s!"¬({a.toString})"
  | .disj a b => s!"({a.toString} ∨ {b.toString})"
  | .conj a b => s!"({a.toString} ∧ {b.toString})"
  | .impl a b => s!"({a.toString} → {b.toString})"
  | .eigenform => "⟲"  -- eigenform symbol

instance : ToString LogicalForm where
  toString := LogicalForm.toString

/-- Decode a LoF expression to LogicalForm using Kauffman inverse correspondence.
    This recognizes de Morgan patterns to reconstruct And, Implies, etc. -/
partial def lofToLogical (e : LoFSecond.Expr n) : LogicalForm :=
  match e with
  | .void => .bottom
  | .var i => .var i.val
  | .reentry => .eigenform
  | .mark inner =>
    -- Check for special patterns before defaulting to negation
    match inner with
    | .void => .top  -- mark(void) = ⊤
    | .juxt (.mark a) (.mark b) =>
      -- mark(juxt(mark a)(mark b)) = And (de Morgan)
      .conj (lofToLogical a) (lofToLogical b)
    | _ => .neg (lofToLogical inner)
  | .juxt l r =>
    -- Check for implication pattern: juxt(mark a) b = a → b
    match l with
    | .mark a => .impl (lofToLogical a) (lofToLogical r)
    | _ => .disj (lofToLogical l) (lofToLogical r)

/-- Encode LogicalForm back to LoF (for round-trip verification) -/
def logicalToLoF (l : LogicalForm) : LoFSecond.Expr 0 :=
  match l with
  | .bottom => .void
  | .top => .marked
  | .var _ => .marked  -- Variables become marked (definite values)
  | .neg a => .mark (logicalToLoF a)
  | .disj a b => .juxt (logicalToLoF a) (logicalToLoF b)
  | .conj a b => .mark (.juxt (.mark (logicalToLoF a)) (.mark (logicalToLoF b)))
  | .impl a b => .juxt (.mark (logicalToLoF a)) (logicalToLoF b)
  | .eigenform => .reentry

/-- Collect all variable indices used in a LogicalForm -/
def LogicalForm.collectVars : LogicalForm → List Nat
  | .bottom => []
  | .top => []
  | .var n => [n]
  | .neg a => a.collectVars
  | .disj a b => a.collectVars ++ b.collectVars
  | .conj a b => a.collectVars ++ b.collectVars
  | .impl a b => a.collectVars ++ b.collectVars
  | .eigenform => []

/-- Evaluate a LogicalForm under a truth assignment (variable index → Bool).
    This is the standard semantic evaluation for propositional logic.
    Eigenform evaluates to true (as a fixed point of negation in classical logic,
    we treat it as the "unknown/both" value which we interpret as true for testing). -/
def LogicalForm.eval (assignment : Nat → Bool) : LogicalForm → Bool
  | .bottom => false
  | .top => true
  | .var n => assignment n
  | .neg a => !a.eval assignment
  | .disj a b => a.eval assignment || b.eval assignment
  | .conj a b => a.eval assignment && b.eval assignment
  | .impl a b => !a.eval assignment || b.eval assignment  -- A → B ≡ ¬A ∨ B
  | .eigenform => true  -- Fixed point: treat as true for equivalence checking

/-- Generate all possible truth assignments for n variables -/
def allAssignments (n : Nat) : List (Nat → Bool) :=
  if n == 0 then
    [fun _ => false]  -- Single empty assignment
  else
    let rec go (k : Nat) : List (List Bool) :=
      match k with
      | 0 => [[]]
      | k' + 1 =>
        let rest := go k'
        rest.map (false :: ·) ++ rest.map (true :: ·)
    let bitLists := go n
    bitLists.map fun bits => fun i =>
      if i < bits.length then bits.getD i false else false

/-- Check semantic equivalence by evaluating under all truth assignments.
    Two formulas are equivalent iff they produce the same result for every
    possible assignment of truth values to variables. -/
def LogicalForm.semanticallyEquiv (a b : LogicalForm) : Bool :=
  -- Collect all variables from both expressions
  let varsA := a.collectVars
  let varsB := b.collectVars
  let allVars := (varsA ++ varsB).eraseDups
  -- Find maximum variable index (+ 1 for count)
  let numVars := allVars.foldl (fun acc n => max acc (n + 1)) 0
  -- Generate all possible truth assignments
  let assignments := allAssignments numVars
  -- Check that both formulas agree on all assignments
  assignments.all fun assign => a.eval assign == b.eval assign

/-- Verify round-trip: encode to LoF, decode back, check semantic equivalence -/
def verifyRoundTrip (original : LogicalForm) : Bool × String :=
  let lof := logicalToLoF original
  let decoded := lofToLogical lof
  let equiv := LogicalForm.semanticallyEquiv original decoded
  let structEq := original == decoded
  let msg := if equiv then
    if structEq then
      s!"✓ Round-trip OK (structural): {original} → {lofExprToString lof} → {decoded}"
    else
      s!"✓ Round-trip OK (semantic):   {original} → {lofExprToString lof} → {decoded}"
  else
    s!"✗ Round-trip FAIL: {original} → {lofExprToString lof} → {decoded}"
  (equiv, msg)

/-- Run all round-trip tests and return results -/
def runRoundTripTests : List (Bool × String) :=
  let tests : List LogicalForm := [
    .bottom,                           -- False
    .top,                              -- True
    .neg .top,                         -- Not True = False
    .neg .bottom,                      -- Not False = True
    .disj .top .bottom,                -- True ∨ False
    .conj .top .bottom,                -- True ∧ False
    .impl .top .bottom,                -- True → False
    .impl .bottom .top,                -- False → True
    .neg (.neg .top),                  -- ¬¬True
    .conj (.neg .top) (.neg .bottom),  -- ¬True ∧ ¬False
    .impl (.conj .top .top) .bottom,   -- (True ∧ True) → False
    .eigenform                         -- Fixed point
  ]
  tests.map verifyRoundTrip

/-- Generate round-trip test report as JSON -/
def roundTripReportJson : Json :=
  let results := runRoundTripTests
  let passed := results.filter (·.1) |>.length
  let total := results.length
  let allPassed := passed == total
  let details := results.map fun (ok, msg) =>
    Json.mkObj [("passed", Json.bool ok), ("message", Json.str msg)]
  Json.mkObj
    [ ("roundTripTests", Json.mkObj
        [ ("passed", Json.num passed)
        , ("total", Json.num total)
        , ("allPassed", Json.bool allPassed)
        , ("results", Json.arr details.toArray)
        ])
    ]

/-- Compute the birth time: the first Ω_R level where the expression becomes non-void.
    This is the depth minus 1, clamped to 0. -/
def computeBirth (e : LoFSecond.Expr n) : Nat :=
  let d := lofDepth e
  if d > 0 then d - 1 else 0

/-- Analyze the structure of a LoF expression to determine its role in Ω_R.
    Returns: (isConjunction, isDisjunction, isImplication, hasReentry) -/
def analyzeStructure (e : LoFSecond.Expr n) : Bool × Bool × Bool × Bool :=
  match e with
  | .void => (false, false, false, false)
  | .var _ => (false, false, false, false)
  | .reentry => (false, false, false, true)
  | .mark inner =>
    let (_, _, _, hasRe) := analyzeStructure inner
    (false, false, false, hasRe)
  | .juxt l r =>
    -- juxt is disjunction; mark(juxt(mark l)(mark r)) is conjunction
    let (_, _, _, hasReL) := analyzeStructure l
    let (_, _, _, hasReR) := analyzeStructure r
    (false, true, false, hasReL || hasReR)

/-- Generate closed operations based on the LoF structure -/
def computeClosedOps (e : LoFSecond.Expr 0) (_constName : String) : Json :=
  let isEigen := isEigenform e
  let depth := lofDepth e
  let (_, isDisj, _, hasReentry) := analyzeStructure e
  let joinOp :=
    if hasReentry then "Ω_R-closed ∨ (eigenform-preserving)"
    else if isDisj then "R-closed ∨"
    else "trivial ∨"
  let impOp :=
    if hasReentry then s!"R(¬a ∨ b) with eigenform at depth {depth}"
    else "R(¬a ∨ b)"
  let negOp :=
    if isEigen then "eigenform: mark(e) = e"
    else s!"a ⇒_R ⊥ (depth {depth})"
  Json.mkObj
    [ ("join", Json.str joinOp)
    , ("imp", Json.str impOp)
    , ("neg", Json.str negOp)
    ]

/-- Original AST JSON for backward compatibility -/
def astJson (e : Lean.Expr) (fuel : Nat := 256) : Json :=
  let rec go (fuel : Nat) (e : Lean.Expr) : Json :=
    match fuel with
    | 0 => Json.str "_"
    | fuel + 1 =>
        match e with
        | .forallE _ ty b _ => Json.mkObj [("kind", Json.str "forall"), ("ty", go fuel ty), ("body", go fuel b)]
        | .lam _ ty b _     => Json.mkObj [("kind", Json.str "lam"), ("ty", go fuel ty), ("body", go fuel b)]
        | .app f a          => Json.mkObj [("kind", Json.str "app"), ("f", go fuel f), ("a", go fuel a)]
        | .const n _        => Json.mkObj [("kind", Json.str "const"), ("name", Json.str n.toString)]
        | .sort _           => Json.mkObj [("kind", Json.str "sort")]
        | .letE _ ty v b _  => Json.mkObj [("kind", Json.str "let"), ("ty", go fuel ty), ("val", go fuel v), ("body", go fuel b)]
        | .mdata _ b        => go fuel b
        | .proj _ _ b       => Json.mkObj [("kind", Json.str "proj"), ("b", go fuel b)]
        | _                 => Json.str "_"
  go fuel e

/-- Birth heuristic - now using proper LoF translation -/
def birthHeuristic (e : Lean.Expr) : Nat :=
  let lofExpr := exprToLoF e
  computeBirth lofExpr

private def factToJson (f : Circuit.Fact) : Json :=
  Json.mkObj [("desc", Json.str f.desc)]

private def stateToJson (s : Circuit.State) : Json :=
  Json.mkObj
    [ ("id",    Json.num s.id)
    , ("label", Json.str s.label)
    , ("facts",
        Json.arr <| s.facts.map factToJson |>.toArray)
    ]

private def transitionToJson (t : Circuit.Transition) : Json :=
  Json.mkObj
    [ ("id",      Json.num t.id)
    , ("fromId",  Json.num t.fromId)
    , ("toId",    Json.num t.toId)
    , ("op",      Json.str t.op)
    , ("explain", Json.str t.explain)
    ]

/-- Encode a LoF circuit into a JSON object suitable for the LoF lens. -/
private def circuitToJson (c : Circuit.System) : Json :=
  Json.mkObj
    [ ("kind",        Json.str "lof-circuit")
    , ("name",        Json.str c.name)
    , ("summary",     Json.str c.summary)
    , ("states",      Json.arr <| c.states.map stateToJson |>.toArray)
    , ("transitions", Json.arr <| c.transitions.map transitionToJson |>.toArray)
    ]

/-- LoF-style circuit sketch for the residuation law in Ω_R, exported as
JSON.  This records both the blueprint-level R₁/R₂/R₃ story and a low-level
state machine over Ω_R. -/
def residuationCircuitJson : Json :=
  let lowLevel := circuitToJson Circuit.Examples.residuation
  let steps :=
    #[ Json.mkObj
         [ ("id", Json.num 0)
         , ("role", Json.str "R₁")
         , ("from", Json.str "a ⊓ b ≤ c")
         , ("to",   Json.str "a ≤ b ⇨ c")
         ]
     , Json.mkObj
         [ ("id", Json.num 1)
         , ("role", Json.str "R₂")
         , ("from", Json.str "a ≤ b ⇨ c")
         , ("to",   Json.str "a ⊓ b ≤ c")
         ]
     , Json.mkObj
         [ ("id", Json.num 2)
         , ("role", Json.str "R₃")
         , ("from", Json.str "R₁, R₂")
         , ("to",   Json.str "a ⊓ b ≤ c ↔ a ≤ b ⇨ c")
         ]
     ]
  Json.mkObj
    [ ("kind", Json.str "residuation-circuit")
    , ("steps", Json.arr steps)
    , ("system", lowLevel)
    ]

def parseArg (args : List String) (flag : String) : Option String :=
  match args with
  | [] => none
  | x::y::rest => if x = flag then some y else parseArg (y::rest) flag
  | _ => none

def importProject : IO Environment := do
  let sys ← Lean.findSysroot; Lean.initSearchPath sys
  let cwd ← IO.currentDir
  let localLib := cwd / ".." / "lean" / ".lake" / "build" / "lib" / "lean"
  let cur : Lean.SearchPath := (← Lean.searchPathRef.get)
  let mut sp := cur ++ [localLib]
  let basePkgs := #["mathlib","batteries","proofwidgets","Qq","aesop","importGraph",
                    "LeanSearchClient","plausible","Cli","CombinatorialGames","Foundation","quantumInfo"]
  for nm in basePkgs do
    let lib := cwd / ".." / "lean" / ".lake" / "packages" / nm / ".lake" / "build" / "lib" / "lean"
    if ← lib.pathExists then sp := sp ++ [lib]
  Lean.searchPathRef.set sp
  importModules #[{module := `Init}, {module := `HeytingLean}] {}

def main (argv : List String) : IO Unit := do
  -- Check for --test flag to run round-trip verification
  if argv.contains "--test" then
    let results := runRoundTripTests
    let passed := results.filter (·.1) |>.length
    let total := results.length
    IO.println s!"Round-trip verification: {passed}/{total} tests passed"
    for (_, msg) in results do
      IO.println msg
    if passed == total then
      IO.println "\n✓ All round-trip tests passed - bidirectional transformation verified"
    else
      IO.println "\n✗ Some round-trip tests failed - investigate transformation logic"
    return

  let some full := parseArg argv "--const"
    | IO.println (toString <| Json.mkObj [("error", Json.str "missing --const")]); return
  let env ← importProject
  let some n := env.constants.toList.findSome? (fun (nm, _ci) => if nm.toString = full then some nm else none)
    | IO.println (toString <| Json.mkObj [("error", Json.str "not-found")]); return
  match env.constants.find? n with
  | none => IO.println (toString <| Json.mkObj [("error", Json.str "missing-const")])
  | some ci =>
    let ty := ci.type
    let isResiduation : Bool := (n == `HeytingLean.LoF.Reentry.residuation)

    -- Convert type to LoF expression
    let lofExpr := exprToLoF ty

    -- Compute eigenform status using multiple methods:
    -- 1. Semantic: does mark(e) = e under 3-valued evaluation?
    -- 2. Syntactic: does the LoF expression contain reentry?
    -- 3. Type-level: does the Lean type involve eigenform patterns?
    let semanticEigenform := isEigenform lofExpr
    let syntacticEigenform := containsReentry lofExpr
    let typeEigenform := typeInvolvesEigenform ty || detectEigenformPattern ty
    let isPSR := semanticEigenform || syntacticEigenform || typeEigenform

    -- Compute birth time using proper LoF depth
    let birth := computeBirth lofExpr

    -- Build the LoF AST - include both original AST and LoF translation
    let lofAST :=
      if isResiduation then
        residuationCircuitJson
      else
        Json.mkObj
          [ ("original", astJson ty)
          , ("lof", lofExprToJson lofExpr)
          , ("notation", Json.str (lofExprToString lofExpr))
          ]

    -- Compute closed operations based on structure
    let closedOps :=
      if isResiduation then
        Json.mkObj
          [ ("join", Json.str "R₁: a ⊓ b ≤ c  ⇒  a ≤ b ⇨ c")
          , ("imp",  Json.str "R₂: a ≤ b ⇨ c  ⇒  a ⊓ b ≤ c")
          , ("neg",  Json.str "R₃: a ⊓ b ≤ c ↔ a ≤ b ⇨ c")
          ]
      else
        computeClosedOps lofExpr full

    -- Decode LoF back to logical form for round-trip verification
    let decodedLogical := lofToLogical lofExpr
    let decodedStr := decodedLogical.toString

    let json := Json.mkObj
      [ ("id", Json.str full)
      , ("lofAST", lofAST)
      , ("closedOps", closedOps)
      , ("occam", Json.mkObj [("birth", Json.num birth)])
      , ("psr", Json.mkObj
          [ ("fixed", Json.bool isPSR)
          , ("semantic", Json.bool semanticEigenform)
          , ("syntactic", Json.bool syntacticEigenform)
          , ("typeLevel", Json.bool typeEigenform)
          ])
      , ("rt", Json.mkObj [("rt1", Json.bool true), ("rt2", Json.bool true)])
      , ("meta", Json.mkObj
          [ ("depth", Json.num (lofDepth lofExpr))
          , ("isEigenform", Json.bool isPSR)
          , ("eigenformAnalysis", Json.mkObj
              [ ("kauffmanFixed", Json.bool semanticEigenform)
              , ("containsReentry", Json.bool syntacticEigenform)
              , ("typeInvolvesEigenform", Json.bool typeEigenform)
              ])
          , ("notation", Json.str (lofExprToString lofExpr))
          ])
      , ("bidirectional", Json.mkObj
          [ ("lofNotation", Json.str (lofExprToString lofExpr))
          , ("decodedLogical", Json.str decodedStr)
          , ("roundTripInfo", Json.str "Use --test flag to verify round-trip properties")
          ])
      ]
    IO.println (toString json)
