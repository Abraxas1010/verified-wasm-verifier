import Lean

namespace HeytingLean.HeytingVeil.DSL

inductive HvType
  | int
  | bool
  deriving Repr, DecidableEq, Inhabited

inductive Expr
  | var (name : String)
  | intLit (n : Int)
  | boolLit (b : Bool)
  | add (lhs rhs : Expr)
  | le (lhs rhs : Expr)
  | eq (lhs rhs : Expr)
  | not (e : Expr)
  deriving Repr, DecidableEq, Inhabited

inductive Stmt
  | skip
  | assign (name : String) (rhs : Expr)
  | seq (s1 s2 : Stmt)
  | if_ (cond : Expr) (then_ else_ : Stmt)
  | return (e : Expr)
  deriving Repr, DecidableEq, Inhabited

structure Action where
  name : String
  body : Stmt
  deriving Repr, DecidableEq

structure Module where
  name : String
  stateVars : List (String × HvType)
  init : Action
  next : Action
  safety : List Expr
  liveness : List Expr
  invariants : List Expr := []
  reachable : List Expr := []
  safetyLabels : List String := []
  livenessLabels : List String := []
  invariantLabels : List String := []
  reachableLabels : List String := []
  actionNames : List String := []
  hasAfterInit : Bool := false
  wfActions : List String := []
  sfActions : List String := []
  wfConditions : List Expr := []
  sfConditions : List Expr := []
  backendHint : String := "lambdair_minic_c"
  backendTarget : String := "c"
  backendDialect : String := "minic"
  packageCertificate : String := "cab_export_v2"
  packageProfile : String := "dev"
  explicitSafetyCount : Nat := 0
  explicitLivenessCount : Nat := 0
  explicitInvariantCount : Nat := 0
  explicitReachableCount : Nat := 0
  deriving Repr, DecidableEq

structure ParsedModule where
  source : String
  mod : Module
  deriving Repr, DecidableEq

private def defaultInit : Action :=
  { name := "Init", body := .skip }

private def defaultNext : Action :=
  { name := "Next", body := .skip }

private def parseHeaderName (line : String) : Except String String :=
  let trimmed := line.trim
  if trimmed.startsWith "module " then
    let name := (trimmed.drop "module ".length).trim
    if name.isEmpty then
      .error "module name is empty"
    else
      .ok name
  else if trimmed.startsWith "heytingveil module " then
    let name := (trimmed.drop "heytingveil module ".length).trim
    if name.isEmpty then
      .error "module name is empty"
    else
      .ok name
  else
    .error "expected first line `module <name>` or `heytingveil module <name>`"

private def countPrefix (lines : List String) (pfx : String) : Nat :=
  lines.foldl
    (fun acc line =>
      let trimmed := line.trim
      if trimmed.startsWith pfx then acc + 1 else acc)
    0

private def extractBracketLabel (line pfx : String) : Option String :=
  let trimmed := line.trim
  if trimmed.startsWith pfx then
    match (trimmed.drop pfx.length).splitOn "]" with
    | [] => none
    | label :: _ =>
        let t := label.trim
        if t.isEmpty then none else some t
  else
    none

private def extractBracketPayload (line pfx : String) : Option String :=
  let trimmed := line.trim
  if trimmed.startsWith pfx then
    match (trimmed.drop pfx.length).splitOn "]" with
    | [] => none
    | _ :: rest =>
        let payload := (String.intercalate "]" rest).trim
        if payload.isEmpty then none else some payload
  else
    none

private def collectBracketLabels (lines : List String) (pfx : String) : List String :=
  lines.foldr
    (fun line acc =>
      match extractBracketLabel line pfx with
      | some x => x :: acc
      | none => acc)
    []

private def parseTaggedValue (line tag : String) : Option String :=
  let trimmed := line.trim
  if trimmed.startsWith tag then
    some ((trimmed.drop tag.length).trim)
  else
    none

private def normalizeTokenSeparators (s : String) : String :=
  let s1 := s.replace "{" " "
  let s2 := s1.replace "}" " "
  let s3 := s2.replace "=" " "
  s3.replace ":" " "

private def parsePrefixedName (line pfx : String) : Option String :=
  let trimmed := line.trim
  if trimmed.startsWith pfx then
    let rest := normalizeTokenSeparators ((trimmed.drop pfx.length).trim)
    let toks0 := rest.splitOn " "
    let toks1 := toks0.map String.trim
    let toks := toks1.filter (fun t => !t.isEmpty)
    match toks with
    | [] => none
    | name :: _ => some name
  else
    none

private def collectPrefixedNames (lines : List String) (pfx : String) : List String :=
  lines.foldr
    (fun line acc =>
      match parsePrefixedName line pfx with
      | some x => x :: acc
      | none => acc)
    []

private def hasPrefixLine (lines : List String) (pfx : String) : Bool :=
  lines.any (fun line => line.trim.startsWith pfx)

private def lastTaggedValue (lines : List String) (tag : String) : Option String :=
  lines.foldl
    (fun acc line =>
      match parseTaggedValue line tag with
      | some v => some v
      | none => acc)
    none

private def canonicalBackendHint (raw : String) : String :=
  if raw = "lean_lambdair_minic_c" then "lambdair_minic_c" else raw

private def replicatedTruth (count : Nat) : List Expr :=
  if count = 0 then [.boolLit true] else List.replicate count (.boolLit true)

private def parseHvTypeToken (tok : String) : Option HvType :=
  match tok.trim with
  | "Nat" | "Int" | "nat" | "int" => some .int
  | "Bool" | "bool" => some .bool
  | _ => none

private def splitWhitespaceTokens (raw : String) : List String :=
  (normalizeTokenSeparators raw).splitOn " "
    |>.map String.trim
    |>.filter (fun t => !t.isEmpty)

private def parseStateVarBody (raw : String) : Option (String × HvType) :=
  match splitWhitespaceTokens raw with
  | name :: ty :: _ =>
      match parseHvTypeToken ty with
      | some hvTy =>
          if name.isEmpty then none else some (name, hvTy)
      | none => none
  | _ => none

private def parseStateVarLine (line : String) : Option (String × HvType) :=
  let t := line.trim
  if t.startsWith "immutable individual " then
    parseStateVarBody (t.drop "immutable individual ".length)
  else if t.startsWith "individual " then
    parseStateVarBody (t.drop "individual ".length)
  else if t.startsWith "ghost " then
    parseStateVarBody (t.drop "ghost ".length)
  else
    none

private def collectStateVars (lines : List String) : List (String × HvType) :=
  lines.foldr
    (fun line acc =>
      match parseStateVarLine line with
      | some x => x :: acc
      | none => acc)
    []

private def stripOuterParens (raw : String) : String :=
  let t := raw.trim
  if t.length >= 2 && t.startsWith "(" && t.endsWith ")" then
    (t.drop 1).dropRight 1
  else
    t

private def splitBinaryOnce (s op : String) : Option (String × String) :=
  let parts := s.splitOn op
  match parts with
  | [] => none
  | [_] => none
  | lhs :: rhsParts =>
      let lhs := lhs.trim
      let rhs := (String.intercalate op rhsParts).trim
      if lhs.isEmpty || rhs.isEmpty then none else some (lhs, rhs)

private def parseAtomExpr (raw : String) : Expr :=
  let t := stripOuterParens raw
  if t == "true" then
    .boolLit true
  else if t == "false" then
    .boolLit false
  else
    match t.toInt? with
    | some n => .intLit n
    | none =>
        if t.isEmpty then .boolLit true else .var t

private partial def parseExprText (raw : String) : Expr :=
  let t := stripOuterParens raw
  if t.startsWith "not " then
    .not (parseExprText (t.drop 4))
  else
    match splitBinaryOnce t "<=" with
    | some (lhs, rhs) => .le (parseExprText lhs) (parseExprText rhs)
    | none =>
        match splitBinaryOnce t ">=" with
        | some (lhs, rhs) => .le (parseExprText rhs) (parseExprText lhs)
        | none =>
            match splitBinaryOnce t "=" with
            | some (lhs, rhs) => .eq (parseExprText lhs) (parseExprText rhs)
            | none =>
                match splitBinaryOnce t ">" with
                | some (lhs, rhs) => .not (.le (parseExprText lhs) (parseExprText rhs))
                | none =>
                    match splitBinaryOnce t "<" with
                    | some (lhs, rhs) => .not (.le (parseExprText rhs) (parseExprText lhs))
                    | none =>
                        let terms := (t.splitOn "+").map parseAtomExpr
                        match terms with
                        | [] => .boolLit true
                        | first :: rest => rest.foldl (fun acc e => .add acc e) first

private def collectClauseExprs (lines : List String) (pfx : String) : List Expr :=
  lines.foldr
    (fun line acc =>
      match extractBracketPayload line pfx with
      | some payload => parseExprText payload :: acc
      | none => acc)
    []

private def clauseExprsWithFallback (lines : List String) (pfx : String) : List Expr :=
  let count := countPrefix lines pfx
  let parsed := collectClauseExprs lines pfx
  if parsed.isEmpty then replicatedTruth count else parsed

private def parseEnabledExpr (raw : String) : Option Expr :=
  let t := stripOuterParens raw
  if t.startsWith "ENABLED(" && t.endsWith ")" then
    let prefixLen := "ENABLED(".length
    let rawAction := (t.drop prefixLen).dropRight 1
    let action := rawAction.trim
    if action.isEmpty then none else some (.var s!"enabled_{action}")
  else
    none

private def parseFairnessExpr (raw : String) : Expr :=
  match parseEnabledExpr raw with
  | some e => e
  | none => parseExprText raw

private def collectFairnessExprs (lines : List String) (pfx : String) : List Expr :=
  lines.foldr
    (fun line acc =>
      match extractBracketPayload line pfx with
      | some payload => parseFairnessExpr payload :: acc
      | none => acc)
    []

/--
Extremely small parser for sprint bootstrap:
first line must be `module <name>` or `heytingveil module <name>`.
The rest of the DSL is scanned for key clause families and metadata.
-/
def parseText (src : String) : Except String ParsedModule :=
  let lines := src.splitOn "\n"
  match lines with
  | [] => .error "empty specification"
  | first :: _ =>
      match parseHeaderName first with
      | .error e => .error e
      | .ok name =>
          let safetyCount := countPrefix lines "safety["
          let livenessCount := countPrefix lines "liveness["
          let invariantCount := countPrefix lines "invariant["
          let reachableCount := countPrefix lines "reachable["
          let safetyLabels := collectBracketLabels lines "safety["
          let livenessLabels := collectBracketLabels lines "liveness["
          let invariantLabels := collectBracketLabels lines "invariant["
          let reachableLabels := collectBracketLabels lines "reachable["
          let safetyExprs := clauseExprsWithFallback lines "safety["
          let livenessExprs := clauseExprsWithFallback lines "liveness["
          let invariantExprs := clauseExprsWithFallback lines "invariant["
          let reachableExprs := clauseExprsWithFallback lines "reachable["
          let stateVars := collectStateVars lines
          let actionNames := collectPrefixedNames lines "action "
          let hasAfterInit := hasPrefixLine lines "after_init"
          let wfActions := collectBracketLabels lines "WF["
          let sfActions := collectBracketLabels lines "SF["
          let wfConditions := collectFairnessExprs lines "WF["
          let sfConditions := collectFairnessExprs lines "SF["
          let backendHint :=
            canonicalBackendHint <| (lastTaggedValue lines "route:").getD "lambdair_minic_c"
          let backendTarget := (lastTaggedValue lines "target:").getD "c"
          let backendDialect := (lastTaggedValue lines "dialect:").getD "minic"
          let packageCertificate := (lastTaggedValue lines "certificate:").getD "cab_export_v2"
          let packageProfile := (lastTaggedValue lines "profile:").getD "dev"
          let m : Module :=
            { name := name
              stateVars := stateVars
              init := defaultInit
              next := defaultNext
              safety := safetyExprs
              liveness := livenessExprs
              invariants := invariantExprs
              reachable := reachableExprs
              safetyLabels := safetyLabels
              livenessLabels := livenessLabels
              invariantLabels := invariantLabels
              reachableLabels := reachableLabels
              actionNames := actionNames
              hasAfterInit := hasAfterInit
              wfActions := wfActions
              sfActions := sfActions
              wfConditions := wfConditions
              sfConditions := sfConditions
              backendHint := backendHint
              backendTarget := backendTarget
              backendDialect := backendDialect
              packageCertificate := packageCertificate
              packageProfile := packageProfile
              explicitSafetyCount := safetyCount
              explicitLivenessCount := livenessCount
              explicitInvariantCount := invariantCount
              explicitReachableCount := reachableCount }
          .ok { source := src, mod := m }

/--
A deterministic text snapshot used by downstream emit/check/verify/package commands.
-/
def canonicalSnapshot (p : ParsedModule) : String :=
  s!"name={p.mod.name};backend={p.mod.backendHint};target={p.mod.backendTarget};dialect={p.mod.backendDialect};cert={p.mod.packageCertificate};profile={p.mod.packageProfile};state={p.mod.stateVars.length};actions={p.mod.actionNames.length};after_init={p.mod.hasAfterInit};wf={p.mod.wfActions.length};sf={p.mod.sfActions.length};safety={p.mod.explicitSafetyCount};liveness={p.mod.explicitLivenessCount};invariant={p.mod.explicitInvariantCount};reachable={p.mod.explicitReachableCount}"

end HeytingLean.HeytingVeil.DSL
