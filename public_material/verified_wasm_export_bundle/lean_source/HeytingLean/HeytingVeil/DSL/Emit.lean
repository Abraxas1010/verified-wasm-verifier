import HeytingLean.HeytingVeil.DSL.Schema

namespace HeytingLean.HeytingVeil.DSL

structure LeanArtifact where
  moduleName : String
  code : String
  contentHash : UInt64
  deriving Repr, DecidableEq

private def hashText (s : String) : UInt64 :=
  s.foldl (fun acc c => acc * 16777619 + c.toNat.toUInt64 + 1469598103934665603) 2166136261

private def renderStringList (xs : List String) : String :=
  let body := String.intercalate ", " (xs.map (fun x => s!"\"{x}\""))
  s!"[{body}]"

private def hvTypeTag : HvType → String
  | .int => "int"
  | .bool => "bool"

private def renderStateVarList (xs : List (String × HvType)) : String :=
  let body :=
    String.intercalate ", "
      (xs.map (fun (name, ty) => s!"(\"{name}\", \"{hvTypeTag ty}\")"))
  s!"[{body}]"

private def sanitizeIdent (s : String) : String :=
  let mapped := s.map (fun c => if c.isAlphanum then c else '_')
  let trimmed :=
    if mapped.data.any (fun c => c != '_') then mapped else "unnamed"
  match trimmed.data with
  | [] => "unnamed"
  | c :: _ =>
      if c.isDigit then s!"id_{trimmed}" else trimmed

private def stateKey (name : String) : String :=
  s!"\"{name.replace "\"" "_"}\""

private partial def renderIntExpr (e : Expr) : String :=
  match e with
  | .var name => s!"s {stateKey name}"
  | .intLit n => s!"({n} : Int)"
  | .boolLit true => "(1 : Int)"
  | .boolLit false => "(0 : Int)"
  | .add lhs rhs => s!"({renderIntExpr lhs} + {renderIntExpr rhs})"
  | .le lhs rhs =>
      s!"(if {renderIntExpr lhs} <= {renderIntExpr rhs} then (1 : Int) else (0 : Int))"
  | .eq lhs rhs =>
      s!"(if {renderIntExpr lhs} = {renderIntExpr rhs} then (1 : Int) else (0 : Int))"
  | .not inner =>
      s!"(if {renderIntExpr inner} = (0 : Int) then (1 : Int) else (0 : Int))"

private def renderPropExpr (e : Expr) : String :=
  s!"({renderIntExpr e} != (0 : Int))"

private def nthExprOrTruth : List Expr → Nat → Expr
  | [], _ => .boolLit true
  | e :: _, 0 => e
  | _ :: es, n + 1 => nthExprOrTruth es n

private def propertyDeclLinesAux (pfx : String) (exprs : List Expr) :
    Nat → List String → List String
  | _, [] => []
  | idx, label :: rest =>
      let ident := sanitizeIdent label
      let expr := nthExprOrTruth exprs idx
      s!"def {pfx}_{ident} : State -> Prop := fun s => {renderPropExpr expr}" ::
        propertyDeclLinesAux pfx exprs (idx + 1) rest

private def propertyDeclLines (pfx : String) (labels : List String) (exprs : List Expr) : List String :=
  propertyDeclLinesAux pfx exprs 0 labels

private def registryLine (name : String) (pfx : String) (labels : List String) : String :=
  let entries :=
    labels.map (fun label =>
      let ident := sanitizeIdent label
      s!"(\"{label}\", {pfx}_{ident})")
  let body := String.intercalate ", " entries
  s!"def {name} : List (String × (State -> Prop)) := [{body}]"

def emit (em : ElaboratedModule) : LeanArtifact :=
  let safetyLabelsRendered := renderStringList em.parsed.mod.safetyLabels
  let livenessLabelsRendered := renderStringList em.parsed.mod.livenessLabels
  let invariantLabelsRendered := renderStringList em.parsed.mod.invariantLabels
  let reachableLabelsRendered := renderStringList em.parsed.mod.reachableLabels
  let actionNamesRendered := renderStringList em.parsed.mod.actionNames
  let stateVarsRendered := renderStateVarList em.parsed.mod.stateVars
  let wfRendered := renderStringList em.parsed.mod.wfActions
  let sfRendered := renderStringList em.parsed.mod.sfActions
  let safetyDecls := propertyDeclLines "safety" em.parsed.mod.safetyLabels em.parsed.mod.safety
  let livenessDecls := propertyDeclLines "liveness" em.parsed.mod.livenessLabels em.parsed.mod.liveness
  let invariantDecls := propertyDeclLines "invariant" em.parsed.mod.invariantLabels em.parsed.mod.invariants
  let reachableDecls := propertyDeclLines "reachable" em.parsed.mod.reachableLabels em.parsed.mod.reachable
  let fairnessDecls :=
    propertyDeclLines "wf" em.parsed.mod.wfActions em.parsed.mod.wfConditions ++
      propertyDeclLines "sf" em.parsed.mod.sfActions em.parsed.mod.sfConditions
  let safetyRegistryLine := registryLine "safetyRegistry" "safety" em.parsed.mod.safetyLabels
  let livenessRegistryLine := registryLine "livenessRegistry" "liveness" em.parsed.mod.livenessLabels
  let invariantRegistryLine := registryLine "invariantRegistry" "invariant" em.parsed.mod.invariantLabels
  let reachableRegistryLine := registryLine "reachableRegistry" "reachable" em.parsed.mod.reachableLabels
  let wfRegistryLine := registryLine "wfRegistry" "wf" em.parsed.mod.wfActions
  let sfRegistryLine := registryLine "sfRegistry" "sf" em.parsed.mod.sfActions
  let scaffoldLines : List String :=
    [ "abbrev State : Type := String -> Int"
    , "def Init : State -> Prop := fun _ => True"
    , "def Next : State -> State -> Prop := fun _ _ => True"
    , "def Spec : Prop := True"
    ] ++ safetyDecls ++ livenessDecls ++ invariantDecls ++ reachableDecls ++ fairnessDecls ++
      [ safetyRegistryLine
      , livenessRegistryLine
      , invariantRegistryLine
      , reachableRegistryLine
      , wfRegistryLine
      , sfRegistryLine
      ]
  let code :=
    String.intercalate "\n" <|
      ([ s!"namespace HeytingLean.HeytingVeil.Generated.{em.parsed.mod.name}"
      ] ++ scaffoldLines ++
      [ s!"def moduleName : String := \"{em.parsed.mod.name}\""
      , s!"def stateVars : List (String × String) := {stateVarsRendered}"
      , "def stateSemantics : String := \"typed_machine_state_v1\""
      , "def traceSemantics : String := \"nat_indexed_trace_v1\""
      , s!"def stateVarCount : Nat := {em.parsed.mod.stateVars.length}"
      , s!"def backendHint : String := \"{em.parsed.mod.backendHint}\""
      , s!"def backendTarget : String := \"{em.parsed.mod.backendTarget}\""
      , s!"def backendDialect : String := \"{em.parsed.mod.backendDialect}\""
      , s!"def packageCertificate : String := \"{em.parsed.mod.packageCertificate}\""
      , s!"def packageProfile : String := \"{em.parsed.mod.packageProfile}\""
      , s!"def safetyLabels : List String := {safetyLabelsRendered}"
      , s!"def livenessLabels : List String := {livenessLabelsRendered}"
      , s!"def invariantLabels : List String := {invariantLabelsRendered}"
      , s!"def reachableLabels : List String := {reachableLabelsRendered}"
      , s!"def actionNames : List String := {actionNamesRendered}"
      , s!"def hasAfterInit : Bool := {if em.parsed.mod.hasAfterInit then "true" else "false"}"
      , s!"def wfActions : List String := {wfRendered}"
      , s!"def sfActions : List String := {sfRendered}"
      , s!"def hasWeakFairness : Bool := {if em.parsed.mod.wfActions.isEmpty then "false" else "true"}"
      , s!"def hasStrongFairness : Bool := {if em.parsed.mod.sfActions.isEmpty then "false" else "true"}"
      , s!"def explicitSafetyCount : Nat := {em.parsed.mod.explicitSafetyCount}"
      , s!"def explicitLivenessCount : Nat := {em.parsed.mod.explicitLivenessCount}"
      , s!"def explicitInvariantCount : Nat := {em.parsed.mod.explicitInvariantCount}"
      , s!"def explicitReachableCount : Nat := {em.parsed.mod.explicitReachableCount}"
      , "end HeytingLean.HeytingVeil.Generated"
      ])
  { moduleName := em.parsed.mod.name
    code := code
    contentHash := hashText code }

/-- Sprint obligation `HV.DSL.EmitDeterministic`. -/
theorem emitDeterministic {e1 e2 : ElaboratedModule} (h : e1 = e2) :
    emit e1 = emit e2 := by
  cases h
  rfl

end HeytingLean.HeytingVeil.DSL
