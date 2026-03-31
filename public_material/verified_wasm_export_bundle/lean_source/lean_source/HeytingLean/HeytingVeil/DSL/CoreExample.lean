import HeytingLean.HeytingVeil.DSL.Emit

namespace HeytingLean.HeytingVeil.DSL

def coreSpecText : String :=
  String.intercalate "\n"
    [ "heytingveil module transfer_guard"
    , "state balance : int"
    , "state guard : bool"
    , "action Init == balance := 0"
    , "action Next == balance := balance + 1"
    , "fairness"
    , "  WF[Next] ENABLED(Next)"
    , "safety[bounded_total] balance >= 0"
    , "invariant[conservation] balance >= 0"
    , "reachable[progress_seen] balance >= 0"
    , "backend {"
    , "  target: c"
    , "  route: lean_lambdair_minic_c"
    , "  dialect: minic"
    , "}"
    , "package {"
    , "  certificate: cab_export_v2"
    , "  profile: prod_strict"
    , "}"
    ]

def coreParsed : ParsedModule :=
  match parseText coreSpecText with
  | .ok pm => pm
  | .error _ =>
      { source := coreSpecText
        mod :=
          { name := "transfer_guard"
            stateVars := []
            init := { name := "Init", body := .skip }
            next := { name := "Next", body := .skip }
            safety := [.boolLit true]
            liveness := [.boolLit true] } }

def coreModule : Module :=
  { coreParsed.mod with
    stateVars := [("balance", .int), ("guard", .bool)]
    safety := [.le (.intLit 0) (.var "balance")]
    liveness := [.boolLit true]
    invariants := [.le (.intLit 0) (.var "balance")]
    reachable := [.boolLit true]
    wfActions := ["Next"] }

def coreElaborated : Except String ElaboratedModule :=
  elaborate defaultProfile { coreParsed with mod := coreModule }

def coreArtifact : Except String LeanArtifact := do
  let em ← coreElaborated
  pure (emit em)

end HeytingLean.HeytingVeil.DSL
