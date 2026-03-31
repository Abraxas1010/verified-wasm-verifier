import Lean.Data.Json

namespace HeytingLean.HeytingVeil.Verify

open Lean

structure CTIRecord where
  invariantId : String
  stateFingerprint : String
  reason : String
  clauseFamily : String := "invariant"
  clauseLabel : String := ""
  stateVars : List String := []
  deriving Repr, DecidableEq

def toJson (c : CTIRecord) : Json :=
  let stateVarsJson := Json.arr (c.stateVars.map Json.str).toArray
  Json.mkObj
    [ ("invariant_id", Json.str c.invariantId)
    , ("state_fingerprint", Json.str c.stateFingerprint)
    , ("reason", Json.str c.reason)
    , ("clause_family", Json.str c.clauseFamily)
    , ("clause_label", Json.str c.clauseLabel)
    , ("state_vars", stateVarsJson)
    ]

/-- Sprint obligation `HV.Verify.CTIReplayDeterministic` (renderer determinism). -/
theorem ctiRenderDeterministic (c1 c2 : CTIRecord) (h : c1 = c2) :
    toJson c1 = toJson c2 := by
  cases h
  rfl

end HeytingLean.HeytingVeil.Verify
