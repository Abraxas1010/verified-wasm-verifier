import HeytingLean.Bridge.AgentPMT.Types

namespace HeytingLean.Bridge.AgentPMT

/-- Python: routers/auth.py:425-460. -/
def checkAuth (req : Request) (expectedProductId : String)
    (jwtProductId : Option String) : AuthDecision :=
  if req.adminKeyValid then
    .bypass
  else if !req.hasBearerToken then
    .rejected "Missing Authorization header"
  else
    match jwtProductId with
    | none => .rejected "Invalid or expired token"
    | some pid =>
        if pid = expectedProductId then
          .authenticated pid ""
        else
          .rejected s!"Product ID mismatch: {pid} != {expectedProductId}"

/-- Python: routers/auth.py:368-377. -/
def productIdStringMatch (tokenProductId expectedProductId : String) : Bool :=
  tokenProductId = expectedProductId

/-- Python: routers/middleware/credential_injection.py:90-105. -/
def selectCredentialSource (req : Request) : CredentialSource :=
  if req.hasInternalCredHeader then
    .internalHeader
  else if req.hasAutoloadHeaders then
    .localAutoload
  else
    .none

end HeytingLean.Bridge.AgentPMT
