import HeytingLean.Bridge.AgentPMT.Types

namespace HeytingLean.Bridge.AgentPMT

/-- Python: routers/credential_resolver.py:464-481, 523-542. -/
def mergeBindings (existing new_ : CredentialBinding) : CredentialBinding :=
  if existing.tier ≤ new_.tier then new_ else existing

/-- Python: routers/credential_resolver.py:460-558. -/
structure ResolvedCredentials where
  payloads : List CredentialBinding
  headers : List (String × String)
  deriving DecidableEq, Repr

/-- Python: routers/credential_resolver.py:374-415, 483-558. -/
def isRequirementSatisfied (bindings : List CredentialBinding) (reqId : String) : Bool :=
  bindings.any (fun binding => binding.requirementId = reqId)

end HeytingLean.Bridge.AgentPMT
