import HeytingLean.Bridge.AgentPMT.AuthGate

namespace HeytingLean.Tests.Bridge.AgentPMT

open HeytingLean.Bridge.AgentPMT

private def adminRequest : Request :=
  { defaultRequest with
      method := .POST
      path := "/tools/test"
      hasAdminKey := true
      adminKeyValid := true }

private def bearerRequest : Request :=
  { defaultRequest with
      method := .POST
      path := "/tools/test"
      hasBearerToken := true }

example : checkAuth adminRequest "product123" none = .bypass := by
  rfl

example :
    checkAuth { defaultRequest with method := .POST, path := "/tools/test" } "product123" none =
      .rejected "Missing Authorization header" := by
  rfl

example :
    checkAuth bearerRequest "product123" (some "product123") =
      .authenticated "product123" "" := by
  rfl

example :
    checkAuth bearerRequest "product123" (some "product456") =
      .rejected "Product ID mismatch: product456 != product123" := by
  rfl

example :
    selectCredentialSource
      { defaultRequest with hasInternalCredHeader := true, hasAutoloadHeaders := true } =
      .internalHeader := by
  rfl

#eval checkAuth adminRequest "product123" none
#eval checkAuth bearerRequest "product123" (some "product456")

end HeytingLean.Tests.Bridge.AgentPMT
