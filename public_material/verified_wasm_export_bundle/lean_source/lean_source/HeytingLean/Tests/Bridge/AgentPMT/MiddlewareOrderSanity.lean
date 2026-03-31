import HeytingLean.Bridge.AgentPMT.MiddlewareOrder

namespace HeytingLean.Tests.Bridge.AgentPMT

open HeytingLean.Bridge.AgentPMT

example :
    requestOrderNames =
      ["ErrorLoggingMiddleware", "CredentialInjectionMiddleware",
        "SecurityHeadersMiddleware", "CORSMiddleware"] := by
  rfl

example : productionStack.length = 4 := by
  rfl

example :
    credentialInjectionMiddleware.fires
      { defaultRequest with method := .GET, path := "/tools/test" } = false := by
  rfl

example :
    credentialInjectionMiddleware.fires
      { defaultRequest with method := .POST, path := "/health" } = false := by
  apply credentialInjection_path_guard
  native_decide

example :
    credentialInjectionMiddleware.fires
      { defaultRequest with method := .POST, path := "/tools/test", contentType := "text/plain" } = false := by
  apply credentialInjection_content_type_guard
  native_decide

example :
    errorLoggingMiddleware.fires
      { defaultRequest with path := "/crypto/decrypt" } = false := by
  rfl

#eval requestOrderNames
#eval credentialInjectionMiddleware.fires { defaultRequest with method := .POST, path := "/tools/test" }

end HeytingLean.Tests.Bridge.AgentPMT
