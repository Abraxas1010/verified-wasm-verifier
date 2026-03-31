import Mathlib.Tactic
import HeytingLean.Bridge.AgentPMT.Middleware

namespace HeytingLean.Bridge.AgentPMT

/-- Python: main.py:32-74. The request path reverses middleware registration order. -/
theorem requestOrder_names :
    requestOrderNames =
      ["ErrorLoggingMiddleware", "CredentialInjectionMiddleware",
        "SecurityHeadersMiddleware", "CORSMiddleware"] := by
  rfl

/-- Python: main.py:67-74. Error logging runs before credential injection on requests. -/
theorem errorLogging_before_credentialInjection_in_request_path :
    requestOrderNames.head? = some "ErrorLoggingMiddleware" ∧
      requestOrderNames[1]? = some "CredentialInjectionMiddleware" := by
  constructor <;> rfl

/-- Python: routers/middleware/credential_injection.py:56-58. -/
theorem credentialInjection_method_guard :
    ∀ req : Request,
      req.method = .GET →
      credentialInjectionMiddleware.fires req = false := by
  intro req hMethod
  simp [credentialInjectionMiddleware, isCredentialMethod, hMethod]

/-- Python: routers/middleware/credential_injection.py:57-59. -/
theorem credentialInjection_path_guard :
    ∀ req : Request,
      ¬ req.path.startsWith toolsPrefix →
      credentialInjectionMiddleware.fires req = false := by
  intro req hPath
  simp [credentialInjectionMiddleware, hPath]

/-- Python: routers/middleware/credential_injection.py:60-64. -/
theorem credentialInjection_content_type_guard :
    ∀ req : Request,
      req.contentType ≠ "application/json" →
      credentialInjectionMiddleware.fires req = false := by
  intro req hContentType
  simp [credentialInjectionMiddleware, hContentType]

/-- Python: main.py:46-55. -/
theorem securityHeaders_always_fires :
    ∀ req : Request, securityHeadersMiddleware.fires req = true := by
  intro req
  rfl

/-- Python: main.py:32-74. -/
theorem productionStack_length : productionStack.length = 4 := by
  rfl

end HeytingLean.Bridge.AgentPMT
