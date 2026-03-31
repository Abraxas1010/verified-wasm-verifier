import HeytingLean.Bridge.AgentPMT.Types
import HeytingLean.Bridge.AgentPMT.Middleware
import HeytingLean.Bridge.AgentPMT.Auth
import HeytingLean.Bridge.AgentPMT.Credential

namespace HeytingLean.Bridge.AgentPMT

/-- Python: main.py:32-74. -/
def expectedMiddlewareOrder : List String :=
  ["CORSMiddleware", "SecurityHeadersMiddleware", "CredentialInjectionMiddleware", "ErrorLoggingMiddleware"]

/-- Python: main.py:32-74. -/
def expectedRequestOrder : List String :=
  ["ErrorLoggingMiddleware", "CredentialInjectionMiddleware", "SecurityHeadersMiddleware", "CORSMiddleware"]

/-- Python: routers/middleware/credential_injection.py:46-49. -/
def expectedAllowedMethodTokens : List String :=
  ["POST", "PUT", "PATCH"]

/-- Python: routers/middleware/credential_injection.py:46-49. -/
def expectedToolsPrefix : String := "/tools/"

/-- Python: routers/middleware/credential_injection.py:60-64. -/
def expectedContentTypeContainsJson : Bool := true

/-- Python: main.py:57-65, routers/middleware/error_logging.py:31-40. -/
def expectedExemptPaths : List String :=
  ["/health", "/", "/_ah/start", "/_ah/stop", "/crypto/encrypt", "/crypto/decrypt"]

/-- Python: routers/tools.py. Tool routes are expected to be auth-protected. -/
def expectedUnprotectedToolFunctions : List String := []

/-- Python: routers/auth.py:425-460. -/
def expectedAdminBypassPrecedesBearerCheck : Bool := true

/-- Python: routers/auth.py:368-377. -/
def expectedProductIdUsesStringCoercion : Bool := true

/-- Python: routers/middleware/credential_injection.py:90-105. -/
def expectedCredentialSourcePriority : List String :=
  ["internalHeader", "localAutoload", "none"]

/-- Python: main.py:32-74. -/
theorem expected_middleware_matches_model :
    productionStackNames = expectedMiddlewareOrder := by
  rfl

/-- Python: main.py:32-74. -/
theorem expected_request_order_matches_model :
    requestOrderNames = expectedRequestOrder := by
  rfl

/-- Python: routers/middleware/credential_injection.py:46-49. -/
theorem expected_allowed_methods_match_model :
    credentialInjectionAllowedMethods.map HttpMethod.asToken = expectedAllowedMethodTokens := by
  rfl

/-- Python: routers/middleware/credential_injection.py:46-49. -/
theorem expected_tools_prefix_matches_model : toolsPrefix = expectedToolsPrefix := by
  rfl

/-- Python: main.py:57-65, routers/middleware/error_logging.py:31-40. -/
theorem expected_exempt_paths_match_model :
    errorLoggingExemptPaths = expectedExemptPaths := by
  rfl

end HeytingLean.Bridge.AgentPMT
