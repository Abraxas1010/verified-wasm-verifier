import HeytingLean.Bridge.AgentPMT.Types

namespace HeytingLean.Bridge.AgentPMT

/-- Python: routers/middleware/credential_injection.py:46-49. -/
def credentialInjectionAllowedMethods : List HttpMethod :=
  [.POST, .PUT, .PATCH]

/-- Python: main.py:58-65, routers/middleware/error_logging.py:31-40. -/
def errorLoggingExemptPaths : List String :=
  ["/health", "/", "/_ah/start", "/_ah/stop", "/crypto/encrypt", "/crypto/decrypt"]

/-- Python: routers/middleware/credential_injection.py:46-49. -/
def toolsPrefix : String := "/tools/"

/-- Python: routers/middleware/credential_injection.py:56-64. -/
def isCredentialMethod : HttpMethod → Bool
  | .POST | .PUT | .PATCH => true
  | _ => false

/-- Python: main.py:32-74, routers/middleware/error_logging.py:31-40. -/
structure MiddlewareDef where
  name : String
  fires : Request → Bool
  modifiesBody : Bool
  modifiesHeaders : Bool

/-- Python: main.py:32-44. -/
def corsMiddleware : MiddlewareDef where
  name := "CORSMiddleware"
  fires := fun _ => true
  modifiesBody := false
  modifiesHeaders := true

/-- Python: main.py:46-55. -/
def securityHeadersMiddleware : MiddlewareDef where
  name := "SecurityHeadersMiddleware"
  fires := fun _ => true
  modifiesBody := false
  modifiesHeaders := true

/-- Python: main.py:67-68, routers/middleware/credential_injection.py:51-109. -/
def credentialInjectionMiddleware : MiddlewareDef where
  name := "CredentialInjectionMiddleware"
  fires := fun req =>
    isCredentialMethod req.method &&
      req.path.startsWith toolsPrefix &&
      req.contentType == "application/json"
  modifiesBody := true
  modifiesHeaders := true

/-- Python: main.py:70-75, routers/middleware/error_logging.py:45-59. -/
def errorLoggingMiddleware : MiddlewareDef where
  name := "ErrorLoggingMiddleware"
  fires := fun req => !(errorLoggingExemptPaths.contains req.path)
  modifiesBody := false
  modifiesHeaders := false

/-- Python: main.py:32-74. -/
def MiddlewareStack := List MiddlewareDef

/-- Python: main.py:32,55,68,72-75. Request path runs in reverse registration order. -/
def productionStack : MiddlewareStack :=
  [corsMiddleware, securityHeadersMiddleware, credentialInjectionMiddleware, errorLoggingMiddleware]

/-- Python: Starlette/FastAPI ASGI middleware composition; later registrations run first on requests. -/
def requestOrder (stack : MiddlewareStack) : MiddlewareStack :=
  stack.reverse

/-- Python: sync artifact mirror for `app.add_middleware(...)` order in main.py:32-74. -/
def productionStackNames : List String :=
  productionStack.map (·.name)

/-- Python: sync artifact mirror for request-path order implied by main.py:32-74. -/
def requestOrderNames : List String :=
  (requestOrder productionStack).map (·.name)

/-- Python: sync artifact mirror for named middleware lookup in main.py:32-74. -/
def indexOf (stack : MiddlewareStack) (name : String) : Option Nat :=
  stack.findIdx? (fun m => m.name = name)

end HeytingLean.Bridge.AgentPMT
