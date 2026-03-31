import Mathlib.Data.List.Basic

namespace HeytingLean.Bridge.AgentPMT

/-- Python: routers/middleware/credential_injection.py:46-49. -/
inductive HttpMethod
  | GET
  | POST
  | PUT
  | PATCH
  | DELETE
  | HEAD
  | OPTIONS
  deriving DecidableEq, Repr

/-- Python: routers/middleware/credential_injection.py:56-64. -/
def HttpMethod.asToken : HttpMethod → String
  | .GET => "GET"
  | .POST => "POST"
  | .PUT => "PUT"
  | .PATCH => "PATCH"
  | .DELETE => "DELETE"
  | .HEAD => "HEAD"
  | .OPTIONS => "OPTIONS"

/-- Python: main.py:57-65, routers/auth.py:408-460, routers/middleware/credential_injection.py:51-109. -/
structure Request where
  method : HttpMethod
  path : String
  hasAdminKey : Bool
  adminKeyValid : Bool
  hasBearerToken : Bool
  hasInternalCredHeader : Bool
  hasAutoloadHeaders : Bool
  contentType : String
  deriving DecidableEq, Repr

/-- Python: main.py:25-29, routers/middleware/error_logging.py:64-119. -/
inductive Response
  | success (body : String)
  | error (code : Nat) (message : String)
  | passthrough
  deriving DecidableEq, Repr

/-- Python: routers/middleware/credential_injection.py:90-105. -/
inductive CredentialSource
  | none
  | internalHeader
  | localAutoload
  deriving DecidableEq, Repr

/-- Python: routers/auth.py:425-460. -/
inductive AuthDecision
  | bypass
  | authenticated (productId : String) (budgetId : String)
  | rejected (reason : String)
  deriving DecidableEq, Repr

/-- Python: routers/credential_resolver.py:417-458, 495-507. -/
inductive BindingTier
  | budget
  | budgetWide
  | master
  deriving DecidableEq, Repr

instance : LE BindingTier where
  le a b :=
    match a, b with
    | .budget, _ => True
    | .budgetWide, .budget => False
    | .budgetWide, _ => True
    | .master, .master => True
    | .master, _ => False

instance : DecidableRel (α := BindingTier) (· ≤ ·) := by
  intro a b
  cases a <;> cases b
  all_goals
    first
      | exact isTrue trivial
      | exact isFalse (by intro h; cases h)

/-- Python: routers/credential_resolver.py:358-558. -/
structure CredentialBinding where
  tier : BindingTier
  requirementId : String
  credentialId : String
  payload : String
  deriving DecidableEq, Repr

/-- Python: routers/auth.py:391-460, routers/middleware/credential_injection.py:35-140. -/
def defaultRequest : Request where
  method := .GET
  path := "/"
  hasAdminKey := false
  adminKeyValid := false
  hasBearerToken := false
  hasInternalCredHeader := false
  hasAutoloadHeaders := false
  contentType := "application/json"

end HeytingLean.Bridge.AgentPMT
