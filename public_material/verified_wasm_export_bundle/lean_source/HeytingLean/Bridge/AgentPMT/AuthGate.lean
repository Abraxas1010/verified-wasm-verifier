import Mathlib.Tactic
import HeytingLean.Bridge.AgentPMT.Auth

namespace HeytingLean.Bridge.AgentPMT

/-- Python: routers/auth.py:425-434. -/
theorem admin_bypass_is_total :
    ∀ req : Request, ∀ expectedPid : String, ∀ jwtPid : Option String,
      req.adminKeyValid = true →
      checkAuth req expectedPid jwtPid = .bypass := by
  intro req expectedPid jwtPid hAdmin
  simp [checkAuth, hAdmin]

/-- Python: routers/auth.py:436-443. -/
theorem no_credentials_means_rejection :
    ∀ req : Request, ∀ expectedPid : String, ∀ jwtPid : Option String,
      req.adminKeyValid = false →
      req.hasBearerToken = false →
      ∃ reason, checkAuth req expectedPid jwtPid = .rejected reason := by
  intro req expectedPid jwtPid hAdmin hBearer
  refine ⟨"Missing Authorization header", ?_⟩
  simp [checkAuth, hAdmin, hBearer]

/-- Python: routers/auth.py:368-377, 445-460. -/
theorem product_id_match_reflexive :
    ∀ req : Request, ∀ pid : String,
      req.adminKeyValid = false →
      req.hasBearerToken = true →
      checkAuth req pid (some pid) = .authenticated pid "" := by
  intro req pid hAdmin hBearer
  simp [checkAuth, hAdmin, hBearer]

/-- Python: routers/auth.py:373-377, 445-455. -/
theorem product_id_mismatch_rejects :
    ∀ req : Request, ∀ expectedPid tokenPid : String,
      req.adminKeyValid = false →
      req.hasBearerToken = true →
      tokenPid ≠ expectedPid →
      ∃ reason, checkAuth req expectedPid (some tokenPid) = .rejected reason := by
  intro req expectedPid tokenPid hAdmin hBearer hMismatch
  refine ⟨s!"Product ID mismatch: {tokenPid} != {expectedPid}", ?_⟩
  simp [checkAuth, hAdmin, hBearer, hMismatch]

/-- Python: routers/middleware/credential_injection.py:90-105. -/
theorem credential_source_internal_header_priority :
    ∀ req : Request,
      req.hasInternalCredHeader = true →
      selectCredentialSource req = .internalHeader := by
  intro req hInternal
  simp [selectCredentialSource, hInternal]

/-- Python: routers/middleware/credential_injection.py:90-105. -/
theorem credential_source_exclusivity :
    ∀ req : Request,
      req.hasInternalCredHeader = true →
      selectCredentialSource req ≠ .localAutoload := by
  intro req hInternal
  rw [credential_source_internal_header_priority req hInternal]
  simp

/-- Python: routers/middleware/credential_injection.py:107-109. -/
theorem no_headers_no_injection :
    ∀ req : Request,
      req.hasInternalCredHeader = false →
      req.hasAutoloadHeaders = false →
      selectCredentialSource req = .none := by
  intro req hInternal hAutoload
  simp [selectCredentialSource, hInternal, hAutoload]

end HeytingLean.Bridge.AgentPMT
