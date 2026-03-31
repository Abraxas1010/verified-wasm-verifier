import HeytingLean.Certified.Program
import HeytingLean.Certified.Properties
import HeytingLean.Crypto.VerifiedPQC.Certificate

namespace HeytingLean
namespace Crypto
namespace VerifiedPQC

open HeytingLean.CAB
open HeytingLean.Certified

def requiredChecks : Nat := 4

/-- Acceptance kernel: succeed iff all four packet checks pass. -/
def acceptAllChecksFn (passedChecks : Nat) : Nat :=
  if passedChecks = requiredChecks then 1 else 0

private theorem acceptAllChecksFn_bounded : Property.Holds (.boundedNat 0 1) .nat .nat acceptAllChecksFn := by
  intro n
  by_cases h : n = requiredChecks
  · simp [acceptAllChecksFn, h, requiredChecks]
  · have h' : n ≠ 4 := by
      simpa [requiredChecks] using h
    simp [acceptAllChecksFn, requiredChecks, h']

private def v0_1_0 : SemVer := { major := 0, minor := 1, patch := 0 }

/-- Certified program artifact for the packet-verifier acceptance kernel. -/
def acceptAllChecksProgram : CertifiedProgram :=
  CertifiedProgram.mkHashed
    (id := "verified_pqc_accept_all_checks")
    (name := "verified_pqc_accept_all_checks")
    (version := v0_1_0)
    (dom := .nat)
    (cod := .nat)
    (dimension := .D3_Classical)
    (lenses := [.core, .c])
    (properties := [.boundedNat 0 1, .custom "VerifiedPQC.AcceptAllChecks"])
    (invariants := [])
    (fn := acceptAllChecksFn)
    (propProofs := by
      intro p hp
      simp at hp
      rcases hp with hp | hp
      · subst hp
        exact acceptAllChecksFn_bounded
      · subst hp
        trivial)
    (cCode :=
      "/* verified_pqc_accept_all_checks: Nat -> Nat */\n" ++
      "#include <stdint.h>\n" ++
      "uint64_t verified_pqc_accept_all_checks(uint64_t passed_checks) {\n" ++
      "  return passed_checks == 4 ? 1 : 0;\n" ++
      "}\n")

/-- Default CAB metadata for the carried verifier artifact. -/
def acceptAllChecksMetadata : CABMetadata :=
  { fragment := .Custom "verified-pqc-accept-all-checks"
    dimension := .D3
    lensCompatibility := []
    timestamp := 20260327 }

/-- Helper: package the acceptance-kernel program as a carried certificate. -/
def acceptAllChecksCertificate (proofBytes : ByteArray) : CarriedCertificate :=
  mkCarriedCertificate acceptAllChecksProgram proofBytes acceptAllChecksMetadata

theorem verify_acceptAllChecksCertificate (proofBytes : ByteArray) :
    verify (acceptAllChecksCertificate proofBytes) = true := by
  simpa [acceptAllChecksCertificate] using
    verify_mkCarriedCertificate acceptAllChecksProgram proofBytes acceptAllChecksMetadata

end VerifiedPQC
end Crypto
end HeytingLean
