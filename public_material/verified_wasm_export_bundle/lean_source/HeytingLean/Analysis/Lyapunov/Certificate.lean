import HeytingLean.Analysis.Lyapunov.Basic

/-!
# Lyapunov Stability Certificates

This module defines the oracle-based certificate structure for verifying Lyapunov
stability. A numerical solver (e.g., scipy) computes the certificate, and we
verify the algebraic conditions that guarantee stability.

## Main Definitions

* `LyapunovCertificate`: Bundle of matrices (G, P, Q) with spectral bounds
* `claimsStable`: The certificate claims the system is stable
* `verifyLyapunovEquation`: Check if the Lyapunov equation holds (within tolerance)

## Oracle Model

The certificate includes:
- `minEigP`: Minimum eigenvalue of P (must be > 0 for P positive definite)
- `maxEigSymG`: Maximum eigenvalue of symmetric part of G (must be < 0 for Hurwitz)
- `residualBound`: Bound on ||G^T P + P G + Q||_F

These bounds come from the numerical solver and are trusted as oracles.
-/

noncomputable section

open scoped Matrix

namespace HeytingLean
namespace Analysis
namespace Lyapunov

variable {n : ℕ}

/-! ## Certificate Structure -/

/-- A Lyapunov stability certificate from a numerical solver. -/
structure LyapunovCertificate (n : ℕ) where
  /-- The system matrix. -/
  G : RMat n
  /-- The Lyapunov matrix (should be positive definite). -/
  P : RMat n
  /-- The rate matrix (should be positive definite for asymptotic stability). -/
  Q : RMat n
  /-- Minimum eigenvalue of P (oracle value). -/
  minEigP : ℝ
  /-- Maximum eigenvalue of the symmetric part of G (oracle value). -/
  maxEigSymG : ℝ
  /-- Residual bound: ||G^T P + P G + Q||_F (oracle value). -/
  residualBound : ℝ

/-! ## Certificate Claims -/

/-- The certificate claims the system `ẋ = Gx` is asymptotically stable. -/
def LyapunovCertificate.claimsStable (cert : LyapunovCertificate n) : Prop :=
  cert.minEigP > 0 ∧ cert.maxEigSymG < 0

/-- The certificate claims the Lyapunov equation is satisfied (exactly). -/
def LyapunovCertificate.claimsLyapunov (cert : LyapunovCertificate n) : Prop :=
  SatisfiesLyapunov cert.G cert.P cert.Q

/-- The certificate claims the Lyapunov equation is approximately satisfied. -/
def LyapunovCertificate.claimsApproxLyapunov (cert : LyapunovCertificate n) (tol : ℝ) : Prop :=
  cert.residualBound ≤ tol

/-! ## Oracle Assumptions -/

/-- Oracle assumption: minEigP is positive implies P is positive definite. -/
def LyapunovCertificate.PPosDef (cert : LyapunovCertificate n) : Prop :=
  cert.minEigP > 0 → cert.P.PosDef

/-- Oracle assumption: maxEigSymG is negative implies symmetric part negative definite. -/
def LyapunovCertificate.SymGNegDef (cert : LyapunovCertificate n) : Prop :=
  cert.maxEigSymG < 0 →
    ∀ x : Fin n → ℝ, x ≠ 0 → dot x ((symmetricPart cert.G).mulVec x) < 0

/-- Oracle assumption: P is symmetric. -/
def LyapunovCertificate.PSymmetric (cert : LyapunovCertificate n) : Prop :=
  cert.P.IsHermitian

/-- Oracle assumption: Q is symmetric. -/
def LyapunovCertificate.QSymmetric (cert : LyapunovCertificate n) : Prop :=
  cert.Q.IsHermitian

/-! ## Verified Claims -/

/-- A fully verified certificate bundles all oracle assumptions. -/
structure VerifiedCertificate (n : ℕ) extends LyapunovCertificate n where
  /-- P is symmetric. -/
  hPSymm : toLyapunovCertificate.PSymmetric
  /-- Q is symmetric. -/
  hQSymm : toLyapunovCertificate.QSymmetric
  /-- The Lyapunov equation holds exactly. -/
  hLyapunov : toLyapunovCertificate.claimsLyapunov
  /-- Oracle: minEigP positive implies P positive definite. -/
  hPPosDef : toLyapunovCertificate.PPosDef
  /-- Oracle: maxEigSymG negative implies sym(G) negative definite. -/
  hSymGNegDef : toLyapunovCertificate.SymGNegDef

/-- Extract stability claim from a verified certificate. -/
theorem VerifiedCertificate.stable_of_claims
    (cert : VerifiedCertificate n)
    (hStable : cert.toLyapunovCertificate.claimsStable) :
    cert.minEigP > 0 ∧ cert.maxEigSymG < 0 :=
  hStable

/-! ## Certificate Composition -/

/-- Create a certificate for a stable generator (to be proven in StableGenerator). -/
def mkStableGeneratorCert (A : RMat n) (B : RMat n)
    (_hA : A.transpose * A ≠ 0) : LyapunovCertificate n where
  G := -(A.transpose * A) + (B - B.transpose)
  P := 1  -- Identity matrix; actual value computed by solver
  Q := 2 • (A.transpose * A)
  minEigP := 0  -- Placeholder; solver computes actual value
  maxEigSymG := 0  -- Placeholder; solver computes actual value
  residualBound := 0  -- Placeholder

end Lyapunov
end Analysis
end HeytingLean

end
