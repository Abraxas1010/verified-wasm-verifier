import HeytingLean.Crypto.DSA.MLDSA204Params
import HeytingLean.Crypto.KEM.FujisakiOkamoto
import HeytingLean.Crypto.Lattice.Problems

namespace HeytingLean
namespace Crypto
namespace DSA
namespace FIPS204
namespace ProofLine

open HeytingLean.Crypto.KEM.FujisakiOkamoto

/-!
# ML-DSA proof-line skeleton

This module records the current repository-native statement shape for ML-DSA:

1. parameter bookkeeping from FIPS 204,
2. the imported lattice-assumption boundary (module-LWE + SIS),
3. the external proof-line / implementation provenance boundary.

It is intentionally an honest metadata layer, not a claim that EUF-CMA has already
been rechecked natively in Lean.
-/

/-- External references used by the imported ML-DSA proof line. -/
structure ImportedProofBundle where
  standardReference : ExternalReference
  signatureSecurity : ExternalReference
  implementationRefinement : ExternalReference
  deriving Repr

/-- A named security component used in the imported proof line. -/
structure SecurityComponent where
  name : String
  provenance : ExternalReference
  summary : String
  deriving Repr

/-- Statement bundle corresponding to the current ML-DSA external proof line. -/
structure StatementBundle (p : MLDSA204Params) where
  parameterSet : String
  mlweParams : Lattice.MLWEParams
  sisParams : Lattice.SISParams
  proofSources : ImportedProofBundle
  signingUnforgeability : SecurityComponent
  nativeCorrectnessSurface : String
  implementationBoundary : String
  claimSummary : String
  deriving Repr

/-- Statement-level MLWE parameter view induced from an ML-DSA FIPS 204 bundle. -/
def toMLWEParams (p : MLDSA204Params) : Lattice.MLWEParams :=
  { n := p.n, q := p.q, k := p.k }

/-- Statement-level SIS parameter view induced from an ML-DSA FIPS 204 bundle. -/
def toSISParams (p : MLDSA204Params) : Lattice.SISParams :=
  { n := p.ℓ * p.n, m := p.k * p.n, q := p.q }

def fips204Reference : ExternalReference :=
  { label := "FIPS 204 ML-DSA"
    location := "https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.204.pdf"
    theoremId := "Published ML-DSA parameter table"
    model := "standard specification" }

/-- Conservative external citation placeholder for the current ML-DSA proof line. -/
def importedMLDSAReference : ExternalReference :=
  { label := "External ML-DSA / Dilithium EUF-CMA proof line"
    location := "https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.204.pdf"
    theoremId := "Security rationale tracked externally; Lean-native import pending"
    model := "external proof literature / implementation boundary" }

def importedProofSources : ImportedProofBundle :=
  { standardReference := fips204Reference
    signatureSecurity := importedMLDSAReference
    implementationRefinement := importedMLDSAReference }

def importedStatementBundle (p : MLDSA204Params) : StatementBundle p :=
  { parameterSet := p.name
    mlweParams := toMLWEParams p
    sisParams := toSISParams p
    proofSources := importedProofSources
    signingUnforgeability :=
      { name := "mldsa_euf_cma"
        provenance := importedMLDSAReference
        summary :=
          "EUF-CMA is tracked as an imported statement boundary over MLWE/SIS-style lattice assumptions." }
    nativeCorrectnessSurface :=
      "abort-explicit sign/verify relation with parameter-indexed key/signature views"
    implementationBoundary := "Standardized runtime and external proof corpus remain the executable and security boundary."
    claimSummary :=
      "ML-DSA EUF-CMA is represented as an imported proof-line bundle; Lean currently tracks parameters, assumptions, a native correctness surface, and provenance only." }

theorem importedStatementBundle_parameterSet (p : MLDSA204Params) :
    (importedStatementBundle p).parameterSet = p.name := rfl

theorem importedStatementBundle_mlweParams (p : MLDSA204Params) :
    (importedStatementBundle p).mlweParams = toMLWEParams p := rfl

theorem importedStatementBundle_sisParams (p : MLDSA204Params) :
    (importedStatementBundle p).sisParams = toSISParams p := rfl

theorem importedStatementBundle_nativeCorrectnessSurface (p : MLDSA204Params) :
    (importedStatementBundle p).nativeCorrectnessSurface =
      "abort-explicit sign/verify relation with parameter-indexed key/signature views" := rfl

end ProofLine
end FIPS204
end DSA
end Crypto
end HeytingLean
