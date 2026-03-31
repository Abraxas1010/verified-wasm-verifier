import HeytingLean.Crypto.DSA.MLDSA
import HeytingLean.Crypto.DSA.MLDSA204Params
import HeytingLean.Crypto.DSA.MLDSAProofLine
import HeytingLean.Crypto.DSA.MLDSASpec
import HeytingLean.Crypto.Lattice.RecoveryViews
import HeytingLean.Crypto.Security.Advantage
import HeytingLean.Crypto.Security.Reduction

namespace HeytingLean
namespace Crypto
namespace DSA

/-!
# ML-DSA security statement shells (v0.7)

This file records *statement-level* security goals for ML-DSA, explicitly parameterized by named
lattice assumptions (`MLWE`, `SIS`) from `HeytingLean.Crypto.Lattice`.

Nothing here is proven yet; it is a place to hang stable names and blueprint links while the
formalization is staged.
-/

namespace Security

open HeytingLean.Crypto.Lattice

/-- Interpret the lightweight runtime parameter tag as a FIPS 204 bundle. -/
def toFIPS204Params (p : MLDSAParams) : FIPS204.MLDSA204Params :=
  if p.name = "ML-DSA-44" then FIPS204.mldsa44
  else if p.name = "ML-DSA-65" then FIPS204.mldsa65
  else FIPS204.mldsa87

/-- Repository-native EUF-CMA statement bundle for the given ML-DSA parameter set. -/
abbrev EUF_CMA (p : MLDSAParams) : Type :=
  FIPS204.ProofLine.StatementBundle (toFIPS204Params p)

/-- Shell statement: ML-DSA EUF-CMA security under MLWE and SIS hardness assumptions. -/
structure EUF_CMA_under_MLWE_SIS (p : MLDSAParams) (Pmlwe : MLWEParams) (Psis : SISParams) where
  derive : Unsolvable (MLWEView Pmlwe) → Unsolvable (SISView Psis) → EUF_CMA p

/-- Explicit witness for the shared-game MLWE/SIS assumption input. -/
structure MLWESISAssumptionWitness (p : MLDSAParams) where
  token : Unit := ()
  mlweWitness : Unsolvable (MLWEView (FIPS204.ProofLine.toMLWEParams (toFIPS204Params p)))
  sisWitness : Unsolvable (SISView (FIPS204.ProofLine.toSISParams (toFIPS204Params p)))

/-- Shared-game target for the current native ML-DSA security surface. -/
def nativeEUFCMAGame (p : MLDSAParams) : HeytingLean.Crypto.Security.Game where
  State := Unit
  Transcript := FIPS204.MLDSA204Params × MLWEParams × SISParams
  Challenge := ByteArray
  Output := EUF_CMA p
  init := ()
  transcript := fun _ =>
    (toFIPS204Params p,
      FIPS204.ProofLine.toMLWEParams (toFIPS204Params p),
      FIPS204.ProofLine.toSISParams (toFIPS204Params p))
  challenge := fun _ => ByteArray.empty
  output := fun _ => FIPS204.ProofLine.importedStatementBundle (toFIPS204Params p)

/-- Shared oracle budget for the current ML-DSA security shell. -/
def nativeEUFCMAOracle (_p : MLDSAParams) : HeytingLean.Crypto.Security.OracleModel ByteArray ByteArray :=
  { budget :=
      { randomOracleQueries := 0
        decapsulationQueries := 0
        signingQueries := 1
        auxiliaryQueries := 0 }
    answer := some }

/-- Shared advantage surface for the current imported-shell target. -/
def nativeEUFCMAAdvantage (_p : MLDSAParams) : HeytingLean.Crypto.Security.Advantage :=
  { challenge0 := 0, challenge1 := 0 }

/-- Shared reduction target for the current ML-DSA security shell. -/
def nativeEUFCMAReduction (p : MLDSAParams) :
    HeytingLean.Crypto.Security.Reduction
      (MLWESISAssumptionWitness p)
      (EUF_CMA p) where
  budget := (nativeEUFCMAOracle p).budget
  transform := fun _ => FIPS204.ProofLine.importedStatementBundle (toFIPS204Params p)
  lossUpperBound := 0

theorem nativeEUFCMAGame_output (p : MLDSAParams) :
    (nativeEUFCMAGame p).output (nativeEUFCMAGame p).init =
      FIPS204.ProofLine.importedStatementBundle (toFIPS204Params p) := rfl

theorem nativeEUFCMAOracle_signing_budget (p : MLDSAParams) :
    (nativeEUFCMAOracle p).budget.signingQueries = 1 := rfl

theorem toFIPS204Params_44 :
    toFIPS204Params mldsa44 = FIPS204.mldsa44 := by
  simp [toFIPS204Params, mldsa44]

theorem toFIPS204Params_65 :
    toFIPS204Params mldsa65 = FIPS204.mldsa65 := by
  simp [toFIPS204Params, mldsa65]

theorem toFIPS204Params_87 :
    toFIPS204Params mldsa87 = FIPS204.mldsa87 := by
  simp [toFIPS204Params, mldsa87]

theorem toFIPS204Params_valid (p : MLDSAParams) :
    FIPS204.validParams (toFIPS204Params p) := by
  by_cases h44 : p.name = "ML-DSA-44"
  · simp [toFIPS204Params, h44, FIPS204.mldsa44_valid]
  · by_cases h65 : p.name = "ML-DSA-65"
    · simp [toFIPS204Params, h65, FIPS204.mldsa65_valid]
    · simp [toFIPS204Params, h44, h65, FIPS204.mldsa87_valid]

theorem importedEUF_CMA_assumption_surface (p : MLDSAParams) :
    let bundle := (FIPS204.ProofLine.importedStatementBundle (toFIPS204Params p))
    bundle.mlweParams = FIPS204.ProofLine.toMLWEParams (toFIPS204Params p) ∧
      bundle.sisParams = FIPS204.ProofLine.toSISParams (toFIPS204Params p) ∧
      FIPS204.validParams (toFIPS204Params p) := by
  simp [FIPS204.ProofLine.importedStatementBundle, toFIPS204Params_valid]

theorem importedEUF_CMA_signed_outputs_respect_hint_bound (p : MLDSAParams)
    (spec : FIPS204.Spec (toFIPS204Params p)) (seed msg : ByteArray) {σ : FIPS204.Signature (toFIPS204Params p)} :
    (spec.sign (spec.keygen seed).2 msg).signature? = some σ →
      (spec.sigRepr σ).hintWeight ≤ (toFIPS204Params p).ω := by
  exact FIPS204.sign_result_signature_hint_bound (p := toFIPS204Params p) spec seed msg

end Security

end DSA
end Crypto
end HeytingLean
