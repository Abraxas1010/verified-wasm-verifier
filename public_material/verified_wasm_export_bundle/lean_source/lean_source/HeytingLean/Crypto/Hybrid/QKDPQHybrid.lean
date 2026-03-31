import HeytingLean.Crypto.Composable
import HeytingLean.Crypto.KEM.HybridKEM
import HeytingLean.Crypto.QKD.BB84.KeyExtraction
import HeytingLean.Crypto.QKD.BB84.ProbabilisticSecurity

/-!
# Hybrid protocols: QKD + PQC (spec-level)

Phase 11: interface-first specification for hybrid key establishment that combines:
- an information-theoretic QKD key (modeled via UC `IdealKeyExchange`), and
- a computational PQ KEM shared secret (modeled via an abstract `KEMScheme`).

This file is intentionally lightweight: it provides stable names and a “either breaks” style
security statement shell without asserting concrete cryptographic reductions. The PQ side now
reuses the local PMF-based IND-CCA witness surface from `Crypto.KEM.HybridKEM`, so `PQSecure`
is no longer a raw `True` placeholder.
-/

namespace HeytingLean
namespace Crypto
namespace Hybrid

open HeytingLean.Crypto.Composable
open HeytingLean.Crypto.Information.Hashing
open HeytingLean.Crypto.KEM
open HeytingLean.Crypto.QKD

/-- Hybrid key material: a QKD key together with a PQ shared secret (plus ciphertext). -/
structure HybridKEM (n : Nat) (K : KEMScheme) where
  qkd_key : Fin n → Bool
  pq_ciphertext : K.Ciphertext
  pq_sharedSecret : K.SharedSecret

/-- Combined key material (interface-first). -/
def HybridKEM.combined {n : Nat} {K : KEMScheme} (H : HybridKEM n K) :
    (Fin n → Bool) × K.SharedSecret :=
  (H.qkd_key, H.pq_sharedSecret)

/--
Native hybrid-facing wrapper around the BB84 privacy-amplification witness. This now lives in the
hybrid module directly, so downstream QKD+PQC consumers do not need a separate bridge import.
-/
structure QKDExtractionWitness (D R S : Type*)
    [Fintype D] [Fintype R] [Fintype S] [DecidableEq R] [TwoUniversal D R S] where
  finiteKey : QKD.BB84.BB84FiniteKeySecurity
  extracted : QKD.BB84.BB84ExtractedKeySecurity D R S
  covered : finiteKey.coversExtractionError extracted.extractionError

namespace QKDExtractionWitness

variable {D R S : Type*}
variable [Fintype D] [Fintype R] [Fintype S] [DecidableEq R] [TwoUniversal D R S]

/-- The extracted BB84 key is within the finite-key secrecy budget. -/
theorem statDistance_le_epsilonSec (W : QKDExtractionWitness D R S) :
    Information.PrivacyAmplification.Finite.statDistance
        W.extracted.actualDist W.extracted.idealDist ≤ W.finiteKey.bound.epsilon_sec := by
  exact le_trans W.extracted.statDistance_le_extractionError W.covered

/-- The total finite-key budget covers correctness plus the extracted-key error. -/
theorem correctness_plus_extraction_le_total (W : QKDExtractionWitness D R S) :
    W.finiteKey.bound.epsilon_cor + W.extracted.extractionError ≤ W.finiteKey.epsilonTotal := by
  exact W.finiteKey.correctness_plus_extraction_le_total W.covered

end QKDExtractionWitness

/--
A hybrid key-establishment package carrying both the concrete hybrid key material and the native
BB84 extraction witness that certifies the QKD leg.
-/
structure WitnessedHybridKEM (n : Nat) (K : KEMScheme) (D R S : Type*)
    [Fintype D] [Fintype R] [Fintype S] [DecidableEq R] [TwoUniversal D R S]
    extends HybridKEM n K where
  qkdWitness : QKDExtractionWitness D R S

namespace HybridKEM

variable {n : Nat} {K : KEMScheme}
variable {D R S : Type*}
variable [Fintype D] [Fintype R] [Fintype S] [DecidableEq R] [TwoUniversal D R S]

/-- Attach native BB84 extraction evidence directly to a hybrid key-establishment record. -/
def withQKDExtractionWitness (H : HybridKEM n K) (W : QKDExtractionWitness D R S) :
    WitnessedHybridKEM n K D R S :=
  { toHybridKEM := H, qkdWitness := W }

end HybridKEM

namespace WitnessedHybridKEM

variable {n : Nat} {K : KEMScheme}
variable {D R S : Type*}
variable [Fintype D] [Fintype R] [Fintype S] [DecidableEq R] [TwoUniversal D R S]

/-- The QKD component of a witnessed hybrid package inherits the BB84 secrecy budget. -/
theorem qkd_statDistance_le_epsilonSec (H : WitnessedHybridKEM n K D R S) :
    Information.PrivacyAmplification.Finite.statDistance
        H.qkdWitness.extracted.actualDist H.qkdWitness.extracted.idealDist ≤
      H.qkdWitness.finiteKey.bound.epsilon_sec := by
  exact QKDExtractionWitness.statDistance_le_epsilonSec H.qkdWitness

/-- The QKD component of a witnessed hybrid package stays inside the total finite-key budget. -/
theorem qkd_correctness_plus_extraction_le_total (H : WitnessedHybridKEM n K D R S) :
    H.qkdWitness.finiteKey.bound.epsilon_cor + H.qkdWitness.extracted.extractionError ≤
      H.qkdWitness.finiteKey.epsilonTotal := by
  exact QKDExtractionWitness.correctness_plus_extraction_le_total H.qkdWitness

end WitnessedHybridKEM

/-- PQ component security inherited from the local IND-CCA witness interface. -/
def PQSecure (K : KEMScheme) : Prop :=
  IND_CCA K

/-- “Either breaks” hybrid security: if either component is secure, treat the hybrid as secure. -/
def HybridSecure {n : Nat} (πqkd : Protocol (Composable.Instances.IdealKeyExchange n))
    (K : KEMScheme) : Prop :=
  UCSecure (Composable.Instances.IdealKeyExchange n) πqkd ∨ PQSecure K

theorem hybrid_security {n : Nat} (πqkd : Protocol (Composable.Instances.IdealKeyExchange n))
    (K : KEMScheme) :
    (UCSecure (Composable.Instances.IdealKeyExchange n) πqkd ∨ PQSecure K) →
      HybridSecure (πqkd := πqkd) K := by
  intro h
  exact h

end Hybrid
end Crypto
end HeytingLean
