import HeytingLean.Crypto.Games.INDCCA

/-!
# Hybrid KEM composition (X-Wing style, spec-level)

This module provides:
- a small abstract KEM interface (`KEMScheme`);
- a product/parallel combiner (`hybridKEM`);
- a bridge to the local `PMF`-based IND-CCA game; and
- explicit reduction-statement surfaces for proving hybrid security honestly.

We intentionally do **not** introduce new axioms here. Concrete cryptographic assumptions and
reductions are tracked separately (conjecture/session workflow) and, when approved, isolated in
dedicated assumption modules (like `MLKEMAxioms.lean` for FO + published numerical bounds).

Important scope boundary:

* the old placeholder `IND_CCA := True` has been removed;
* the raw pair-valued hybrid secret does **not** get a free "left secure or right secure"
  theorem in this module; and
* hybrid security is only exported through explicit reduction statements.

That is the honest midpoint before a richer X-Wing-style combiner or VCV-io game-hopping layer lands.

Reference motivation:
- ePrint 2024/039 ("X-Wing: The Hybrid KEM You've Been Looking For")
- IETF draft "tls-ecdhe-mlkem" (hybrid ECDHE + ML-KEM)
-/

namespace HeytingLean
namespace Crypto
namespace KEM

open scoped BigOperators

/-- Abstract KEM interface, equipped for the local `PMF`-based IND-CCA game. -/
structure KEMScheme where
  PublicKey : Type
  SecretKey : Type
  Ciphertext : Type
  SharedSecret : Type
  [ciphertextDecEq : DecidableEq Ciphertext]
  [sharedSecretFintype : Fintype SharedSecret]
  [sharedSecretNonempty : Nonempty SharedSecret]
  keygen : PMF (PublicKey × SecretKey)
  encaps : PublicKey → PMF (Ciphertext × SharedSecret)
  decaps : SecretKey → Ciphertext → Option SharedSecret

attribute [instance] KEMScheme.ciphertextDecEq
attribute [instance] KEMScheme.sharedSecretFintype
attribute [instance] KEMScheme.sharedSecretNonempty

/-- Reinterpret a `KEMScheme` as the generic local IND-CCA game interface. -/
def toGameKEM (K : KEMScheme) : Games.KEM where
  PK := K.PublicKey
  SK := K.SecretKey
  CT := K.Ciphertext
  SS := K.SharedSecret
  ctDecEq := K.ciphertextDecEq
  ssFintype := K.sharedSecretFintype
  ssNonempty := K.sharedSecretNonempty
  keygen := K.keygen
  encaps := K.encaps
  decaps := K.decaps

/-- Local IND-CCA adversaries for a `KEMScheme`, reusing the generic PMF game. -/
abbrev INDCCAAdversary (K : KEMScheme) : Type :=
  Games.INDCCAAdversary (toGameKEM K)

/-- Local IND-CCA game output distribution for challenge bit `b`. -/
noncomputable def IND_CCA_Game (K : KEMScheme) (A : INDCCAAdversary K) (b : Bool) : PMF Bool :=
  Games.INDCCA.game (K := toGameKEM K) (A := A) b

/-- Local IND-CCA win probability for challenge bit `b`. -/
noncomputable def IND_CCA_WinProb (K : KEMScheme) (A : INDCCAAdversary K) (b : Bool) : ℝ :=
  Games.INDCCA.winProb (K := toGameKEM K) (A := A) b

/-- Local IND-CCA distinguishing advantage. -/
noncomputable def IND_CCA_Advantage (K : KEMScheme) (A : INDCCAAdversary K) : ℝ :=
  Games.INDCCA.advantage (K := toGameKEM K) (A := A)

/-- A concrete security witness packages an explicit adversary-dependent bound for the local
IND-CCA game. This is the current honest security surface for abstract KEMs in Heyting. -/
structure INDCCASecurityWitness (K : KEMScheme) where
  bound : INDCCAAdversary K → ℝ
  sound : ∀ A, IND_CCA_Advantage K A ≤ bound A

/-- A scheme is IND-CCA secure when it comes with an explicit local game-bound witness. -/
def IND_CCA (K : KEMScheme) : Prop :=
  Nonempty (INDCCASecurityWitness K)

/-- Hybrid combiner: run both KEMs and pair ciphertexts/secrets. -/
noncomputable def hybridKEM (K1 K2 : KEMScheme) : KEMScheme where
  PublicKey := K1.PublicKey × K2.PublicKey
  SecretKey := K1.SecretKey × K2.SecretKey
  Ciphertext := K1.Ciphertext × K2.Ciphertext
  SharedSecret := K1.SharedSecret × K2.SharedSecret
  keygen := K1.keygen.bind fun (pk1, sk1) =>
    K2.keygen.bind fun (pk2, sk2) =>
      PMF.pure ((pk1, pk2), (sk1, sk2))
  encaps := fun (pk1, pk2) =>
    (K1.encaps pk1).bind fun (ct1, ss1) =>
      (K2.encaps pk2).bind fun (ct2, ss2) =>
        PMF.pure ((ct1, ct2), (ss1, ss2))
  decaps := fun (sk1, sk2) (ct1, ct2) =>
    match K1.decaps sk1 ct1, K2.decaps sk2 ct2 with
    | some ss1, some ss2 => some (ss1, ss2)
    | _, _ => none

/-- An explicit left-component reduction statement for the current product hybrid. -/
def LeftReductionStatement (K1 K2 : KEMScheme) : Prop :=
  ∀ A : INDCCAAdversary (hybridKEM K1 K2),
    ∃ B : INDCCAAdversary K1,
      IND_CCA_Advantage (hybridKEM K1 K2) A ≤ IND_CCA_Advantage K1 B

/-- An explicit right-component reduction statement for the current product hybrid. -/
def RightReductionStatement (K1 K2 : KEMScheme) : Prop :=
  ∀ A : INDCCAAdversary (hybridKEM K1 K2),
    ∃ B : INDCCAAdversary K2,
      IND_CCA_Advantage (hybridKEM K1 K2) A ≤ IND_CCA_Advantage K2 B

/-- Named bundle of classical reduction assumptions for the current raw product
hybrid. This is the honest assumption surface for closing the current WP-5
theorem family without pretending the reductions are already formalized. -/
structure ReductionAssumptionBundle (K1 K2 : KEMScheme) where
  left : LeftReductionStatement K1 K2
  right : RightReductionStatement K1 K2

/-- Predicate asserting that the current hybrid theorem family is backed by an
explicit named reduction bundle. -/
def DocumentedReductionAssumptions (K1 K2 : KEMScheme) : Prop :=
  Nonempty (ReductionAssumptionBundle K1 K2)

/-- If a left-component reduction is supplied, a left security witness lifts to the raw product
hybrid. This theorem is honest about its hypothesis: the reduction itself is not free. -/
theorem hybrid_security_of_left (K1 K2 : KEMScheme)
    (hRed : LeftReductionStatement K1 K2) :
    IND_CCA K1 → IND_CCA (hybridKEM K1 K2) := by
  classical
  intro hSec
  rcases hSec with ⟨sec⟩
  refine ⟨{ bound := fun A => sec.bound (Classical.choose (hRed A)), sound := ?_ }⟩
  intro A
  have hChosen := Classical.choose_spec (hRed A)
  exact le_trans hChosen (sec.sound _)

/-- Right-component version of `hybrid_security_of_left`. -/
theorem hybrid_security_of_right (K1 K2 : KEMScheme)
    (hRed : RightReductionStatement K1 K2) :
    IND_CCA K2 → IND_CCA (hybridKEM K1 K2) := by
  classical
  intro hSec
  rcases hSec with ⟨sec⟩
  refine ⟨{ bound := fun A => sec.bound (Classical.choose (hRed A)), sound := ?_ }⟩
  intro A
  have hChosen := Classical.choose_spec (hRed A)
  exact le_trans hChosen (sec.sound _)

/-- OR-style hybrid security is available only when the corresponding explicit reduction
statement is available on the branch that is assumed secure. -/
theorem hybrid_security_of_or (K1 K2 : KEMScheme)
    (hLeft : LeftReductionStatement K1 K2)
    (hRight : RightReductionStatement K1 K2) :
    (IND_CCA K1 ∨ IND_CCA K2) → IND_CCA (hybridKEM K1 K2) := by
  intro h
  cases h with
  | inl h1 => exact hybrid_security_of_left K1 K2 hLeft h1
  | inr h2 => exact hybrid_security_of_right K1 K2 hRight h2

/-- Bundle-driven version of `hybrid_security_of_or`. This is the intended
assumption-scoped API surface for the current WP-5 state. -/
theorem hybrid_security_of_documentedAssumptions (K1 K2 : KEMScheme)
    (hBundle : DocumentedReductionAssumptions K1 K2) :
    (IND_CCA K1 ∨ IND_CCA K2) → IND_CCA (hybridKEM K1 K2) := by
  intro h
  rcases hBundle with ⟨bundle⟩
  exact hybrid_security_of_or K1 K2 bundle.left bundle.right h

/-
Phase 11 (Hybrid Protocols) additionally uses a hybrid of *key sources* (e.g.
QKD + PQ KEM). We keep this interface-first, parallel to `KEMScheme`, so later
work can connect it to UC executions and concrete KEM game definitions.

Important scope boundary: this block is deliberately about interface
well-formedness / usability, not cryptographic security. The old
`KeySecure := True` placeholder has been removed to avoid overclaiming.
-/

/-- Abstract source of key material (shape only). -/
structure KeySource where
  Key : Type
  gen : Unit → Key

/-- Minimal well-formedness / usability condition for a key source: it can
actually produce a key. This is structural, not cryptographic. -/
def KeySourceUsable (S : KeySource) : Prop :=
  Nonempty S.Key

/-- Any declared key source is usable because `gen` produces a key. -/
theorem keySourceUsable (S : KeySource) : KeySourceUsable S := by
  exact ⟨S.gen ()⟩

/-- Hybrid key source: generate both keys and pair them. -/
def hybridKeySource (S1 S2 : KeySource) : KeySource where
  Key := S1.Key × S2.Key
  gen := fun () => (S1.gen (), S2.gen ())

theorem hybridKey_usable_of_left (S1 S2 : KeySource) :
    KeySourceUsable S1 → KeySourceUsable (hybridKeySource S1 S2) := by
  intro h1
  exact ⟨(Classical.choice h1, S2.gen ())⟩

theorem hybridKey_usable_of_right (S1 S2 : KeySource) :
    KeySourceUsable S2 → KeySourceUsable (hybridKeySource S1 S2) := by
  intro h2
  exact ⟨(S1.gen (), Classical.choice h2)⟩

theorem hybridKey_usable_of_or (S1 S2 : KeySource) :
    (KeySourceUsable S1 ∨ KeySourceUsable S2) → KeySourceUsable (hybridKeySource S1 S2) := by
  intro h
  cases h with
  | inl h1 => exact hybridKey_usable_of_left S1 S2 h1
  | inr h2 => exact hybridKey_usable_of_right S1 S2 h2

end KEM
end Crypto
end HeytingLean
