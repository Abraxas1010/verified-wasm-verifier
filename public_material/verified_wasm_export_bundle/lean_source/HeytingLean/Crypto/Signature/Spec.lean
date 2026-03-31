/-
# Crypto.Signature.Spec

Abstract interfaces and specification-level properties for digital
signature schemes, aligned with `Crypto.Primitives.Spec` signature
property identifiers.

This module defines:
* a generic signature scheme interface; and
* correctness and unforgeability properties at a high level.

Concrete schemes (ECDSA, EdDSA, BLS, Schnorr, Dilithium, etc.) can
instantiate this interface and attach proofs or assumptions as needed.
-/

namespace HeytingLean
namespace Crypto
namespace Signature
namespace Spec

/-- Generic digital signature scheme interface. -/
structure Scheme where
  Msg   : Type
  Pub   : Type
  Priv  : Type
  Sig   : Type
  /-- Signature generation. -/
  sign   : Priv → Msg → Sig
  /-- Signature verification predicate. -/
  verify : Pub → Msg → Sig → Prop
  /-- Relation between public and private keys. -/
  keyRel : Pub → Priv → Prop

namespace Scheme

/-- Standard correctness property: messages signed with a private key
    verify under the corresponding public key. -/
def Correct (S : Scheme) : Prop :=
  ∀ (pk : S.Pub) (sk : S.Priv) (m : S.Msg),
    S.keyRel pk sk → S.verify pk m (S.sign sk m)

/-- Abstract unforgeability property:

This is intentionally left as a single `Prop` field to be instantiated
per scheme with a concrete game-based or reduction-style formulation. -/
structure SecurityProps (S : Scheme) where
  unforgeable : Prop

end Scheme

/- A trivial signature scheme where signatures are just strings of the
    form `"sig:<msg>"` and the public/private keys are ignored. This is
    for demonstration only and does **not** model any real cryptographic
    scheme. -/
def demoScheme : Scheme :=
  { Msg := String
    , Pub := Unit
    , Priv := Unit
    , Sig := String
    , sign := fun _ m => "sig:" ++ m
    , verify := fun _ m σ => σ = "sig:" ++ m
    , keyRel := fun _ _ => True }

/- Correctness of the trivial `demoScheme`: every signed message
    verifies under any key pair related by `keyRel` (which is always
    true in this example model). -/
theorem demoScheme_correct : Scheme.Correct demoScheme := by
  intro pk sk m hRel
  -- `keyRel` carries no information; correctness reduces to reflexivity.
  simp [demoScheme]

end Spec
end Signature
end Crypto
end HeytingLean
