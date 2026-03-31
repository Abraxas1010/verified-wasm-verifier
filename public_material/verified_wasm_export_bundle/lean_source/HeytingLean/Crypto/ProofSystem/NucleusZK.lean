import HeytingLean.Crypto.Commit.NucleusCommit

/-!
# Abstract zk-style interface over the nucleus commitment relation

This is a purely semantic interface:
* no cryptographic hardness is claimed;
* properties (completeness, soundness, zero-knowledge) are fields.

It composes over the order-theoretic `Rel` defined in `Commit/NucleusCommit`.
-/

namespace HeytingLean
namespace Crypto
namespace ProofSystem

open HeytingLean.Crypto.Commit

variable {PreGame : Type*}

/-- Problem instance: witness encoding and a nucleus context. -/
structure Instance (PreGame : Type*) where
  EW : EncodableWitness PreGame
  NC : NucleusCtx PreGame

namespace Instance

variable (I : Instance PreGame)

abbrev W    := I.EW.W
abbrev Ωpub := I.NC.stmt I.EW
abbrev Rel  := I.NC.Rel I.EW

/-- A minimal zk-style interface (CRS/prove/verify/simulate). -/
structure ZKInterface where
  CRS    : Type*
  Proof  : Type*
  keygen  : CRS
  prove   : CRS → I.W → Ωpub I → Proof
  verify  : CRS → Ωpub I → Proof → Prop
  simulate : CRS → Ωpub I → Proof

/-- Semantic properties w.r.t. the nucleus-induced relation. -/
structure ZKProperties (Z : ZKInterface I) : Prop where
  complete :
    ∀ (w : I.W) (y : Ωpub I),
      (I.Rel w y) → Z.verify Z.keygen y (Z.prove Z.keygen w y)
  sound :
    ∀ (y : Ωpub I) (π : Z.Proof),
      Z.verify Z.keygen y π → ∃ w : I.W, I.Rel w y
  zeroKnowledge :
    ∀ (y : Ωpub I),
      Z.verify Z.keygen y (Z.simulate Z.keygen y)

end Instance

/-- Convenience constructor for instances. -/
def mkInstance (EW : EncodableWitness PreGame) (NC : NucleusCtx PreGame) :
  Instance PreGame :=
  { EW := EW, NC := NC }

end ProofSystem
end Crypto
end HeytingLean
