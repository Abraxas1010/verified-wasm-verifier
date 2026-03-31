import HeytingLean.Crypto.Witness

namespace HeytingLean
namespace Crypto

open HeytingLean.LoF

universe u v

variable {α : Type u} [PrimaryAlgebra α]
variable {R : Reentry α}

namespace Lens

variable (L : Lens (R := R))

/-- Proof-carrying transaction payload capturing the specification, environment, and trace. -/
structure Payload where
  arity : ℕ
  form : Form arity
  env : EnvΩ (R := R) arity
  program : Program arity
  trace : Trace L
  signatures : Unit := ()

/-- Canonical payload generated from the compiled form and its witness trace. -/
def canonicalPayload {n : ℕ} (φ : Form n) (ρ : EnvΩ (R := R) n) :
    Payload (L := L) :=
  { arity := n
    form := φ
    env := ρ
    program := Form.compile φ
    trace := canonicalWitness (L := L) φ ρ
    signatures := () }

/-- Predicate expressing that the payload carries the expected proof objects. -/
def verifies (payload : Payload (L := L)) : Prop :=
  payload.program = Form.compile payload.form ∧
    Witness (L := L) payload.form payload.env payload.trace

lemma canonicalPayload_verifies {n : ℕ} (φ : Form n) (ρ : EnvΩ (R := R) n) :
    verifies (L := L) (canonicalPayload (L := L) (φ := φ) (ρ := ρ)) := by
  constructor
  · rfl
  · exact Witness.complete (L := L) (φ := φ) (ρ := ρ)

/-- Soundness: a verified payload guarantees semantic agreement with the Heyting core. -/
lemma verifies_sound {payload : Payload (L := L)}
    (h : verifies (L := L) payload) :
    L.dec
        (canonicalValue (L := L)
          (φ := payload.form) (ρ := payload.env)) =
      Form.evalΩ (R := R) payload.form payload.env :=
  Witness.sound (L := L) (φ := payload.form) (ρ := payload.env)
    (trace := payload.trace) h.2

/-- Completeness: every specification admits a payload that verifies. -/
lemma verifies_complete {n : ℕ} (φ : Form n) (ρ : EnvΩ (R := R) n) :
    ∃ payload, verifies (L := L) payload :=
  ⟨canonicalPayload (L := L) (φ := φ) (ρ := ρ),
    canonicalPayload_verifies (L := L) (φ := φ) (ρ := ρ)⟩

end Lens

end Crypto
end HeytingLean
