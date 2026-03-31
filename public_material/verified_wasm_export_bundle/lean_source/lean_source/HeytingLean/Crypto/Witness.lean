import HeytingLean.Crypto.Correctness

namespace HeytingLean
namespace Crypto

open HeytingLean.LoF

universe u v

variable {α : Type u} [PrimaryAlgebra α]
variable {R : Reentry α}

namespace Lens

variable (L : Lens (R := R))

/-- Canonical witness trace obtained by running the compiled form. -/
def canonicalWitness {n : ℕ} (φ : Form n) (ρ : EnvΩ (R := R) n) :
    Trace L :=
  canonicalTrace (L := L) (φ := φ) (ρ := ρ)

/-- Propositional witness relation: a trace is valid if it matches the canonical run. -/
def Witness {n : ℕ} (φ : Form n) (ρ : EnvΩ (R := R) n) (trace : Trace L) : Prop :=
  trace = canonicalWitness (L := L) (φ := φ) (ρ := ρ)

lemma Witness.sound {n : ℕ} {φ : Form n} {ρ : EnvΩ (R := R) n}
    {trace : Trace L} (_ : Witness (L := L) φ ρ trace) :
    L.dec (canonicalValue (L := L) (φ := φ) (ρ := ρ)) =
      Form.evalΩ (R := R) φ ρ :=
  compile_correct (L := L) (φ := φ) (ρ := ρ)

lemma Witness.complete {n : ℕ} (φ : Form n) (ρ : EnvΩ (R := R) n) :
    Witness (L := L) φ ρ (canonicalWitness (L := L) φ ρ) :=
  rfl

theorem Witness.exists {n : ℕ} (φ : Form n) (ρ : EnvΩ (R := R) n) :
    ∃ trace, Witness (L := L) φ ρ trace :=
  ⟨canonicalWitness (L := L) φ ρ,
    Witness.complete (L := L) (φ := φ) (ρ := ρ)⟩

end Lens

end Crypto
end HeytingLean
