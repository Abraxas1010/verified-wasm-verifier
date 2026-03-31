import HeytingLean.Crypto.CoreSemantics
import HeytingLean.Crypto.Lens.Semantics

namespace HeytingLean
namespace Crypto

open HeytingLean.LoF

universe u v

variable {α : Type u} [PrimaryAlgebra α]
variable {R : Reentry α}

namespace Lens

variable (L : Lens (R := R))

lemma dec_evalL {n : ℕ} (φ : Form n) (ρ : L.EnvL n) :
    L.dec (Form.evalL (L := L) φ ρ) =
      Form.evalΩ (R := R) φ (fun i => L.dec (ρ i)) := by
  induction φ with
  | top =>
      simp [Form.evalL, Form.evalΩ, Lens.dec_top]
  | bot =>
      simp [Form.evalL, Form.evalΩ, Lens.dec_bot]
  | var idx =>
      simp [Form.evalL, Form.evalΩ]
  | and φ ψ ihφ ihψ =>
      simp [Form.evalL, Form.evalΩ, Lens.dec_and, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [Form.evalL, Form.evalΩ, Lens.dec_or, ihφ, ihψ]
  | imp φ ψ ihφ ihψ =>
      simp [Form.evalL, Form.evalΩ, Lens.dec_imp, ihφ, ihψ]

lemma transport {n : ℕ} (φ : Form n) (ρ : EnvΩ (R := R) n) :
    L.dec
        (Form.evalL (L := L) φ (fun i => L.enc (ρ i))) =
      Form.evalΩ (R := R) φ ρ := by
  have h :=
    dec_evalL (L := L) (φ := φ)
      (ρ := fun i => L.enc (ρ i))
  simpa [Lens.dec_enc] using h
