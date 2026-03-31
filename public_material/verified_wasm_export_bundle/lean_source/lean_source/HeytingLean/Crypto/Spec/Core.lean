import HeytingLean.Crypto.CoreSemantics
import HeytingLean.Crypto.Correctness

/-
# Crypto.Spec.Core

Thin specification facade for the core `Form`/lens compilation semantics.
This module re‑exports the canonical run/value helpers and the
`compile_correct` theorem so that higher‑level spec modules can depend on a
stable API without importing the full crypto stack.
-/

namespace HeytingLean
namespace Crypto
namespace Spec

open HeytingLean.LoF

universe u v

variable {α : Type u} [PrimaryAlgebra α]
variable {R : Reentry α}

/-! ## Core environment abbreviation -/

abbrev EnvΩ (n : ℕ) := Crypto.EnvΩ (R := R) n

/-! ## Logical satisfaction helpers

These helpers give a standard way to view `Form` programs as propositions
over Ωᵣ and over compiled lens semantics. They are intentionally thin
wrappers so that higher‑level spec modules can talk about “spec holds”
without depending on implementation details of the crypto stack.
-/

/-- Direct Ωᵣ satisfaction of a `Form` under an environment. -/
def holds {n : ℕ} (φ : Crypto.Form n) (ρ : EnvΩ (R := R) n) : Prop :=
  Crypto.Form.evalΩ (R := R) φ ρ = (⊤ : R.Omega)

/-! ## Canonical lens semantics (re‑exports)

The following are thin re‑exports of the core compilation correctness
lemmas from `HeytingLean.Crypto.Correctness`. They are placed under the
`Spec` namespace so that higher layers can depend on a single module for
the “intended meaning” of `Form` programs.
-/

namespace Lens

variable (L : Lens (R := R))

export Crypto.Lens (canonicalRun canonicalTrace canonicalValue compile_correct)

/-- Satisfaction via compiled lens semantics: decode the canonical value
    and require that it equals top in Ωᵣ. -/
def compiledHolds {n : ℕ} (φ : Crypto.Form n) (ρ : EnvΩ (R := R) n) : Prop :=
  L.dec (canonicalValue (L := L) (φ := φ) (ρ := ρ)) = (⊤ : R.Omega)

/-- Generic bridge: compiled satisfaction is equivalent to direct Ωᵣ
    satisfaction, via `compile_correct`. This is the standard hand‑off
    lemma for specs built on `Form`. -/
theorem compiledHolds_iff_holds {n : ℕ}
    (φ : Crypto.Form n) (ρ : EnvΩ (R := R) n) :
    compiledHolds (L := L) (φ := φ) (ρ := ρ) ↔
      holds (R := R) (φ := φ) (ρ := ρ) := by
  unfold compiledHolds holds
  have h := compile_correct (L := L) (φ := φ) (ρ := ρ)
  constructor
  · intro hcomp
    -- From `L.dec (canonicalValue ...) = ⊤` and `compile_correct`,
    -- conclude `Form.evalΩ φ ρ = ⊤`.
    have : Crypto.Form.evalΩ (R := R) φ ρ = (⊤ : R.Omega) := by
      calc
        Crypto.Form.evalΩ (R := R) φ ρ
            = L.dec (canonicalValue (L := L) (φ := φ) (ρ := ρ)) := by
              symm; exact h
        _   = (⊤ : R.Omega) := hcomp
    exact this
  · intro hholds
    -- From `Form.evalΩ φ ρ = ⊤` and `compile_correct`, conclude
    -- `L.dec (canonicalValue ...) = ⊤`.
    have : L.dec (canonicalValue (L := L) (φ := φ) (ρ := ρ)) = (⊤ : R.Omega) := by
      calc
        L.dec (canonicalValue (L := L) (φ := φ) (ρ := ρ))
            = Crypto.Form.evalΩ (R := R) φ ρ := h
        _   = (⊤ : R.Omega) := hholds
    exact this

end Lens

end Spec
end Crypto
end HeytingLean
