import Mathlib.Data.Finsupp.Encodable
import HeytingLean.IteratedVirtual.Bridge.HelixAdelic
import HeytingLean.MirandaDynamics.Billiards.CantorEncoding

/-!
# Bridges.OneDimensionalCompression

This module packages the “1D compression” pattern across three already-landed threads:

1. **Helix decomposition**: iteration depth is a 1D base (the `z` coordinate) with a periodic fiber (`xy`).
2. **Miranda billiards encoding**: a bi-infinite tape is injected into `[0,1]` (Cantor set), then combined with a head
   position `k : ℤ` by an affine embedding into pairwise-disjoint intervals.
3. **Computable encodings**: finite descriptions (e.g. finite-support tapes) have injections into `ℕ`, unlike full tape
   spaces `ℤ → Bool` which are uncountable.

Important caveat (made explicit here):
- An injection into a *linear order* (e.g. `ℝ`) does **not** imply countability.
  Countability/computability requires a separate effectivity hypothesis (e.g. `Encodable`).
-/

namespace HeytingLean
namespace Bridges

open scoped Real

universe u

/-! ## Two notions of “encoding” -/

/-- A “topological” 1D encoding: inject into the real line. -/
abbrev TopologicalEncoding (T : Type u) : Prop :=
  ∃ encode : T → ℝ, Function.Injective encode

/-- A “computable” encoding: inject into `ℕ` (finite description). -/
abbrev ComputableEncoding (T : Type u) : Prop :=
  ∃ encode : T → ℕ, Function.Injective encode

theorem computableEncoding_of_encodable (T : Type u) [Encodable T] : ComputableEncoding T :=
  ⟨Encodable.encode, Encodable.encode_injective⟩

/-! ## General “1D encoding” into a linear order -/

structure OneDEncoding (T : Type u) where
  carrier : Type _
  instLinearOrder : LinearOrder carrier
  encode : T → carrier
  injective : Function.Injective encode

attribute [instance] OneDEncoding.instLinearOrder

def oneDEncoding_compose {T : Type u} (e1 : OneDEncoding T) (e2 : OneDEncoding e1.carrier) : OneDEncoding T where
  carrier := e2.carrier
  instLinearOrder := e2.instLinearOrder
  encode := e2.encode ∘ e1.encode
  injective := Function.Injective.comp e2.injective e1.injective

/-! ## Miranda: tape/head encoding is already a lossless 1D embedding -/

namespace Miranda

open HeytingLean.MirandaDynamics.Billiards

/-- Tape-only Cantor encoding as a `TopologicalEncoding`. -/
theorem tape_topologicalEncoding : TopologicalEncoding Tape :=
  ⟨encodeTape, encodeTape_injective⟩

/-- Tape+head combined encoding as a `TopologicalEncoding`. -/
theorem tapeHead_topologicalEncoding : TopologicalEncoding (Tape × ℤ) :=
  ⟨fun p => encodeWithHead p.1 p.2, encodeWithHead_injective⟩

/-- Choose `false` as the zero digit for finite-support tapes. -/
instance : Zero Bool := ⟨false⟩

/-- Finite-support tapes (finsupp) have a computable encoding into `ℕ`. -/
abbrev TapeFS : Type :=
  ℤ →₀ Bool

theorem tapeFS_computableEncoding : ComputableEncoding TapeFS :=
  computableEncoding_of_encodable TapeFS

/-- Finite-support tapes also inherit the Cantor-set real embedding by coercion to functions. -/
theorem tapeFS_topologicalEncoding : TopologicalEncoding TapeFS := by
  refine ⟨fun t => encodeTape (fun z => t z), ?_⟩
  intro t₁ t₂ h
  apply Finsupp.ext
  intro z
  have hfun : (fun z => t₁ z) = fun z => t₂ z :=
    encodeTape_injective h
  exact congrArg (fun f => f z) hfun

end Miranda

/-! ## Helix: depth is a 1D base coordinate (under a nondegeneracy assumption) -/

namespace Helix

open HeytingLean.IteratedVirtual.Bridge

theorem helixZ_injective (h : HelixDecomposition) (hnz : h.pitch * h.step ≠ 0) :
    Function.Injective h.z := by
  intro k₁ k₂ hk
  have : (h.pitch * h.step : ℝ) * (k₁ : ℝ) = (h.pitch * h.step : ℝ) * (k₂ : ℝ) := by
    simpa [HelixDecomposition.z, mul_assoc, mul_left_comm, mul_comm] using hk
  have hcast : (k₁ : ℝ) = (k₂ : ℝ) :=
    (mul_left_cancel₀ hnz) this
  exact_mod_cast hcast

end Helix

end Bridges
end HeytingLean
