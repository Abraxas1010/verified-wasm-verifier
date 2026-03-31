import HeytingLean.Physics.Substrate.Hilbert
import HeytingLean.Quantum.QChannel

/-!
# CPTP quantum channels (interface-first)

This module provides a *typed* interface for quantum channels between finite
Hilbert substrates.  The goal is to support physics applications (e.g.
photoemission) without forcing an immediate commitment to heavy analytic
infrastructure.

We therefore:
- reuse `HeytingLean.Quantum.KrausChannel` as an optional concrete
  representation (Kraus operators + trace preservation proof);
- treat the map on density matrices as *data* (`apply`), with CPTP-ness recorded
  by a proposition `isCPTP`.

This matches the project’s “structure-first” style: downstream modules can
state and prove theorems from assumptions, while concrete instantiations may
later supply Kraus witnesses and density-preservation proofs.
-/

noncomputable section

namespace HeytingLean
namespace Physics
namespace Channels

open HeytingLean.Physics.Substrate

/-- Kraus representation for a channel between Hilbert substrates. -/
structure KrausDecomposition (H_in H_out : HilbertSubstrate) where
  channel : HeytingLean.Quantum.KrausChannel H_in.dim H_out.dim

namespace KrausDecomposition

variable {H_in H_out : HilbertSubstrate}

/-- Number of Kraus operators. -/
abbrev numOps (K : KrausDecomposition H_in H_out) : ℕ :=
  K.channel.ops.length

/-- Access the `k`-th Kraus operator. -/
abbrev operator (K : KrausDecomposition H_in H_out) (k : Fin K.numOps) :
    Matrix (Fin H_out.dim) (Fin H_in.dim) ℂ :=
  K.channel.ops.get k

/-- The (matrix-level) map induced by a Kraus decomposition. -/
abbrev map (K : KrausDecomposition H_in H_out) :
    HeytingLean.Quantum.Mat H_in.dim → HeytingLean.Quantum.Mat H_out.dim :=
  K.channel.map

end KrausDecomposition

/-- A typed quantum channel between finite Hilbert substrates. -/
structure QuantumChannel (H_in H_out : HilbertSubstrate) where
  /-- Action on density matrices (CPTP intended, recorded separately). -/
  apply : DensityMatrix H_in → DensityMatrix H_out
  /-- Optional Kraus witness. -/
  kraus? : Option (KrausDecomposition H_in H_out) := none
  /-- Predicate asserting this is a CPTP map (interface-first). -/
  isCPTP : Prop := True

namespace QuantumChannel

variable {H₁ H₂ H₃ : HilbertSubstrate}

/-- Channel composition (serial). -/
def comp (E₂ : QuantumChannel H₂ H₃) (E₁ : QuantumChannel H₁ H₂) :
    QuantumChannel H₁ H₃ :=
  { apply := fun ρ => E₂.apply (E₁.apply ρ)
    isCPTP := E₁.isCPTP ∧ E₂.isCPTP }

@[simp] theorem comp_apply (E₂ : QuantumChannel H₂ H₃) (E₁ : QuantumChannel H₁ H₂)
    (ρ : DensityMatrix H₁) :
    (comp E₂ E₁).apply ρ = E₂.apply (E₁.apply ρ) := rfl

/-- Identity channel. -/
def id (H : HilbertSubstrate) : QuantumChannel H H :=
  { apply := fun ρ => ρ
    kraus? := some ⟨HeytingLean.Quantum.KrausChannel.id H.dim⟩
    isCPTP := True }

@[simp] theorem id_apply (H : HilbertSubstrate) (ρ : DensityMatrix H) :
    (id H).apply ρ = ρ := rfl

end QuantumChannel

/-- An isometric channel (unitary embedding) as a refinement of `QuantumChannel`. -/
structure IsometricChannel (H_in H_out : HilbertSubstrate) extends QuantumChannel H_in H_out where
  /-- Isometry witness (interface-first; may be tied to a Kraus witness later). -/
  isometry : Prop

end Channels
end Physics
end HeytingLean

