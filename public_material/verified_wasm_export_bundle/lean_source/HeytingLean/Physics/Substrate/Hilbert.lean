import HeytingLean.Quantum.QState

/-!
# Hilbert substrates (finite-dimensional scaffolding)

This module provides a lightweight *typing* layer for physics developments that
want to talk about finite-dimensional Hilbert spaces, density matrices, and CT
attributes without committing to a full quantum mechanics stack.

Implementation note: we reuse the existing `HeytingLean.Quantum.Density n`
record as our density-matrix carrier. This avoids re-proving Hermitian / trace
and positivity boilerplate.
-/

namespace HeytingLean
namespace Physics
namespace Substrate

/-- A finite-dimensional Hilbert space substrate (dimension only, with labels). -/
structure HilbertSubstrate where
  /-- Dimension (finite for now). -/
  dim : ℕ
  /-- Basis labels (purely informational). -/
  basis : Fin dim → String

namespace HilbertSubstrate

/-- Tensor/product substrate (dimension multiplies; labels are schematic). -/
def tensor (H K : HilbertSubstrate) : HilbertSubstrate :=
  { dim := H.dim * K.dim
    basis := fun _ => "⊗" }

end HilbertSubstrate

/-- Density matrix on a Hilbert substrate (reusing `Quantum.Density`). -/
abbrev DensityMatrix (H : HilbertSubstrate) : Type :=
  HeytingLean.Quantum.Density H.dim

/-- CT attribute carrier for quantum substrates: attributes are sets of density matrices. -/
abbrev QuantumAttribute (H : HilbertSubstrate) : Type :=
  DensityMatrix H

end Substrate
end Physics
end HeytingLean

