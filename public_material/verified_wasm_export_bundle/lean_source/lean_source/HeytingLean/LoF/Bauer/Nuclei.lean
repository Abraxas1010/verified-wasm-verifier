import Mathlib.Order.Nucleus
import HeytingLean.LoF.PrimaryAlgebra

/-!
# Bauer: nuclei as Lawvere–Tierney local operators

Mathlib models a (localic) Lawvere–Tierney topology as a `Nucleus` on a frame.
This file provides a small “HeytingLean-facing” API layer and a few
high-value facts used in the Bauer integration plan:

* nuclei on a frame form a complete lattice and a Heyting algebra;
* inclusion of ranges corresponds to the order on nuclei.
-/

namespace HeytingLean
namespace LoF
namespace Bauer

open scoped Classical

universe u

variable {α : Type u} [PrimaryAlgebra α]

/-- Nuclei on a frame form a Heyting algebra (Lawvere–Tierney operators form a Heyting algebra). -/
example : HeytingAlgebra (Nucleus α) := by infer_instance

/-- Nuclei on a frame form a complete lattice (Lawvere–Tierney operators form a complete lattice). -/
example : CompleteLattice (Nucleus α) := by infer_instance

variable {n m : Nucleus α}

/-- Range inclusion corresponds to order on nuclei (reversed): `range m ⊆ range n ↔ n ≤ m`. -/
theorem range_subset_range_iff : Set.range m ⊆ Set.range n ↔ n ≤ m :=
  _root_.Nucleus.range_subset_range (m := m) (n := n)

end Bauer
end LoF
end HeytingLean
