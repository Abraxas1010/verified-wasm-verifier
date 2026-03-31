import Foundation.Modal.ModalCompanion.Int

/-!
# IteratedVirtual.Bridge.ModalCompanion

Strict-only: re-export the Gödel–McKinsey–Tarski (“modal companion”) correspondence from the
`Foundation` dependency.

In particular, `Foundation` provides a Gödel translation `φ ↦ φᵍ` from propositional formulas
to modal formulas, and proves that intuitionistic provability is equivalent to S4 provability
of the Gödel translation.

This is intentionally *provability-level* (Hilbert systems), not a separate development of
Kripke semantics inside HeytingLean.
-/

namespace HeytingLean
namespace IteratedVirtual
namespace Bridge

open LO
open LO.Entailment

/-- Gödel–McKinsey–Tarski correspondence (provability form): `Int ⊢ φ ↔ S4 ⊢ φᵍ`. -/
theorem gmt_correspondence (φ : LO.Propositional.Formula ℕ) :
    (LO.Propositional.Int ⊢ φ) ↔ (LO.Modal.S4 ⊢ φᵍ) := by
  simpa using
    (LO.Modal.ModalCompanion.companion (IL := LO.Propositional.Int) (ML := LO.Modal.S4) (φ := φ))

end Bridge
end IteratedVirtual
end HeytingLean

