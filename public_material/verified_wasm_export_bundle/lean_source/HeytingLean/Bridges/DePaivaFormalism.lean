import HeytingLean.Bridges.LinearLogicBridge
import HeytingLean.CategoryTheory.Dialectica.Monoidal
import HeytingLean.IteratedVirtual.Bridge.ModalCompanion

/-!
# Bridges.DePaivaFormalism

This is a **compile-first** integration point for “de Paiva style” semantics:

- **Dialectica categories** (`Dial C`) as a categorical home for resource-sensitive semantics
  (a standard motivation for linear logic models).
- The repo’s existing **S4 modal companion** correspondence at the provability level.

Scope note:
- We intentionally avoid claiming “□ is a comonad induced by nuclei/local operators” here.
  Nuclei are typically *closure-like* (inflationary), whereas CS4 presentations often model `□`
  as a comonad with `□A → A` (deflationary). Any such identification must be hypothesis-driven.

Primary references (for the mathematical story; not all formalized here):
- Valeria de Paiva, *The Dialectica Categories* (UCAM-CL-TR-213).
- Bierman & de Paiva, “On an Intuitionistic Modal Logic” (Studia Logica, 2000).
- Alechina, Mendler, de Paiva, Ritter, “Categorical and Kripke Semantics for CS4” (CSL 2001).
-/

namespace HeytingLean
namespace Bridges
namespace DePaivaFormalism

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] [HasPullbacks C]

/-- Convenience abbreviation for the Dialectica category over `C`. -/
abbrev DialC := HeytingLean.CategoryTheory.Dialectica.Dial C

/-- `Dial C` is monoidal (already proved in `HeytingLean.CategoryTheory.Dialectica.Monoidal`). -/
noncomputable def dialMonoidal : MonoidalCategory (DialC (C := C)) :=
  inferInstance

/-- `Dial C` is symmetric monoidal (already proved in `HeytingLean.CategoryTheory.Dialectica.Monoidal`). -/
noncomputable def dialSymmetric : SymmetricCategory (DialC (C := C)) :=
  inferInstance

/-- Re-export: Gödel–McKinsey–Tarski “modal companion” correspondence (provability form). -/
theorem gmt_correspondence (φ : LO.Propositional.Formula ℕ) :
    (LO.Propositional.Int ⊢ φ) ↔ (LO.Modal.S4 ⊢ φᵍ) :=
  HeytingLean.IteratedVirtual.Bridge.gmt_correspondence φ

end DePaivaFormalism
end Bridges
end HeytingLean
