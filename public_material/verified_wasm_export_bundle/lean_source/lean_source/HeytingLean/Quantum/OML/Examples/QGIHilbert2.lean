import Mathlib
import HeytingLean.Quantum.OML.Examples.Hilbert2
import HeytingLean.Quantum.OML.Examples.QGIInterferometer

/-
# QGI-style Hilbert-space witness (finite-dimensional)

This optional example ties the finite Boolean OML `H2` used in the QGI
example to an actual finite-dimensional complex vector space. It does
**not** replace `QGIβ := H2` as the logical carrier; instead it provides
concrete Hilbert-space subspaces corresponding to the four lattice
elements.

Design:
* Take `H := Fin 2 → ℂ` as a simple model of `ℂ²`.
* Define basis-like vectors `eLab`, `eFree : H`.
* Define rank‑1 submodules `subLab`, `subFree` spanned by those basis
  vectors.
* Provide a map `toHilbertSubspace : QGIβ → Submodule ℂ H` that sends:
  - `⊥ ↦ ⊥`, `⊤ ↦ ⊤`,
  - `labPath ↦ subLab`,
  - `freePath ↦ subFree`.

This keeps all heavy analysis in mathlib and leaves the existing OML
structure on `QGIβ` unchanged.
-/

open scoped Classical

namespace HeytingLean
namespace Quantum
namespace OML

open H2
open QGIInterferometer

/-- Underlying complex vector space used for the QGI Hilbert witness.
    We use the simple model `ℂ² ≃ Fin 2 → ℂ`. -/
abbrev QGIH : Type := Fin 2 → ℂ

namespace QGIHilbert2

/-- Basis-like vector representing the laboratory arm in `QGIH`. -/
def eLab : QGIH :=
  fun i => if i = 0 then (1 : ℂ) else 0

/-- Basis-like vector representing the free-fall arm in `QGIH`. -/
def eFree : QGIH :=
  fun i => if i = 1 then (1 : ℂ) else 0

/-- One-dimensional subspace spanned by the laboratory arm. -/
noncomputable def subLab : Submodule ℂ QGIH :=
  Submodule.span ℂ {eLab}

/-- One-dimensional subspace spanned by the free-fall arm. -/
noncomputable def subFree : Submodule ℂ QGIH :=
  Submodule.span ℂ {eFree}

/-- Map from the Boolean QGI lattice `QGIβ` into concrete subspaces of
    `QGIH`. This does **not** claim to be surjective onto all closed
    subspaces; it only witnesses the four distinguished elements. -/
noncomputable def toHilbertSubspace : QGIβ → Submodule ℂ QGIH
  | H2.bot => ⊥
  | H2.top => ⊤
  | H2.X   => subLab
  | H2.Y   => subFree

@[simp] lemma toHilbertSubspace_bot :
    toHilbertSubspace (H2.bot : QGIβ) = ⊥ := rfl

@[simp] lemma toHilbertSubspace_top :
    toHilbertSubspace (H2.top : QGIβ) = ⊤ := rfl

@[simp] lemma toHilbertSubspace_lab :
    toHilbertSubspace labPath = subLab := rfl

@[simp] lemma toHilbertSubspace_free :
    toHilbertSubspace freePath = subFree := rfl

end QGIHilbert2

end OML
end Quantum
end HeytingLean
