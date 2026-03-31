import HeytingLean.Quantum.OML.Examples.Hilbert2

/-!
# QGI-style two-path OML example

This module packages a minimal orthomodular lattice `β` for use in the
Quantum Galileo Interferometer (QGI) example. It reuses the existing
`H2` instance and designates two distinguished propositions:

* `labPath`   – “wave packet in the laboratory arm”,
* `freePath`  – “wave packet in the free-fall arm”.

These are modelled as the two non-trivial atoms of the Boolean lattice
`H2`, and we record a couple of small lemmas about their orthogonality
and span.
-/

open scoped Classical

namespace HeytingLean
namespace Quantum
namespace OML

open H2

/-- The orthomodular carrier for the QGI example. For now this is
    just the existing `H2` Boolean OML. -/
abbrev QGIβ := H2

namespace QGIInterferometer

/-- Proposition corresponding to the “laboratory arm” of the
    interferometer. -/
def labPath : QGIβ := H2.X

/-- Proposition corresponding to the “free-fall arm” of the
    interferometer. -/
def freePath : QGIβ := H2.Y

/-- The two path propositions are orthogonal in this lattice. -/
@[simp] lemma inf_lab_free :
    (labPath ⊓ freePath : QGIβ) = ⊥ := by
  -- By construction of `H2.inf`, `X ⊓ Y = ⊥`.
  rfl

/-- Orthogonality is symmetric. -/
@[simp] lemma inf_free_lab :
    (freePath ⊓ labPath : QGIβ) = ⊥ := by
  -- By construction of `H2.inf`, `Y ⊓ X = ⊥`.
  rfl

/-- The join of the two paths covers the non-trivial two-dimensional
    subspace of this lattice (here, the entire non-bottom part). -/
@[simp] lemma sup_lab_free :
    (labPath ⊔ freePath : QGIβ) = ⊤ := by
  -- By construction of `H2.sup`, `X ⊔ Y = ⊤`.
  rfl

end QGIInterferometer

end OML
end Quantum
end HeytingLean
