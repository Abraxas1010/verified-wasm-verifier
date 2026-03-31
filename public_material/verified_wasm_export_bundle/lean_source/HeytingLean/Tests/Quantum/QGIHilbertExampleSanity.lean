import HeytingLean.Quantum.OML.Examples.QGIInterferometer
import HeytingLean.Quantum.OML.Examples.QGIHilbert2

/-
Compile-only sanity checks for the QGI Hilbert-space witness:

* availability of the concrete subspaces corresponding to the four
  Boolean lattice elements;
* basic shape of the `toHilbertSubspace` map.
-/

namespace HeytingLean.Tests.Quantum

open HeytingLean.Quantum
open HeytingLean.Quantum.OML
open HeytingLean.Quantum.OML.QGIInterferometer
open HeytingLean.Quantum.OML.QGIHilbert2

/- Sanity: the two one-dimensional subspaces are available. -/
#check subLab
#check subFree

/- Sanity: the embedding from `QGIβ` into subspaces of `QGIH` is available. -/
#check toHilbertSubspace

/-- Sanity: `⊥` and `⊤` in `QGIβ` map to bottom and top subspaces. -/
example :
    toHilbertSubspace (H2.bot : QGIβ) = ⊥ ∧
    toHilbertSubspace (H2.top : QGIβ) = ⊤ := by
  constructor <;> simp

end HeytingLean.Tests.Quantum
