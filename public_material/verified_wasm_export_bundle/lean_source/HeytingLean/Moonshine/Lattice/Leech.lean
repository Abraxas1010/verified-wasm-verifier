import HeytingLean.Moonshine.Lattice.EvenLattice

set_option autoImplicit false

namespace HeytingLean.Moonshine.Lattice

/--
Predicate form used when we only need the characteristic constraints of the Leech lattice:
rank `24` and rootlessness.
-/
def IsLeechLike (L : EvenLattice) : Prop :=
  L.rank = 24 ∧ Rootless L

/--
Structured Leech-lattice interface used by downstream Moonshine modules.

`unimodular` is kept as a field-level proposition so later work can refine it without changing
the outer API.
-/
structure LeechLatticeData where
  L : EvenLattice
  rank_eq : L.rank = 24
  rootless : Rootless L
  unimodular : Prop

lemma LeechLatticeData.isLeechLike (D : LeechLatticeData) : IsLeechLike D.L :=
  ⟨D.rank_eq, D.rootless⟩

lemma LeechLatticeData.normSq_ne_two (D : LeechLatticeData) (x : D.L.Λ) :
    D.L.normSq x ≠ 2 :=
  D.rootless x

end HeytingLean.Moonshine.Lattice
