import HeytingLean.EpistemicCalculus.Enrichment.VEnrichedCategory
import HeytingLean.EpistemicCalculus.Axioms

namespace HeytingLean.EpistemicCalculus.Updating

open HeytingLean.EpistemicCalculus.Enrichment

/--
`V`-updating of an enriched hypothesis category at evidence object `E`.

The updated hom is
`ihom (hom x y fus hom y E) (hom x E)`.
To guarantee a lawful enriched category, we expose the two proof obligations used
in the identity and composition laws as explicit hypotheses.
-/
def vUpdate {V : Type*} [EpistemicCalculus V] [Closed V]
    (H : VEnrichedCat V) (E : H.Obj)
    (hid : ∀ x : H.Obj, H.hom x x fus H.hom x E ≤ H.hom x E)
    (hcomp :
      ∀ x y z : H.Obj,
        Closed.ihom (H.hom y z fus H.hom z E) (H.hom y E) fus
            Closed.ihom (H.hom x y fus H.hom y E) (H.hom x E) ≤
          Closed.ihom (H.hom x z fus H.hom z E) (H.hom x E)) :
    VEnrichedCat V where
  Obj := H.Obj
  hom := fun x y => Closed.ihom (H.hom x y fus H.hom y E) (H.hom x E)
  identity := by
    intro x
    have hbase : EpistemicCalculus.unit fus (H.hom x x fus H.hom x E) ≤ H.hom x E := by
      simpa [EpistemicCalculus.fusion_unit_left] using hid x
    exact (Closed.adjunction EpistemicCalculus.unit (H.hom x x fus H.hom x E) (H.hom x E)).1 hbase
  composition := by
    intro x y z
    exact hcomp x y z

theorem vUpdate_hom {V : Type*} [EpistemicCalculus V] [Closed V]
    (H : VEnrichedCat V) (E : H.Obj)
    (hid : ∀ x : H.Obj, H.hom x x fus H.hom x E ≤ H.hom x E)
    (hcomp :
      ∀ x y z : H.Obj,
        Closed.ihom (H.hom y z fus H.hom z E) (H.hom y E) fus
            Closed.ihom (H.hom x y fus H.hom y E) (H.hom x E) ≤
          Closed.ihom (H.hom x z fus H.hom z E) (H.hom x E))
    (x y : H.Obj) :
    (vUpdate H E hid hcomp).hom x y =
      Closed.ihom (H.hom x y fus H.hom y E) (H.hom x E) := rfl

end HeytingLean.EpistemicCalculus.Updating
