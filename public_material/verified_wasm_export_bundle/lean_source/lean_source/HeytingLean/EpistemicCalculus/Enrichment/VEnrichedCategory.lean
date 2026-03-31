import HeytingLean.EpistemicCalculus.Basic

namespace HeytingLean.EpistemicCalculus.Enrichment

/--
A `V`-enriched category in the posetal setting induced by an epistemic calculus.
`hom x y : V` is a `V`-valued relation between objects.
-/
structure VEnrichedCat (V : Type*) [EpistemicCalculus V] where
  Obj : Type*
  hom : Obj → Obj → V
  identity : ∀ x : Obj, EpistemicCalculus.unit ≤ hom x x
  composition : ∀ x y z : Obj, hom y z fus hom x y ≤ hom x z

end HeytingLean.EpistemicCalculus.Enrichment
