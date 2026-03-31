import HeytingLean.EpistemicCalculus.Enrichment.VEnrichedCategory
import HeytingLean.EpistemicCalculus.ChangeOfCalculi.Conservative

namespace HeytingLean.EpistemicCalculus.Enrichment

open HeytingLean.EpistemicCalculus.ChangeOfCalculi

/--
A conservative change of calculi `F : V → W` transports `V`-enriched categories to
`W`-enriched categories by mapping each hom-object through `F`.
-/
def changeEnrichment {V W : Type*} [EpistemicCalculus V] [EpistemicCalculus W]
    (F : ConservativeChange V W) (C : VEnrichedCat V) : VEnrichedCat W where
  Obj := C.Obj
  hom := fun x y => F.map (C.hom x y)
  identity := by
    intro x
    exact le_trans F.lax_unit (F.monotone (C.identity x))
  composition := by
    intro x y z
    calc
      F.map (C.hom y z) fus F.map (C.hom x y)
          ≤ F.map (C.hom y z fus C.hom x y) := F.lax_monoidal _ _
      _ ≤ F.map (C.hom x z) := F.monotone (C.composition x y z)

end HeytingLean.EpistemicCalculus.Enrichment
