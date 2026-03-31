import HeytingLean.Topology.Condensed.README

example (t : HeytingLean.Topology.Condensed.CondensedTestObj) (x : Int) :
    HeytingLean.Embeddings.PerspectivalDescentCarrier.truncate
        (τ := HeytingLean.Topology.Condensed.CondensedTestObj)
        (Carrier := fun _ => Int) t 0 x = 0 := by
  exact HeytingLean.Topology.Condensed.truncate_zero t x

example (l : HeytingLean.Embeddings.CoreLensTag) :
    l ∈ HeytingLean.Embeddings.CoreLensTag.all := by
  exact HeytingLean.Topology.Condensed.every_core_lens_is_registered l
