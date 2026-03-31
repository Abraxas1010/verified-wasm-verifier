import HeytingLean.Topology.Condensed.Bridge

namespace HeytingLean
namespace Bridges
namespace Archetype

theorem condensed_to_adelic_finite_support (x : Topology.Condensed.CondensedTestObj → Int) :
    {t | x t ∉ Embeddings.PerspectivalDescentCarrier.integral
      (τ := Topology.Condensed.CondensedTestObj) (Carrier := fun _ => Int) t}.Finite := by
  simpa using (Embeddings.PerspectivalDescentCarrier.finiteness
    (τ := Topology.Condensed.CondensedTestObj) (Carrier := fun _ => Int) x)

end Archetype
end Bridges
end HeytingLean
