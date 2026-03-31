import HeytingLean.Topology.Condensed.Basic
import HeytingLean.Embeddings.CoreLenses

namespace HeytingLean
namespace Topology
namespace Condensed

theorem every_core_lens_is_registered (l : Embeddings.CoreLensTag) :
    l ∈ Embeddings.CoreLensTag.all :=
  Embeddings.CoreLensTag.mem_all l

theorem condensed_truncation_bridge (t : CondensedTestObj) (x : Int) :
    Embeddings.PerspectivalDescentCarrier.truncate
        (τ := CondensedTestObj) (Carrier := fun _ => Int) t 0 x = 0 :=
  truncate_zero t x

end Condensed
end Topology
end HeytingLean
