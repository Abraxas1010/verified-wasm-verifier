import HeytingLean.CategoryTheory.Polynomial.Basic
import HeytingLean.Embeddings.CoreLenses

namespace HeytingLean
namespace CategoryTheory
namespace Polynomial

open _root_.CategoryTheory.Polynomial

universe u v w

theorem applyMap_id (p : Poly.{u, v}) (T : Type w) :
    applyMap (polyid p) T = id := by
  funext x
  cases x
  rfl

theorem applyMap_comp {p q r : Poly.{u, v}} (f : polymap p q) (g : polymap q r) (T : Type w) :
    applyMap (composemap f g) T = applyMap g T ∘ applyMap f T := by
  funext x
  cases x
  rfl

def coreLensCarrierPoly : Poly := (Embeddings.CoreLensTag y^PUnit)

theorem core_lens_poly_positions :
    coreLensCarrierPoly.pos = Embeddings.CoreLensTag := by
  rfl

theorem core_lens_all_mem_positions (l : Embeddings.CoreLensTag) :
    l ∈ Embeddings.CoreLensTag.all := by
  exact Embeddings.CoreLensTag.mem_all l

end Polynomial
end CategoryTheory
end HeytingLean
