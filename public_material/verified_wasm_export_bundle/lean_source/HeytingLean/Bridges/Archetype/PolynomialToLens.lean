import HeytingLean.CategoryTheory.Polynomial.ArchetypeBridge
import HeytingLean.Embeddings.CoreLenses

namespace HeytingLean
namespace Bridges
namespace Archetype

open _root_.CategoryTheory.Polynomial
open HeytingLean.CategoryTheory.Polynomial

theorem polynomial_lens_id_on_core_state (T : Type)
    (x : applyFun coreLensCarrierPoly T) :
    applyMap (polyid coreLensCarrierPoly) T x = x := by
  simpa using congrArg (fun f => f x) (applyMap_id coreLensCarrierPoly T)

theorem polynomial_lens_comp_on_core_state
    {q r : Poly} (f : polymap coreLensCarrierPoly q) (g : polymap q r) (T : Type)
    (x : applyFun coreLensCarrierPoly T) :
    applyMap (composemap f g) T x = applyMap g T (applyMap f T x) := by
  simpa using congrArg (fun h => h x) (applyMap_comp f g T)

end Archetype
end Bridges
end HeytingLean
