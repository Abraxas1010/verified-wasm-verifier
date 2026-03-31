import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Finite

namespace HeytingLean
namespace Topos
namespace SheafBridges

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C]
variable {A : Type w} [Category.{max v w} A]
variable (J : GrothendieckTopology C)

/-- Alias to the sheafification functor, left adjoint to inclusion. -/
noncomputable abbrev presheafToSheaf [CategoryTheory.HasWeakSheafify J A] :
    (Cᵒᵖ ⥤ A) ⥤ Sheaf J A :=
  CategoryTheory.presheafToSheaf J A

/-- The sheafification-inclusion adjunction. -/
noncomputable def sheafificationAdjunction [CategoryTheory.HasWeakSheafify J A] :
    CategoryTheory.presheafToSheaf J A ⊣ CategoryTheory.sheafToPresheaf J A :=
  CategoryTheory.sheafificationAdjunction J A

/-- Left-exactness of the reflector under `HasSheafify`. -/
noncomputable def preservesFiniteLimits_presheafToSheaf [CategoryTheory.HasSheafify J A] :
    CategoryTheory.Limits.PreservesFiniteLimits (CategoryTheory.presheafToSheaf J A) :=
  inferInstance

end SheafBridges
end Topos
end HeytingLean
