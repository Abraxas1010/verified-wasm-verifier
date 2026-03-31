import HeytingLean.Topos.SheafBridges

namespace HeytingLean
namespace Tests
namespace Topos

open CategoryTheory

/-! Tiny presheaf-site smoke test (type-level only). -/

section
  universe u v w
  variable (C : Type u) [Category.{v} C]
  variable (A : Type w) [Category.{max v w} A]
  variable (J : GrothendieckTopology C)

  -- Sheafification functor and adjunction names should typecheck through our facade.
  variable [CategoryTheory.HasWeakSheafify J A]
  #check HeytingLean.Topos.SheafBridges.presheafToSheaf (C := C) (A := A) J
  #check HeytingLean.Topos.SheafBridges.sheafificationAdjunction (C := C) (A := A) J
end

end Topos
end Tests
end HeytingLean
