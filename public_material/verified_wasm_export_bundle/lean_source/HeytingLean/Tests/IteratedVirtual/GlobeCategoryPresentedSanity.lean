import HeytingLean.IteratedVirtual.GlobeCategoryPresented

/-!
# Tests.IteratedVirtual.GlobeCategoryPresentedSanity

Compile-only checks for the presented globe category definition.
-/

namespace HeytingLean
namespace Tests
namespace IteratedVirtual

open HeytingLean.IteratedVirtual
open HeytingLean.IteratedVirtual.GlobeCategoryPresented

section
  #check GlobeCategoryPresented.GlobeCat
  #check GlobeCategoryPresented.GlobeCat.sigma_sigma_eq_sigma_tau
  #check GlobeCategoryPresented.ToGlobularIndex.functor
end

end IteratedVirtual
end Tests
end HeytingLean

