import HeytingLean.Bridges.DePaivaFormalism

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits

namespace HeytingLean.Tests.Bridges.DePaivaFormalismSanity

universe v u

variable (C : Type u) [Category.{v} C] [HasFiniteProducts C] [HasPullbacks C]

-- Dialectica is symmetric monoidal (multiplicative linear logic fragment).
#check (inferInstance :
  MonoidalCategory (HeytingLean.CategoryTheory.Dialectica.Dial C))

#check (inferInstance :
  SymmetricCategory (HeytingLean.CategoryTheory.Dialectica.Dial C))

-- Modal companion re-export is available.
#check HeytingLean.Bridges.DePaivaFormalism.gmt_correspondence

end HeytingLean.Tests.Bridges.DePaivaFormalismSanity

