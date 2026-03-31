import HeytingLean.LoF.Bauer

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF.Bauer

namespace BauerDomains

open scoped Classical

abbrev Dom : CountablyBasedDomain (D := Set Bool) :=
  HeytingLean.LoF.Bauer.Toy.domain

example (n : Nat) : OmegaCompact (D := Set Bool) (Dom.basis n) :=
  CountablyBasedDomain.omegaCompact_basis (D := Set Bool) (Dom := Dom) n

example : OmegaCompact (D := Set Bool) ({false} : Set Bool) := by
  simpa using (HeytingLean.LoF.Bauer.Toy.omegaCompact_all (k := ({false} : Set Bool)))

end BauerDomains

end LoF
end Tests
end HeytingLean

