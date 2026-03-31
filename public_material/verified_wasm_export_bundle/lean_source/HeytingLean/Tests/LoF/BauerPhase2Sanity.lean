import HeytingLean.LoF.Bauer

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF.Bauer

namespace BauerPhase2

open HeytingLean.LoF.Bauer.SyntheticComputability

abbrev W : World (Ω := Set Bool) :=
  Toy.world

example (p : W.ΩJ) : ((p : Set Bool)ᶜᶜ ≤ (p : Set Bool)) := by
  exact World.markov (W := W) p

example : Countable W.ΩJ :=
  World.countable (W := W)

end BauerPhase2

end LoF
end Tests
end HeytingLean
