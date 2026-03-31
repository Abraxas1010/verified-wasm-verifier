import HeytingLean.Bridges.Matula

namespace HeytingLean
namespace Tests
namespace Bridges
namespace MatulaSanity

open HeytingLean.Bridges

example (a : Matula.Omega) :
    Matula.contract.decode (Matula.contract.encode a) = a := by
  exact Matula.contract.round a

example (x : Matula.Carrier) : Matula.fromGraph (Matula.toGraph x) = x := by
  exact Matula.rt1 x

example (x : Matula.GraphCarrier) : Matula.toGraph (Matula.fromGraph x) = x := by
  exact Matula.rt2 x

example : Matula.toPlatoTree (Matula.fromPlatoTree 12) = 12 := by
  native_decide

example : Matula.toPlatoTree (Matula.fromPlatoTree 1) = 1 := by
  native_decide

example : Matula.toPlatoTree (Matula.fromPlatoTree 60) = 60 := by
  native_decide

end MatulaSanity
end Bridges
end Tests
end HeytingLean
