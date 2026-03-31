import HeytingLean.Noneism.Bridges.OscillatorSheafGlue

/-!
# Noneism.Bridges.OscillatorRegistry

Registry + umbrella import for primordial oscillator unification.
-/

namespace HeytingLean
namespace Noneism
namespace Bridges

/-- All known primordial oscillator carriers. -/
inductive OscillatorTag where
  | bool
  | iterant
  | infoState
  | side
  | genesis
  | sphere
  | star
  | euler
  | preGame
  | clifford
  | linear
  | dialectica
  | ortho
  deriving Repr, DecidableEq

end Bridges
end Noneism
end HeytingLean
