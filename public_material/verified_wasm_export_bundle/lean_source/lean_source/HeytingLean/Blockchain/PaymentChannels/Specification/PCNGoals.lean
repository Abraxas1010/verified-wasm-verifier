import HeytingLean.PTS.BaseExtension.Main

namespace HeytingLean
namespace Blockchain
namespace PaymentChannels
namespace Specification

open PTS.BaseExtension

structure PCNGoalSpec where
  feasibleAtom : Atom
  blockedAtom : Atom
  liquidityAtom : Atom
  deriving Repr

def defaultGoalSpec : PCNGoalSpec :=
  { feasibleAtom := ⟨9000⟩, blockedAtom := ⟨9001⟩, liquidityAtom := ⟨9002⟩ }

def feasibilityFormula (spec : PCNGoalSpec := defaultGoalSpec) : IPL :=
  .atom spec.feasibleAtom

def blockedFormula (spec : PCNGoalSpec := defaultGoalSpec) : IPL :=
  .atom spec.blockedAtom

def liquidityFormula (spec : PCNGoalSpec := defaultGoalSpec) : IPL :=
  .atom spec.liquidityAtom

end Specification
end PaymentChannels
end Blockchain
end HeytingLean
