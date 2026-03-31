import HeytingLean.Blockchain.PaymentChannels.Specification.PCNGoals
import HeytingLean.Blockchain.PaymentChannels.Algorithmic

namespace HeytingLean
namespace Blockchain
namespace PaymentChannels
namespace Specification

open PTS.BaseExtension
open Algorithmic

def feasibilityProgramOfBool (ok : Bool) (spec : PCNGoalSpec := defaultGoalSpec) : Program :=
  if ok then
    [.atom (.atom spec.feasibleAtom), .atom (.atom spec.liquidityAtom)]
  else
    [.atom (.atom spec.blockedAtom)]

def deriveProgram
    {V : Type u} [DecidableEq V] [Fintype V]
    (G : ChannelGraph V) (w : WealthDist V) (i j : V) (a : Cap)
    (spec : PCNGoalSpec := defaultGoalSpec) : Program :=
  feasibilityProgramOfBool (paymentFeasibleBool (V := V) G w i j a) spec

end Specification
end PaymentChannels
end Blockchain
end HeytingLean
