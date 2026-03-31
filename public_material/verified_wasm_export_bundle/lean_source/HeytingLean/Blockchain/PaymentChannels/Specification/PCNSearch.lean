import HeytingLean.Blockchain.PaymentChannels.Specification.PCNProgram
import HeytingLean.ATP.Ensemble.HHResolver

namespace HeytingLean
namespace Blockchain
namespace PaymentChannels
namespace Specification

open PTS.BaseExtension
open ATP.Ensemble
open Algorithmic

def pcn_search
    {V : Type u} [DecidableEq V] [Fintype V]
    (fuel : Nat)
    (G : ChannelGraph V) (w : Algorithmic.WealthDist V) (i j : V) (a : Cap)
    (spec : PCNGoalSpec := defaultGoalSpec) : Bool :=
  hh_search fuel (deriveProgram (V := V) G w i j a spec) (.atom spec.feasibleAtom)

end Specification
end PaymentChannels
end Blockchain
end HeytingLean
