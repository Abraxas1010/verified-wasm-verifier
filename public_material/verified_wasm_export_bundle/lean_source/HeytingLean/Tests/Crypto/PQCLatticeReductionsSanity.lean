import HeytingLean.Crypto.Lattice.StageBCConstructions
import HeytingLean.Crypto.Lattice.RingReductions
import HeytingLean.Crypto.Lattice.Distributions
import HeytingLean.Crypto.Lattice.FaithfulReductions
import HeytingLean.Crypto.Lattice.NoiseAware

namespace HeytingLean
namespace Tests
namespace Crypto
namespace PQCLatticeReductionsSanity

open HeytingLean.Crypto.Lattice

universe u

def idBridge {S : Type u} (V : RecoveryView S) : Reduction.BridgeData V V where
  mapPub := fun x => x
  mapSecret := fun x => x
  decode := fun _ r => r
  mapInstances := by
    intro s hs
    simpa using hs
  encode_comm := by
    intro s
    rfl
  decode_correct := by
    intro s _hs r hr
    simpa using hr

#check BridgeToTrapdoor
#check BridgeTrapdoorToMLWE
#check BridgeTrapdoorToSIS

-- Concrete v0.9 instantiations (compile coverage)
#check StageBC.stageBPublicView
#check StageBC.stageBBridgeToTrapdoor
#check StageBC.StageC.Faithful.bridgeInvTrapdoorToRingMLWE
#check StageBC.StageC.Faithful.bridgeGadgetTrapdoorToSIS
#check StageBC.StageC.Faithful.bridgeBlockTrapdoorToSIS

#check Rings.Rq
#check Dist.centeredBinomial
#check Dist.uniformMod
#check RingReductions.bridgeRMLWEtoMLWE
#check RingReductions.rqCoeffs
#check RingReductions.rqCoeffs_polyToRq

-- v1.0 faithful reductions (compile coverage)
#check RingMLWE.bridgeInvTrapdoorToMLWE
#check GadgetSIS.bridgeTrapdoorToSIS
#check BlockSIS.bridgeTrapdoorToSIS

-- v1.2 noise-aware view + decode API (compile coverage)
#check RingMLWE.NoisySecret
#check RingMLWE.NoisyView
#check RingMLWE.decodeResidual
#check RingMLWE.decodeByInv

end PQCLatticeReductionsSanity
end Crypto
end Tests
end HeytingLean
