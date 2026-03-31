import HeytingLean.Crypto.Lattice.NoiseDistributions
import HeytingLean.Crypto.Lattice.NoiseMLWE

namespace HeytingLean
namespace Tests
namespace Crypto
namespace PQCLatticeNoiseSanity

open HeytingLean.Crypto.Lattice

#check NoiseMLWEInstance
#check NoiseDecode
#check NoiseDist.CenteredBinomialShape
#check NoiseDist.UniformModShape

def toyParams : MLWEParams :=
  { n := 1, q := 17, k := 1 }

noncomputable def toyS : ModVec toyParams.k toyParams.n toyParams.q :=
  fun _i => fun _j => 1

noncomputable def toyInst : NoiseMLWEInstance toyParams :=
  { A := 1
    s := toyS
    e := 0
    b := toyS
    eqn := by simp }

example :
    (idOnlyDecode toyParams).decode toyInst.A toyInst.b = some toyInst.s := by
  refine (idOnlyDecode toyParams).correct toyInst ?_ ?_
  · simp [idOnlyDecode, idOnlyInstances, toyInst]
  · simpa [toyInst] using (boundedNatRep_zero toyParams 0)

/-!
## CBD boundedness smoke

The deterministic centered-binomial sampler is *shape-only*, but its outputs should still be
bounded in the centered `coeffBound` sense when `q > 2η`.
-/

open NoiseDist

def seed0 : Dist.Seed := { bytes := ByteArray.empty }

example :
    coeffBound (q := 17)
      ((NoiseDist.centeredBinomialFromDist 3 1 17).sample seed0 ⟨0, by decide⟩) ≤ 3 := by
  haveI : NeZero 17 := ⟨by decide⟩
  simpa using
    (NoiseDist.centeredBinomialFromDist_coeffBound_le (η := 3) (n := 1) (q := 17)
      (hη := by decide) (hq := by decide) seed0 ⟨0, by decide⟩)

end PQCLatticeNoiseSanity
end Crypto
end Tests
end HeytingLean
