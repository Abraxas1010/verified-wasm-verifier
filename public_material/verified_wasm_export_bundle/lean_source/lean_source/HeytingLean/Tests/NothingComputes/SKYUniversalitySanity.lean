import HeytingLean.LoF.Combinators.SKYUniversality

namespace HeytingLean.Tests.NothingComputes

open HeytingLean.LoF.Combinators.SKYUniversality

def sampleProgram : SelfProgram := repeatedUnfold HeytingLean.LoF.Comb.K 2

example :
    encode (decode (encode sampleProgram)) = encode sampleProgram := by
  exact decode_encode sampleProgram

example :
    encode sampleProgram =
      HeytingLean.Computation.YWitness.yProductiveSequence HeytingLean.LoF.Comb.K 2 := by
  simpa [sampleProgram] using encode_repeatedUnfold HeytingLean.LoF.Comb.K 2

example :
    HeytingLean.LoF.Comb.Step
      (encode (.unfold sampleProgram))
      (HeytingLean.LoF.Comb.app (encode sampleProgram) (encode (.unfold sampleProgram))) := by
  exact encode_unfold_step sampleProgram

end HeytingLean.Tests.NothingComputes
