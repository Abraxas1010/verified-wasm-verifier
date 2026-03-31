import HeytingLean.Crypto.Games.INDCCA

namespace HeytingLean.Tests.Crypto.PQCGamesSanity

open HeytingLean.Crypto.Games

noncomputable section

def toyKEM : KEM where
  PK := Unit
  SK := Unit
  CT := Bool
  SS := Bool
  keygen := PMF.pure ((), ())
  encaps := fun _pk => PMF.pure (true, true)
  decaps := fun _sk _ct => some false

def toyAdversary : INDCCAAdversary toyKEM where
  run := fun _pk _ctStar _ss _oracle =>
    PMF.pure true

noncomputable def toyAdv : ℝ :=
  INDCCA.advantage (K := toyKEM) (A := toyAdversary)

end

end HeytingLean.Tests.Crypto.PQCGamesSanity
