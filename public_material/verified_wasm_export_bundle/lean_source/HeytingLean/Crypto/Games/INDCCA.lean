import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# IND-CCA game (PMF skeleton)

This module provides a minimal, **executable** definition of the IND-CCA game for a KEM, using
`PMF` from Mathlib as the randomness carrier.

Scope:
- A lightweight game definition with a single “challenge ciphertext + decapsulation oracle”.
- A real-valued advantage definition, suitable as a target for future reductions.

Non-goals (for now):
- PPT/QPT adversary modeling, oracle interaction traces, and full game-hopping proofs.
- Any claim that ML-KEM satisfies IND-CCA (kept separate; see `MLKEMAxioms.lean`).
-/

namespace HeytingLean
namespace Crypto
namespace Games

open scoped BigOperators

/-- KEM interface suitable for defining IND-CCA games via `PMF`. -/
structure KEM where
  PK : Type
  SK : Type
  CT : Type
  SS : Type
  [ctDecEq : DecidableEq CT]
  [ssFintype : Fintype SS]
  [ssNonempty : Nonempty SS]
  keygen : PMF (PK × SK)
  encaps : PK → PMF (CT × SS)
  decaps : SK → CT → Option SS

attribute [instance] KEM.ctDecEq KEM.ssFintype KEM.ssNonempty

/-- IND-CCA adversary: gets `(pk, ct*, ss_b)` and access to a decapsulation oracle. -/
structure INDCCAAdversary (K : KEM) where
  run : K.PK → K.CT → K.SS → (K.CT → Option K.SS) → PMF Bool

namespace INDCCA

variable (K : KEM) (A : INDCCAAdversary K)

noncomputable def uniformSS : PMF K.SS :=
  PMF.uniformOfFintype K.SS

/-- The IND-CCA game output distribution for a fixed challenge bit `b`. -/
noncomputable def game (b : Bool) : PMF Bool :=
  K.keygen.bind fun (pk, sk) =>
    (K.encaps pk).bind fun (ctStar, ss0) =>
      (uniformSS (K := K)).bind fun ss1 =>
        let ssB := if b then ss0 else ss1
        let oracle : K.CT → Option K.SS :=
          fun ct => if ct = ctStar then none else K.decaps sk ct
        A.run pk ctStar ssB oracle

noncomputable def winProb (b : Bool) : ℝ :=
  ((game (K := K) (A := A) b) true).toReal

noncomputable def advantage : ℝ :=
  |winProb (K := K) (A := A) true - winProb (K := K) (A := A) false|

end INDCCA

end Games
end Crypto
end HeytingLean
