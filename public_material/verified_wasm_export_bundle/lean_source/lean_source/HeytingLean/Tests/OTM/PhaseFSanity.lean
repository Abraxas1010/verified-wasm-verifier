import HeytingLean.OTM.TransfiniteIndex

namespace HeytingLean.Tests.OTM

open HeytingLean.OTM

universe u v

variable {ι : Type u} {α : Type v}
variable [DecidableEq ι] [LoF.PrimaryAlgebra α]

example (M : Machine ι α) (fuel : Nat) :
    (runWithIndex fuel M).1 = Machine.run fuel M :=
  runWithIndex_fst fuel M

example (M : Machine ι α) (fuel : Nat) :
    (runWithIndex fuel M).2 = fuelIndex fuel :=
  runWithIndex_snd fuel M

example (n : Nat) :
    preGameIndex (Numbers.Surreal.TransfinitePreGame.PreGame.nat n) = fuelIndex n :=
  preGameIndex_nat n

example :
    preGameIndex Numbers.Surreal.TransfinitePreGame.PreGame.omega =
      Numbers.Ordinal.OrdinalCNF.omega :=
  preGameIndex_omega

example :
    preGameIndex Numbers.Surreal.TransfinitePreGame.PreGame.omegaTimesTwo =
      Numbers.Ordinal.OrdinalCNF.omega + Numbers.Ordinal.OrdinalCNF.omega :=
  preGameIndex_omegaTimesTwo

example :
    preGameIndex Numbers.Surreal.TransfinitePreGame.PreGame.omega =
      Numbers.Ordinal.OrdinalCNF.omega ∧
      preGameIndex Numbers.Surreal.TransfinitePreGame.PreGame.omegaTimesTwo =
        Numbers.Ordinal.OrdinalCNF.omega + Numbers.Ordinal.OrdinalCNF.omega ∧
      ∀ fuel (M : Machine ι α), (runWithIndex fuel M).2 = fuelIndex fuel :=
  otm_transfinite_index_lane_well_defined

end HeytingLean.Tests.OTM
