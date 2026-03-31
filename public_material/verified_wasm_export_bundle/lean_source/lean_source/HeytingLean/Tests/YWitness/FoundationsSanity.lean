import HeytingLean.Genesis.YWitness.WitnessDuality
import HeytingLean.Numbers.Surreal.YWitness
import HeytingLean.LoF.Bauer.DoubleNegation

namespace HeytingLean.Tests.YWitness

open HeytingLean.Genesis.YWitness

def boolSeed : ReentrySeed Bool where
  seq
    | 0 => false
    | _ + 1 => true
  nonconstant := ⟨0, by decide⟩

def boolWitness : ContinuousWitness Bool where
  oscillation := boolSeed.seq
  bounded := by
    intro n
    cases n <;> simp [boolSeed]
  nonconstant := boolSeed.nonconstant

example : Regenerates false boolSeed := by
  exact ⟨rfl, boolSeed.nonconstant⟩

example : AdjacentNonconstant boolWitness.oscillation := boolWitness.nonconstant

example :
    (crystallizedWitness (HeytingLean.LoF.Bauer.doubleNegNucleus Bool)).is_fixed =
      crystallizationPoint_fixed (HeytingLean.LoF.Bauer.doubleNegNucleus Bool) := by
  rfl

example :
    HeytingLean.Numbers.SurrealCore.canonicalize
        HeytingLean.Numbers.SurrealCore.nullCut ∈
      (HeytingLean.Numbers.Surreal.YWitness.ofPreGame
        HeytingLean.Numbers.SurrealCore.nullCut).closureCarrier := by
  exact HeytingLean.Numbers.Surreal.YWitness.canonicalized_mem_closureCarrier _

example :
  (HeytingLean.Numbers.Surreal.YWitness.ofPreGame
      HeytingLean.Numbers.SurrealCore.nullCut).raw =
        HeytingLean.Numbers.SurrealCore.nullCut := by
  rfl

end HeytingLean.Tests.YWitness
