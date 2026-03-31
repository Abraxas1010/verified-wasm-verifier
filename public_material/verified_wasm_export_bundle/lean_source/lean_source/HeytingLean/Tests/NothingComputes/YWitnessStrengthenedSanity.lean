import HeytingLean.Genesis.NothingComputes.FullChain

namespace HeytingLean.Tests.NothingComputes

open Order
open HeytingLean.Genesis.YWitness
open HeytingLean.Numbers.Surreal.NoneistKripke
open HeytingLean.LoF.Combinators.SKYUniversality

noncomputable def topWitness : ContinuousWitness Bool where
  oscillation := nucleusApprox (⊤ : Nucleus Bool)
  bounded := nucleusApprox_bounded (R := (⊤ : Nucleus Bool))
  nonconstant := ⟨0, by simp [nucleusApprox]⟩

noncomputable def topSeed : ReentrySeed Bool where
  seq
    | 0 => crystallizationPoint (⊤ : Nucleus Bool)
    | _ + 1 => false
  nonconstant := ⟨0, by simp [crystallizationPoint]⟩

def varyingWorld : World := { stage := 1, mode := .possible }

def sampleProgram : SelfProgram := repeatedUnfold HeytingLean.LoF.Comb.K 1

example :
    let strengthened :=
      HeytingLean.Genesis.NothingComputes.strengthenedPhase
        (⊤ : Nucleus Bool) topWitness topSeed varyingWorld
        HeytingLean.Numbers.SurrealCore.nullCut false sampleProgram
    strengthened.noneism ∧ strengthened.witness ∧ strengthened.selfReference ∧
      strengthened.foundations ∧ strengthened.surreal ∧
      strengthened.booleanCore ∧ strengthened.computation := by
  exact HeytingLean.Genesis.NothingComputes.strengthened_y_witness
    (R := (⊤ : Nucleus Bool))
    (cw := topWitness)
    (hcw := follows_refl _)
    (seed := topSeed)
    (hseed := rfl)
    (w := varyingWorld)
    (hw := by simp [varyingWorld])
    (g := HeytingLean.Numbers.SurrealCore.nullCut)
    (a := false)
    (program := sampleProgram)
