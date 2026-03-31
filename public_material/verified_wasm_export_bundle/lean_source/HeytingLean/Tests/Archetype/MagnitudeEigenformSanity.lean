import HeytingLean.Metrics.Magnitude.Homology
import HeytingLean.Metrics.Magnitude.Weighting
import HeytingLean.Metrics.Magnitude.EnrichedMagnitude
import HeytingLean.Metrics.Magnitude.IteratedMH
import HeytingLean.LoF.MRSystems.PolynomialBridge
import HeytingLean.Algebra.SpectralSequence.Paged
import HeytingLean.Algebra.SpectralSequence.RatchetConvergence
import HeytingLean.Bridges.Archetype.MagnitudeEigenformSynthesis
import HeytingLean.Bridges.Archetype.ArchetypeCategory

namespace HeytingLean
namespace Tests
namespace Archetype

open HeytingLean.Bridges.Archetype
open scoped BigOperators

def pathBarToRatchet : BridgePath .barConstruction .jRatchet :=
  BridgePath.cons (a := .barConstruction) (b := .spectralSequence) (c := .jRatchet)
    (by decide)
    (BridgePath.cons (a := .spectralSequence) (b := .jRatchet) (c := .jRatchet)
      (by decide) (BridgePath.nil _))

example :
    Metrics.Magnitude.chainRank (Fin 3) 0 = 3 := by
  simpa [Metrics.Magnitude.finiteMagnitude] using
    Metrics.Magnitude.chainRank_zero_eq_finiteMagnitude (α := Fin 3)

example :
    declaredDirectedBridges.length = 12 := by
  exact declaredDirectedBridges_count

example :
    bridgeChainRank 0 = 17 := by
  exact bridgeChainRank_zero_eq_nodeCount

example :
    bridgeChainRank 0 = Metrics.Magnitude.chainRank ArchetypeNode 0 := by
  exact bridgeChainRank_zero_eq_magnitudeChainRank_zero

example :
    bridgeEulerCut 0 = 17 := by
  exact bridgeEulerCut_zero_eq_nodeCount

example :
    bridgeEulerCutOf (insertDirectedBridge bridgeAdjacent .polynomial .lens) 3 =
      bridgeEulerCut 3 := by
  exact redundant_insertion_preserves_eulerCut .polynomial .lens (by decide) 3

example (g : Bool → Nat) :
    LoF.MRSystems.readerObjEquivApplyFun Bool Nat g =
      ⟨PUnit.unit, g⟩ := by
  rfl

example :
    Metrics.Magnitude.chainRank Bool 1 = 2 := by
  exact Metrics.Magnitude.chainRank_bool_one

example :
    Metrics.Magnitude.chainRank (Fin 3) 1 = 6 := by
  exact Metrics.Magnitude.chainRank_fin3_one

example :
    Metrics.Magnitude.chainRank (Fin 3) 2 = 12 := by
  exact Metrics.Magnitude.chainRank_fin3_two

example (τ : Metrics.Magnitude.MagnitudeChain Bool 0) :
    Metrics.Magnitude.magnitudeDifferential 0 (fun _ => (0 : ℤ)) τ = 0 := by
  simp [Metrics.Magnitude.magnitudeDifferential]

example :
    Metrics.Magnitude.IsMagnitudeWeighting
      (Metrics.Magnitude.discreteSimilarity ArchetypeNode)
      (Metrics.Magnitude.uniformWeighting ArchetypeNode) := by
  exact archetype_uniform_weighting

example :
    Function.IsFixedPt
      (Metrics.Magnitude.weightingFixedPtOp
        (Metrics.Magnitude.discreteSimilarity ArchetypeNode))
      (Metrics.Magnitude.uniformWeighting ArchetypeNode) := by
  exact Metrics.Magnitude.uniformWeighting_fixedPt_discrete ArchetypeNode

example :
    Metrics.Magnitude.magnitudeOfWeighting
      (Metrics.Magnitude.uniformWeighting ArchetypeNode) = 17 := by
  exact archetype_magnitude_eq_17

example :
    Algebra.SpectralSequence.SpectralConvergesAt (fun _ => 5) 5 := by
  apply Algebra.SpectralSequence.spectralConverges_of_ratchet_bounded
  · intro a b _
    simp
  · intro n
    simp

example :
    Algebra.SpectralSequence.PageConverges
      (Algebra.SpectralSequence.pagedOfRatchetAndComplex
        (Metrics.Magnitude.magnitudeChainComplex ArchetypeNode)
        (fun n => Nat.min n 17)
        (by
          intro a b hab
          exact min_le_min_right 17 hab))
      17 := by
  exact archetype_ratchet_converges

example :
    ¬ hasSelfLoop .barConstruction := by
  exact no_self_loops_in_bridge_network .barConstruction

example : pathBarToRatchet.length = 2 := by
  simp [pathBarToRatchet, BridgePath.length]

example :
    (BridgePath.append
      (BridgePath.cons (a := .barConstruction) (b := .spectralSequence)
        (c := .spectralSequence) (by decide) (.nil _))
      (BridgePath.cons (a := .spectralSequence) (b := .jRatchet)
        (c := .jRatchet) (by decide) (.nil _))).length = 2 := by
  simp [BridgePath.length_append, BridgePath.length]

example :
    bridgeDistance .barConstruction .barConstruction = some 0 := by
  exact bridgeDistance_self .barConstruction

example :
    bridgeDistance .barConstruction .spectralSequence = some 1 := by
  exact bridgeDistance_of_directed (a := .barConstruction) (b := .spectralSequence)
    (by decide) (by decide)

example :
    bridgeDistance .rNucleus .barConstruction = none := by
  exact bridgeDistance_none_of_no_direct (a := .rNucleus) (b := .barConstruction)
    (by decide) (by decide)

example :
    Algebra.SpectralSequence.SpectralConvergesAt
      (LoF.Bauer.FixedPoint.kleeneChain (D := Nat) (fun n => Nat.min n 4))
      4 := by
  apply Algebra.SpectralSequence.spectralConverges_kleene_of_fixed
  simp [LoF.Bauer.FixedPoint.kleeneChain]

noncomputable def toyNextToken : Bool → Bool → ℝ
  | false, false => 3 / 4
  | false, true => 1 / 4
  | true, false => 1 / 4
  | true, true => 3 / 4

theorem toyNextToken_nonneg : ∀ p v, 0 ≤ toyNextToken p v := by
  intro p v
  fin_cases p <;> fin_cases v <;> norm_num [toyNextToken]

theorem toyNextToken_norm : ∀ p, Finset.sum Finset.univ (fun v => toyNextToken p v) = 1 := by
  intro p
  fin_cases p <;> norm_num [toyNextToken]

example :
    Metrics.Magnitude.tsallisEntropy 2 (toyNextToken false) =
      1 - Finset.sum Finset.univ (fun v => toyNextToken false v ^ (2 : ℝ)) := by
  simpa using Metrics.Magnitude.tsallisEntropy_two (p := toyNextToken false)

example :
    ∃ p₁ p₂, p₁ ≠ p₂ ∧
      0 < (Metrics.Magnitude.llmEnrichment Bool Bool toyNextToken
        toyNextToken_nonneg toyNextToken_norm).sim p₁ p₂ := by
  refine Metrics.Magnitude.llm_similarity_pos_for_distinct_with_overlap
    Bool Bool toyNextToken toyNextToken_nonneg toyNextToken_norm ?_
  refine ⟨false, true, false, by decide, ?_, ?_⟩ <;> norm_num [toyNextToken]

example :
    Algebra.BarConstruction.BarSimplex Bool 3 ≃
      Metrics.Magnitude.MagnitudeNerve Bool 1 2 := by
  simpa using (Metrics.Magnitude.iteratedMH_one_eq_MH (α := Bool) 2).symm

example :
    Algebra.SpectralSequence.PageConverges
      (Algebra.SpectralSequence.pagedOfRatchetAndComplex
        (Metrics.Magnitude.iteratedMH_spectralSequence Bool 2)
        (fun n => Nat.min n 3)
        (by
          intro a b hab
          exact min_le_min hab (le_rfl)))
      3 := by
  simpa using Metrics.Magnitude.iteratedMH_paged_converges
    (α := Bool) (k := 2) (N := 3)

end Archetype
end Tests
end HeytingLean
