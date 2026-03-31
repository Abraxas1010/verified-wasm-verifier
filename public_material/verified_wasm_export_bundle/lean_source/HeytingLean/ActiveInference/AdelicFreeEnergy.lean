import HeytingLean.ActiveInference.Agent
import HeytingLean.Embeddings.Adelic
import HeytingLean.Embeddings.CoreLenses
import HeytingLean.Embeddings.LensIDCoreBridge

/-!
# ActiveInference.AdelicFreeEnergy

Scaffolding for “multi-scale” (lens-indexed) objectives: each adelic lens can contribute its own
free energy term, with a restricted-product style finiteness condition.
-/

namespace HeytingLean
namespace ActiveInference

open HeytingLean.Embeddings

/-- Free energy decomposed across a generic perspective index. -/
structure GenericAdelicFreeEnergy (τ : Type*) where
  perLens : τ → ℝ

/-- Legacy 7-lens specialization retained for backwards compatibility. -/
abbrev AdelicFreeEnergy := GenericAdelicFreeEnergy LensID

/-- Backward-compatible legacy aggregate over the 7-lens decomposition. -/
def AdelicFreeEnergy.total (afe : AdelicFreeEnergy) : ℝ :=
  afe.perLens LensID.omega +
  afe.perLens LensID.region +
  afe.perLens LensID.graph +
  afe.perLens LensID.clifford +
  afe.perLens LensID.tensor +
  afe.perLens LensID.topology +
  afe.perLens LensID.matula

/-- Restricted product condition: only finitely many lenses exceed a threshold. -/
def freeEnergyRestricted {τ : Type*} (afe : GenericAdelicFreeEnergy τ) (threshold : ℝ) : Prop :=
  {lens : τ | afe.perLens lens > threshold}.Finite

/-- A tag-indexed family of agents with cross-tag coupling strengths. -/
structure GenericMultiScaleAgent (τ : Type*) (O S A : Type*) where
  agents : τ → Agent O S A
  coupling : τ → τ → ℝ

/-- Legacy 7-lens specialization retained for backwards compatibility. -/
abbrev MultiScaleAgent (O S A : Type*) := GenericMultiScaleAgent LensID O S A

/-- Positive-coupling alignment at a designated perspective. -/
theorem generic_multiscale_alignment {τ O S A : Type*}
    (msa : GenericMultiScaleAgent τ O S A)
    (strong_coupling : ∀ l1 l2, msa.coupling l1 l2 > 0)
    (focus : τ) :
    0 < msa.coupling focus focus :=
  strong_coupling focus focus

/-- Legacy-name theorem at the omega focus lens. -/
theorem multiscale_alignment {O S A : Type*} [Fintype S]
    (msa : MultiScaleAgent O S A)
    (strong_coupling : ∀ l1 l2, msa.coupling l1 l2 > 0) :
    0 < msa.coupling LensID.omega LensID.omega :=
  generic_multiscale_alignment msa strong_coupling LensID.omega

/-- Backward-compatibility projection from 100-lens free energies to legacy `LensID`. -/
def restrictCoreFreeEnergyToLensID
    (afe : GenericAdelicFreeEnergy CoreLensTag) : AdelicFreeEnergy where
  perLens l := afe.perLens (LensIDCoreBridge.toCoreLensTag l)

/-- Backward-compatibility projection from 100-lens agents to legacy `LensID`. -/
def restrictCoreAgentToLensID {O S A : Type*}
    (msa : GenericMultiScaleAgent CoreLensTag O S A) : MultiScaleAgent O S A where
  agents l := msa.agents (LensIDCoreBridge.toCoreLensTag l)
  coupling l1 l2 := msa.coupling (LensIDCoreBridge.toCoreLensTag l1) (LensIDCoreBridge.toCoreLensTag l2)

end ActiveInference
end HeytingLean
