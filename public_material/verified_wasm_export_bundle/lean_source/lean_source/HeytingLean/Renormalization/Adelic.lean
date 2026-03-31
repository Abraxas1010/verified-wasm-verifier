import HeytingLean.Renormalization.CoarseGrain
import HeytingLean.Embeddings.Adelic
import HeytingLean.Embeddings.CoreLenses
import HeytingLean.Embeddings.LensIDCoreBridge

/-!
# Renormalization.Adelic

Minimal scaffolding for lens-indexed (“adelic”) collections of RG flows.

This slice is intentionally small: it provides stable definitions and theorem names needed for
integration tests and later refinement.
-/

namespace HeytingLean
namespace Renormalization

open HeytingLean.Embeddings

/-- An RG transformation per perspective index. -/
structure GenericAdelicRG (τ : Type*) (α : Type*) where
  perLens : τ → RGTransform α

/-- Legacy 7-lens specialization retained for backwards compatibility. -/
abbrev AdelicRG (α : Type*) := GenericAdelicRG LensID α

/-- Apply each perspective's RG transformation independently. -/
def GenericAdelicRG.coordinatedFlow {τ α : Type*} (arg : GenericAdelicRG τ α)
    (initial : τ → Scale α) : τ → Scale α :=
  fun lens => (arg.perLens lens).coarsen (initial lens)

/-- A coupling structure expressing cross-lens consistency constraints. -/
structure GenericCoupledFlows {τ α : Type*} (arg : GenericAdelicRG τ α) where
  coupling : τ → τ → ℝ
  consistency : ∀ l1 l2, coupling l1 l2 = coupling l2 l1

/-- Legacy 7-lens specialization retained for backwards compatibility. -/
abbrev CoupledFlows {α : Type*} (arg : AdelicRG α) := GenericCoupledFlows arg

/-- Non-trivial alignment witness: strong coupling implies positivity on the diagonal. -/
theorem generic_coupled_rg_alignment {τ α : Type*} (arg : GenericAdelicRG τ α)
    (cf : GenericCoupledFlows arg) (strong : ∀ l1 l2, cf.coupling l1 l2 > 1) (lens : τ) :
    0 < cf.coupling lens lens := by
  have h : 1 < cf.coupling lens lens := strong lens lens
  exact lt_trans zero_lt_one h

/-- Legacy-name alignment theorem at a selected legacy lens. -/
theorem coupled_rg_alignment {α : Type*} (arg : AdelicRG α)
    (cf : CoupledFlows arg) (strong : ∀ l1 l2, cf.coupling l1 l2 > 1)
    (_initial : LensID → Scale α) (lens : LensID) :
    0 < cf.coupling lens lens :=
  generic_coupled_rg_alignment arg cf strong lens

/-- Backward-compatibility projection from 100-lens RG families to legacy `LensID`. -/
def restrictCoreRGToLensID {α : Type*} (arg : GenericAdelicRG CoreLensTag α) : AdelicRG α where
  perLens lens := arg.perLens (LensIDCoreBridge.toCoreLensTag lens)

end Renormalization
end HeytingLean
