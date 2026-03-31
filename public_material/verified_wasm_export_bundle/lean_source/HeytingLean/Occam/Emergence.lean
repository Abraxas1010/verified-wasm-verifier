import HeytingLean.Bridges.Emergence
import HeytingLean.Meta.AIT.ModelComplexity
import HeytingLean.Logic.PSR.Robustness

/-
# Emergence Selector — Occam and PSR alignment

This module connects the Emergence Selector pre-lens to the existing
Occam/birth-index and PSR robustness infrastructure.

* `emergenceModelComplexity` packages a TPM + candidate partitions into
  a `ModelComplexity` profile over partitions, with
  `codeComplexity` given by a simple structural description length
  (number of blocks) and `birthComplexity` aligned with non-redundant
  ΔCP contributors.
* `PSR_RobustAtScale` gives a spec-level robustness notion for
  determinism/specificity at a chosen macroscale, parameterised by an
  abstract perturbation relation.
* `LogicDimension` and `chooseDimension` implement a simple
  dimension/dialectic "dial" driven by the Emergence regime and
  complexity measures.

All definitions are spec-level, with no proof holes and no fake or
dummy semantics; they provide precise shapes that concrete
lenses and policies can specialise further.
-/

namespace HeytingLean
namespace Occam
namespace Emergence

open HeytingLean.Bridges
open HeytingLean.Bridges.Emergence
open HeytingLean.Meta.AIT

/-- A `ModelComplexity` profile for emergence scales (partitions) at a
fixed TPM and candidate set.

* `codeComplexity` is a simple structural measure: the number of
  blocks in the partition (`levelOf`).
* `birthComplexity` aligns with the emergent hierarchy: partitions
  with nonzero ΔCP keep their structural level as birth complexity,
  while non-contributing partitions are penalised by a +1 offset.

This makes it easy to express Occam-style preferences: among scales
with comparable structural description, we favour those that actually
contribute positive ΔCP mass. -/
noncomputable def emergenceModelComplexity {n : Nat}
    (P : TPM n) (candidates : List (Partition n)) :
    ModelComplexity (Partition n) :=
  { codeComplexity := fun π => levelOf π
    birthComplexity := fun π =>
      let ℓ := levelOf π
      let δ := deltaCPOver P π candidates
      if δ > 0 then ℓ else ℓ + 1 }

namespace emergenceModelComplexity

open HeytingLean.Meta.AIT.ModelComplexity

/-- Emergence/Occam alignment lemma: if a partition `π₁` has strictly
positive ΔCP while another partition `π₂` has no positive ΔCP, and
`π₁` is at most as fine as `π₂` (no more blocks), then `π₁` is no
more complex than `π₂` with respect to the emergence-driven
`ModelComplexity`.

This captures the intended Occam preference: earlier or comparable
scales which still contribute non-redundant causal power (ΔCP > 0)
are favoured over non-contributing scales. -/
lemma prefersPositiveDelta {n : Nat}
    (P : TPM n) (candidates : List (Partition n))
    (π₁ π₂ : Partition n)
    (hδ₁ : deltaCPOver P π₁ candidates > 0)
    (hδ₂ : deltaCPOver P π₂ candidates ≤ 0)
    (hle : levelOf π₁ ≤ levelOf π₂) :
    (emergenceModelComplexity P candidates).dominates π₁ π₂ := by
  classical
  -- Unpack the dominance relation for this concrete profile.
  unfold emergenceModelComplexity ModelComplexity.dominates
  constructor
  · -- codeComplexity inequality is exactly `hle`.
    exact hle
  · -- birthComplexity inequality: use the explicit definitions.
    have hstep : levelOf π₂ ≤ levelOf π₂ + 1 := Nat.le_succ _
    have h' : levelOf π₁ ≤ levelOf π₂ + 1 := le_trans hle hstep
    -- Since `δ₂ ≤ 0`, we know that `0 < δ₂` is false.
    have hδ₂' : ¬ 0 < deltaCPOver P π₂ candidates :=
      not_lt_of_ge hδ₂
    -- Rewrite the goal into an explicit inequality between the piecewise
    -- birth complexity expressions and discharge it using `h'`.
    change
      (if 0 < deltaCPOver P π₁ candidates then levelOf π₁ else levelOf π₁ + 1) ≤
        (if 0 < deltaCPOver P π₂ candidates then levelOf π₂ else levelOf π₂ + 1)
    simpa [hδ₁, hδ₂'] using h'

end emergenceModelComplexity

/-- A spec-level notion of PSR robustness at a chosen macroscale.

Given:
* a perturbation relation `Perturb` on TPMs (encoding what counts as a
  “small” or “reasonable” change to the underlying dynamics),
* a microscale TPM `P`, and
* a partition `π`,

`PSR_RobustAtScale Perturb P π` states that both determinism and
specificity of the coarse-grained TPM are invariant across all
perturbations related to `P` by `Perturb`. This is an emergence-lens
instantiation of the PSR idea: reasons (here, macro determinism/
specificity) remain stable under admissible perturbations. -/
def PSR_RobustAtScale {n : Nat}
    (Perturb : TPM n → TPM n → Prop)
    (P : TPM n) (π : Partition n) : Prop :=
  ∀ Q : TPM n, Perturb P Q →
    determinism (P.coarseGrain π) = determinism (Q.coarseGrain π) ∧
    specificity (P.coarseGrain π) = specificity (Q.coarseGrain π)

/-- A trivial but well-typed perturbation relation: only the identity
transition matrix is considered a perturbation.  This is useful in
tests and examples where we want a concrete, non-vacuous instance of
`PSR_RobustAtScale` without committing to a particular metric on TPMs.
-/
def PerturbId {n : Nat} (P Q : TPM n) : Prop :=
  Q = P

/-- Under the identity perturbation relation, PSR robustness at scale
is immediate: determinism and specificity are clearly invariant when
`Q = P`. -/
lemma PSR_RobustAtScale_id {n : Nat} (P : TPM n) (π : Partition n) :
    PSR_RobustAtScale (PerturbId) P π := by
  intro Q hQ
  subst hQ
  simp [PSR_RobustAtScale]

/-- A coarse-grained logical dimension choice driven by the Emergence
regime and complexity measures.  This is intentionally simple:

* `BottomHeavy` → prefer a more constructive setting;
* `TopHeavy` → allow more classical behaviour;
* `Mesoscale` and `ScaleFreeLike` → stay in a balanced intermediate
  regime.

More refined policies can later take `S_path` and `S_row` into
account, but this already provides a deterministic, auditable
dimension dial for small examples. -/
inductive LogicDimension
  | Constructive
  | Balanced
  | Classical
deriving Repr, DecidableEq

/-- Choose a logical dimension regime based on the Emergence profile
of an `EmergentChoice`. -/
def chooseDimension {n : Nat} (ec : Bridges.Emergence.EmergentChoice n) :
    LogicDimension :=
  match ec.regime with
  | EmergenceRegime.BottomHeavy   => LogicDimension.Constructive
  | EmergenceRegime.TopHeavy      => LogicDimension.Classical
  | EmergenceRegime.Mesoscale
  | EmergenceRegime.ScaleFreeLike => LogicDimension.Balanced

end Emergence
end Occam
end HeytingLean
