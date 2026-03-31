import HeytingLean.Metrics.Magnitude.Homology

namespace HeytingLean
namespace Metrics
namespace Magnitude

universe u v

open Finset

/-- Finite metric-like structure for length-graded magnitude chains. -/
class MetricMagnitudeSpace (α : Type u) extends Fintype α where
  decEq : DecidableEq α
  dist : α → α → Nat
  dist_self : ∀ x, dist x x = 0
  dist_symm : ∀ x y, dist x y = dist y x

attribute [instance] MetricMagnitudeSpace.decEq

/-- Length grading of a magnitude chain: sum of consecutive edge lengths. -/
def chainLength {α : Type u} [M : MetricMagnitudeSpace α] {n : Nat}
    (τ : MagnitudeChain α n) : Nat :=
  ∑ i : Fin n, M.dist (τ.1 i.castSucc) (τ.1 i.succ)

/-- Chains of fixed degree and fixed metric length. -/
def gradedChainGroup {α : Type u} [MetricMagnitudeSpace α] (n ℓ : Nat) : Type u :=
  { τ : MagnitudeChain α n // chainLength τ = ℓ }

/-- Chain-level diagonal concentration: no chains occur off the `n = ℓ` diagonal.
This is stronger than homological diagonality (`MH_{n,ℓ} = 0` for `n ≠ ℓ`). -/
def IsChainDiagonal {α : Type u} [MetricMagnitudeSpace α] : Prop :=
  ∀ n ℓ, n ≠ ℓ → IsEmpty (gradedChainGroup (α := α) n ℓ)

/-- Backward-compatible alias used by earlier phases. -/
abbrev IsDiagonal {α : Type u} [MetricMagnitudeSpace α] : Prop :=
  IsChainDiagonal (α := α)

/-- Unit-edge condition: every distinct adjacent pair has unit distance. -/
def UnitEdgeMetric {α : Type u} [M : MetricMagnitudeSpace α] : Prop :=
  ∀ x y, x ≠ y → M.dist x y = 1

theorem chainLength_eq_degree_of_unitEdge {α : Type u} [MetricMagnitudeSpace α]
    (hunit : UnitEdgeMetric (α := α)) {n : Nat} (τ : MagnitudeChain α n) :
    chainLength τ = n := by
  have hterm :
      ∀ i : Fin n,
        MetricMagnitudeSpace.dist (τ.1 i.castSucc) (τ.1 i.succ) = 1 := by
    intro i
    exact hunit _ _ (τ.2 i)
  calc
    chainLength τ = ∑ i : Fin n, (1 : Nat) := by
      unfold chainLength
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact hterm i
    _ = n := by simp

theorem unitEdge_implies_chainDiagonal {α : Type u} [MetricMagnitudeSpace α]
    (hunit : UnitEdgeMetric (α := α)) : IsChainDiagonal (α := α) := by
  intro n ℓ hnℓ
  refine ⟨?_⟩
  intro x
  have hlen : chainLength x.1 = n := chainLength_eq_degree_of_unitEdge hunit x.1
  have hEq : ℓ = n := by simpa [x.2] using hlen
  exact hnℓ hEq.symm

/-- Backward-compatible unit-edge diagonal theorem surface. -/
theorem unitEdge_implies_diagonal {α : Type u} [MetricMagnitudeSpace α]
    (hunit : UnitEdgeMetric (α := α)) : IsDiagonal (α := α) := by
  exact unitEdge_implies_chainDiagonal hunit

theorem section_injective {α : Type u} {β : Type v}
    (r : α → β) (s : β → α) (hrs : ∀ y, r (s y) = y) :
    Function.Injective s := by
  intro x y hxy
  calc
    x = r (s x) := (hrs x).symm
    _ = r (s y) := by simp [hxy]
    _ = y := hrs y

/-- Map magnitude chains along an injective section. -/
def mapChain {α : Type u} {β : Type v} [MetricMagnitudeSpace α] [MetricMagnitudeSpace β]
    (s : β → α) (hsinj : Function.Injective s) {n : Nat}
    (τ : MagnitudeChain β n) : MagnitudeChain α n :=
  ⟨fun i => s (τ.1 i), by
    intro i h
    exact τ.2 i (hsinj h)⟩

theorem chainLength_mapChain {α : Type u} {β : Type v}
    [Mα : MetricMagnitudeSpace α] [Mβ : MetricMagnitudeSpace β]
    (s : β → α) (hdist : ∀ x y, Mα.dist (s x) (s y) = Mβ.dist x y)
    (hsinj : Function.Injective s) {n : Nat} (τ : MagnitudeChain β n) :
    chainLength (mapChain s hsinj τ) = chainLength τ := by
  unfold chainLength mapChain
  refine Finset.sum_congr rfl ?_
  intro i hi
  simpa using hdist (τ.1 i.castSucc) (τ.1 i.succ)

/-- Diagonality descends along a retract preserving chain lengths. -/
theorem diagonal_retract {α : Type u} {β : Type v}
    [Mα : MetricMagnitudeSpace α] [Mβ : MetricMagnitudeSpace β]
    (r : α → β) (s : β → α)
    (hrs : ∀ y, r (s y) = y)
    (hdist : ∀ x y, Mα.dist (s x) (s y) = Mβ.dist x y)
    (hdiag : IsChainDiagonal (α := α)) :
    IsChainDiagonal (α := β) := by
  intro n ℓ hnℓ
  refine ⟨?_⟩
  intro x
  let hsinj : Function.Injective s := section_injective r s hrs
  let xMap : MagnitudeChain α n := mapChain s hsinj x.1
  have hlen : chainLength xMap = ℓ := by
    calc
      chainLength xMap = chainLength x.1 := chainLength_mapChain s hdist hsinj x.1
      _ = ℓ := x.2
  have xDiag : gradedChainGroup (α := α) n ℓ := ⟨xMap, hlen⟩
  exact (hdiag n ℓ hnℓ).false xDiag

end Magnitude
end Metrics
end HeytingLean
