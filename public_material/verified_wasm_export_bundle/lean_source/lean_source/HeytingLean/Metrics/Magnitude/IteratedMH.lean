import HeytingLean.Metrics.Magnitude.HomologyGroups
import HeytingLean.Algebra.SpectralSequence.Paged
import HeytingLean.Algebra.SpectralSequence.RatchetConvergence
import HeytingLean.Algebra.BarConstruction.Basic

namespace HeytingLean
namespace Metrics
namespace Magnitude

universe u

/-- `k`-layered vertices for iterated magnitude nerve simplices. -/
abbrev NerveVertex (α : Type u) (k : Nat) : Type u := Fin k → α

/-- Iterated magnitude nerve `N^k_n`: `(n+1)`-tuples of `k`-layered vertices. -/
abbrev MagnitudeNerve (α : Type u) (k : Nat) (n : Nat) : Type u :=
  Fin (n + 1) → NerveVertex α k

/-- Face map on the iterated nerve by deleting one simplicial index. -/
def nerveFace {α : Type u} {k n : Nat} (i : Fin (n + 2)) :
    MagnitudeNerve α k (n + 1) → MagnitudeNerve α k n :=
  deleteTupleAt i

/-- Simplicial composition law for iterated nerve face maps. -/
theorem nerveFace_comp {α : Type u} {k n : Nat}
    (j : Fin (n + 3)) (i : Fin (n + 2))
    (t : MagnitudeNerve α k (n + 2)) :
    nerveFace i (nerveFace j t) =
      nerveFace (i.predAbove j) (nerveFace (j.succAbove i) t) := by
  simpa [nerveFace] using
    (deleteTupleAt_deleteTupleAt (α := NerveVertex α k) j i t)

/-- Moore complex of the iterated magnitude nerve, using alternating unnormalized faces. -/
def mooreComplex (α : Type u) [Fintype α] [DecidableEq α]
    (k : Nat) : Algebra.SpectralSequence.DifferentialComplex where
  E := fun n => MagnitudeNerve α k n → ℤ
  zero := fun _ _ => 0
  d := fun n f => unnormDiff (α := NerveVertex α k) n f
  d_zero := by
    intro n
    funext τ
    simp [unnormDiff]
  d_squared := by
    intro n f
    funext τ
    simpa using (unnormDiff_squared (α := NerveVertex α k) n f τ)

/-- Cycles in degree `n` for the iterated Moore complex. -/
def iteratedMHCycles (α : Type u) [Fintype α] [DecidableEq α]
    (k n : Nat) : Set (MagnitudeNerve α k (n + 1) → ℤ) :=
  { f | ∀ τ, (mooreComplex α k).d n f τ = 0 }

/-- Boundaries in degree `n` for the iterated Moore complex. -/
def iteratedMHBoundaries (α : Type u) [Fintype α] [DecidableEq α]
    (k n : Nat) : Set (MagnitudeNerve α k (n + 1) → ℤ) :=
  { f | ∃ g : MagnitudeNerve α k (n + 2) → ℤ, (mooreComplex α k).d (n + 1) g = f }

/-- Every iterated boundary is an iterated cycle (`d ∘ d = 0`). -/
theorem iteratedBoundary_subset_cycle (α : Type u) [Fintype α] [DecidableEq α]
    (k n : Nat) :
    iteratedMHBoundaries α k n ⊆ iteratedMHCycles α k n := by
  intro f hf τ
  rcases hf with ⟨g, rfl⟩
  exact congrArg (fun h => h τ) ((mooreComplex α k).d_squared n g)

/-- Degree-`n` iterated cycles as a subtype. -/
abbrev IteratedCycle (α : Type u) [Fintype α] [DecidableEq α]
    (k n : Nat) : Type _ :=
  { f : MagnitudeNerve α k (n + 1) → ℤ // f ∈ iteratedMHCycles α k n }

/-- Homology-class relation in degree `n` for iterated magnitude cycles. -/
def iteratedMHRel (α : Type u) [Fintype α] [DecidableEq α]
    (k n : Nat)
    (f g : IteratedCycle α k n) : Prop :=
  ∃ b, b ∈ iteratedMHBoundaries α k n ∧ f.1 = fun τ => g.1 τ + b τ

/-- Quotient presentation of iterated magnitude homology classes `Z/B`. -/
def iteratedMH (α : Type u) [Fintype α] [DecidableEq α]
    (k n : Nat) : Type _ :=
  Quot (iteratedMHRel α k n)

/-- At level `k = 1`, layered vertices are equivalent to ordinary vertices. -/
def nerveVertexOneEquiv (α : Type u) : NerveVertex α 1 ≃ α where
  toFun := fun f => f 0
  invFun := fun a => fun _ => a
  left_inv := by
    intro f
    funext i
    have hi : i = 0 := Fin.eq_zero i
    simp [hi]
  right_inv := by
    intro a
    rfl

/-- At `k = 1`, iterated nerve simplices identify with ordinary bar simplices. -/
def magnitudeNerveOneEquivBarSimplex (α : Type u) (n : Nat) :
    MagnitudeNerve α 1 n ≃ Algebra.BarConstruction.BarSimplex α (n + 1) where
  toFun := fun t i => (t i) 0
  invFun := fun s i _ => s i
  left_inv := by
    intro t
    funext i
    apply funext
    intro j
    have hj : j = 0 := Fin.eq_zero j
    simp [hj]
  right_inv := by
    intro s
    funext i
    rfl

/-- Level-1 iterated nerve agrees with ordinary degreewise simplex model. -/
def iteratedMH_one_eq_MH (α : Type u) [Fintype α] [DecidableEq α] (n : Nat) :
    MagnitudeNerve α 1 n ≃ Algebra.BarConstruction.BarSimplex α (n + 1) :=
  magnitudeNerveOneEquivBarSimplex α n

/-- Degreewise cardinality of iterated nerve simplices. -/
theorem magnitudeNerve_card (α : Type u) [Fintype α] [DecidableEq α]
    (k n : Nat) :
    Fintype.card (MagnitudeNerve α k n) =
      (Fintype.card α) ^ (k * (n + 1)) := by
  classical
  simp [MagnitudeNerve, NerveVertex, pow_mul]

/-- Spectral-sequence input complex for iterated magnitude homology. -/
def iteratedMH_spectralSequence (α : Type u) [Fintype α] [DecidableEq α]
    (k : Nat) : Algebra.SpectralSequence.DifferentialComplex :=
  mooreComplex α k

/-- Stabilization-based page convergence for the iterated-magnitude spectral model. -/
theorem iteratedMH_paged_converges (α : Type u) [Fintype α] [DecidableEq α]
    (k N : Nat) :
    Algebra.SpectralSequence.PageConverges
      (Algebra.SpectralSequence.pagedOfRatchetAndComplex
        (iteratedMH_spectralSequence α k)
        (fun n => Nat.min n N)
        (by
          intro a b hab
          exact min_le_min hab (le_rfl)))
      N := by
  simpa [Nat.min_self] using
    (Algebra.SpectralSequence.pagedConverges_of_stabilizes
      (C := iteratedMH_spectralSequence α k)
      (level := fun n => Nat.min n N)
      (htraj := by
        intro a b hab
        exact min_le_min hab (le_rfl))
      (N := N)
      (hstab := by
        intro n hn
        simpa [Nat.min_self] using (Nat.min_eq_right hn)))

end Magnitude
end Metrics
end HeytingLean
