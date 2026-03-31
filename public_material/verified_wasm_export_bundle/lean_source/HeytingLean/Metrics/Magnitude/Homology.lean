import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fin.Parity
import Mathlib.Algebra.BigOperators.Ring.Finset
import HeytingLean.Metrics.Magnitude.Basic
import HeytingLean.Algebra.BarConstruction.Basic
import HeytingLean.Algebra.SpectralSequence.Basic

namespace HeytingLean
namespace Metrics
namespace Magnitude

universe u

/-- Consecutive-distinctness condition for tuple chains. -/
def ConsecutiveDistinct {α : Type u} (t : Fin (n + 1) → α) : Prop :=
  ∀ i : Fin n, t i.castSucc ≠ t i.succ

/-- Degree-`n` magnitude chains: `(n+1)`-tuples with consecutive distinctness. -/
def MagnitudeChain (α : Type u) [DecidableEq α] (n : Nat) : Type u :=
  { t : Fin (n + 1) → α // ConsecutiveDistinct t }

instance instDecidableConsecutiveDistinct {α : Type u} [DecidableEq α]
    (n : Nat) (t : Fin (n + 1) → α) : Decidable (ConsecutiveDistinct t) := by
  classical
  unfold ConsecutiveDistinct
  infer_instance

instance instFintypeMagnitudeChain {α : Type u} [Fintype α] [DecidableEq α] (n : Nat) :
    Fintype (MagnitudeChain α n) := by
  classical
  unfold MagnitudeChain
  infer_instance

/-- Forgetful embedding from magnitude chains to bar simplices. -/
def toBarSimplex {α : Type u} [DecidableEq α] (n : Nat) :
    MagnitudeChain α n ↪ Algebra.BarConstruction.BarSimplex α (n + 1) where
  toFun := fun x => x.1
  inj' := by
    intro x y h
    cases x
    cases y
    cases h
    rfl

/-- Cardinal rank of the degree-`n` magnitude chain group (set-level model). -/
def chainRank (α : Type u) [Fintype α] [DecidableEq α] (n : Nat) : Nat :=
  Fintype.card (MagnitudeChain α n)

/-- Euler characteristic cut-off for the first `N+1` chain degrees. -/
def eulerCut (α : Type u) [Fintype α] [DecidableEq α] (N : Nat) : Int :=
  Finset.sum (Finset.range (N + 1)) (fun n => ((-1 : Int) ^ n) * Int.ofNat (chainRank α n))

/-- Magnitude chains embed into bar simplices degreewise. -/
theorem chainRank_le_barRank (α : Type u) [Fintype α] [DecidableEq α] (n : Nat) :
    chainRank α n ≤ Fintype.card (Algebra.BarConstruction.BarSimplex α (n + 1)) := by
  simpa [chainRank] using
    (Fintype.card_le_of_injective (toBarSimplex (α := α) n) (toBarSimplex (α := α) n).injective)

/-- Degreewise rank bound induced by the bar-simplex cardinality formula. -/
theorem chainRank_le_card_pow (α : Type u) [Fintype α] [DecidableEq α] (n : Nat) :
    chainRank α n ≤ finiteMagnitude α ^ (n + 1) := by
  calc
    chainRank α n ≤ Fintype.card (Algebra.BarConstruction.BarSimplex α (n + 1)) :=
      chainRank_le_barRank (α := α) n
    _ = finiteMagnitude α ^ (n + 1) := by
      rw [finiteMagnitude]
      exact Algebra.BarConstruction.barSimplex_card (M := α) (n := n + 1)

/-- Degree-0 magnitude chains are equivalent to the underlying finite type. -/
def magnitudeChainZeroEquiv (α : Type u) [DecidableEq α] : MagnitudeChain α 0 ≃ α where
  toFun := fun x => x.1 0
  invFun := fun a => ⟨fun _ => a, by
    intro i
    exact Fin.elim0 i⟩
  left_inv := by
    intro x
    apply Subtype.ext
    funext i
    have hi : i = 0 := Fin.eq_zero i
    simp [hi]
  right_inv := by
    intro a
    rfl

/-- The degree-0 chain rank recovers finite magnitude exactly. -/
theorem chainRank_zero_eq_finiteMagnitude (α : Type u) [Fintype α] [DecidableEq α] :
    chainRank α 0 = finiteMagnitude α := by
  simpa [chainRank, finiteMagnitude] using
    (Fintype.card_congr (magnitudeChainZeroEquiv α))

/-- The first Euler cut (`N = 0`) is exactly finite magnitude. -/
theorem eulerCut_zero_eq_finiteMagnitude (α : Type u) [Fintype α] [DecidableEq α] :
    eulerCut α 0 = Int.ofNat (finiteMagnitude α) := by
  simp [eulerCut, chainRank_zero_eq_finiteMagnitude]

/-- Delete the `i`-th vertex from an `(n+2)`-tuple, producing an `(n+1)`-tuple. -/
def deleteTupleAt {α : Type u} {n : Nat} (i : Fin (n + 2))
    (t : Fin (n + 2) → α) : Fin (n + 1) → α :=
  t ∘ i.succAbove

/-- Whether deleting vertex `i` preserves consecutive distinctness. -/
def isNondegenerateFace {α : Type u} [DecidableEq α] {n : Nat}
    (t : Fin (n + 2) → α) (_ht : ConsecutiveDistinct t) (i : Fin (n + 2)) : Prop :=
  ConsecutiveDistinct (deleteTupleAt i t)

/-- Deleting the first vertex preserves consecutive distinctness. -/
theorem boundary_face_zero_nondegenerate {α : Type u} [DecidableEq α] {n : Nat}
    (t : Fin (n + 2) → α) (ht : ConsecutiveDistinct t) :
    isNondegenerateFace t ht 0 := by
  intro j
  simpa [isNondegenerateFace, deleteTupleAt] using ht j.succ

/-- Deleting the last vertex preserves consecutive distinctness. -/
theorem boundary_face_last_nondegenerate {α : Type u} [DecidableEq α] {n : Nat}
    (t : Fin (n + 2) → α) (ht : ConsecutiveDistinct t) :
    isNondegenerateFace t ht (Fin.last (n + 1)) := by
  intro j
  simpa [isNondegenerateFace, deleteTupleAt] using ht j.castSucc

/-- Signed face contribution for a generator at index `i`. -/
def signedFaceCoeff {α : Type u} [Fintype α] [DecidableEq α] {n : Nat}
    (σ : MagnitudeChain α (n + 1)) (i : Fin (n + 2)) (τ : MagnitudeChain α n) : ℤ :=
  if h : ConsecutiveDistinct (deleteTupleAt i σ.1) then
    if (⟨deleteTupleAt i σ.1, h⟩ : MagnitudeChain α n) = τ then (-1 : ℤ) ^ i.val else 0
  else 0

/-- Alternating face differential on the chain-module model. -/
def magnitudeDifferential {α : Type u} [Fintype α] [DecidableEq α] (n : Nat)
    (f : MagnitudeChain α (n + 1) → ℤ) : MagnitudeChain α n → ℤ :=
  fun τ => Finset.sum Finset.univ fun σ =>
    f σ * Finset.sum Finset.univ fun i => signedFaceCoeff σ i τ

/-- The `deleteTupleAt` operation coincides with `Fin.removeNth`. -/
theorem deleteTupleAt_eq_removeNth {α : Type u} {n : Nat} (i : Fin (n + 2))
    (t : Fin (n + 2) → α) :
    deleteTupleAt i t = i.removeNth t := by
  rfl

/-- Double deletion identity: the simplicial relation for `deleteTupleAt`. -/
theorem deleteTupleAt_deleteTupleAt {α : Type u} {n : Nat}
    (j : Fin (n + 3)) (i : Fin (n + 2)) (t : Fin (n + 3) → α) :
    deleteTupleAt i (deleteTupleAt j t) =
      deleteTupleAt (i.predAbove j) (deleteTupleAt (j.succAbove i) t) := by
  simp only [deleteTupleAt_eq_removeNth]
  exact Fin.removeNth_removeNth_eq_swap t i j

/-! ### d²=0 for the alternating face map complex

The key identity: `succAbove j i` and `predAbove i j` satisfy
`(succAbove j i).val + (predAbove i j).val = j.val + i.val ± 1`, so the
signs `(-1)^(j+i)` and `(-1)^(succAbove + predAbove)` are always opposite.
Combined with the double-deletion identity, every term in `∂²` pairs with
a partner of opposite sign.

We factor the proof into small, independently verifiable lemmas.
-/

/-- The sign parity key: `j.val + i.val` and `(succAbove j i).val + (predAbove i j).val`
    have opposite parity. -/
theorem succAbove_predAbove_sign_neg {n : Nat} (j : Fin (n + 3)) (i : Fin (n + 2)) :
    ((-1 : ℤ) ^ ((Fin.succAbove j i).val + (Fin.predAbove i j).val)) =
      -((-1 : ℤ) ^ (j.val + i.val)) := by
  simpa using (Fin.neg_one_pow_succAbove_add_predAbove (R := ℤ) j i)

/-- The involution `(j, i) ↦ (succAbove j i, predAbove i j)` is fixed-point free. -/
theorem succAbove_predAbove_ne {n : Nat} (j : Fin (n + 3)) (i : Fin (n + 2)) :
    (Fin.succAbove j i, Fin.predAbove i j) ≠ (j, i) := by
  intro h
  exact Fin.succAbove_ne j i ((Prod.mk.inj h).1)

/-- The involution `(j, i) ↦ (succAbove j i, predAbove i j)` is an involution:
    applying it twice returns to `(j, i)`. -/
theorem succAbove_predAbove_involutive {n : Nat} (j : Fin (n + 3)) (i : Fin (n + 2)) :
    let p := (Fin.succAbove j i, Fin.predAbove i j)
    (Fin.succAbove p.1 p.2, Fin.predAbove p.2 p.1) = (j, i) := by
  ext <;> simp [Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]

/-! ### Unnormalized differential and d²=0

The normalized complex (ConsecutiveDistinct-filtered) prevents a direct involution
argument because the involution `(j,i) ↦ (succAbove j i, predAbove i j)` does not
preserve the ConsecutiveDistinct filter on intermediate faces.

Instead we:
1. Define the unnormalized differential on all tuples.
2. Prove d²=0 on the unnormalized complex via `Finset.sum_ninvolution`.
3. Show that the normalized differential equals the unnormalized one restricted
   to ConsecutiveDistinct generators.
4. Transport d²=0 from unnormalized to normalized.
-/

/-- Unnormalized signed face coefficient: `(-1)^i` if deleting vertex `i` from `σ`
    yields `τ`, and `0` otherwise. No ConsecutiveDistinct filter. -/
def unnormSignedFaceCoeff {α : Type u} [DecidableEq α] {n : Nat}
    (σ : Fin (n + 2) → α) (i : Fin (n + 2)) (τ : Fin (n + 1) → α) : ℤ :=
  if deleteTupleAt i σ = τ then (-1 : ℤ) ^ i.val else 0

/-- Unnormalized differential on all tuples (not restricted to ConsecutiveDistinct). -/
def unnormDiff {α : Type u} [Fintype α] [DecidableEq α] (n : Nat)
    (f : (Fin (n + 2) → α) → ℤ) : (Fin (n + 1) → α) → ℤ :=
  fun τ => Finset.sum Finset.univ fun σ =>
    f σ * Finset.sum Finset.univ fun i => unnormSignedFaceCoeff σ i τ

/-- Double application coefficient for the unnormalized differential.
    For a pair `(j, i)` and source tuple `ρ`, this is
    `(-1)^(j+i)` if `d_i(d_j(ρ)) = τ`, and `0` otherwise. -/
def unnormDoubleCoeff {α : Type u} [DecidableEq α] {n : Nat}
    (ρ : Fin (n + 3) → α) (j : Fin (n + 3)) (i : Fin (n + 2))
    (τ : Fin (n + 1) → α) : ℤ :=
  if deleteTupleAt i (deleteTupleAt j ρ) = τ then
    ((-1 : ℤ) ^ (j.val + i.val))
  else 0

/-- The involution negates unnormalized double coefficients. -/
theorem unnormDoubleCoeff_involution_neg {α : Type u} [DecidableEq α] {n : Nat}
    (ρ : Fin (n + 3) → α) (j : Fin (n + 3)) (i : Fin (n + 2))
    (τ : Fin (n + 1) → α) :
    unnormDoubleCoeff ρ (Fin.succAbove j i) (Fin.predAbove i j) τ =
      -(unnormDoubleCoeff ρ j i τ) := by
  simp only [unnormDoubleCoeff]
  have hdel := deleteTupleAt_deleteTupleAt j i ρ
  -- The double deletion identity: d_i(d_j(ρ)) = d_{predAbove}(d_{succAbove}(ρ))
  by_cases h : deleteTupleAt i (deleteTupleAt j ρ) = τ
  · -- Both sides have the same tuple, just different signs
    have h' : deleteTupleAt (Fin.predAbove i j) (deleteTupleAt (Fin.succAbove j i) ρ) = τ := by
      rwa [← hdel]
    simp [h, h', succAbove_predAbove_sign_neg]
  · -- Neither side matches τ
    have h' : deleteTupleAt (Fin.predAbove i j) (deleteTupleAt (Fin.succAbove j i) ρ) ≠ τ := by
      rwa [← hdel]
    simp [h, h']

/-- Composition of unnormalized face coefficients collapses to `unnormDoubleCoeff`. -/
theorem unnormSignedFaceCoeff_comp {α : Type u} [Fintype α] [DecidableEq α] {n : Nat}
    (ρ : Fin (n + 3) → α) (j : Fin (n + 3)) (i : Fin (n + 2))
    (τ : Fin (n + 1) → α) :
    Finset.sum Finset.univ (fun σ : Fin (n + 2) → α =>
      unnormSignedFaceCoeff ρ j σ * unnormSignedFaceCoeff σ i τ) =
      unnormDoubleCoeff ρ j i τ := by
  classical
  unfold unnormSignedFaceCoeff unnormDoubleCoeff
  refine (Finset.sum_eq_single (deleteTupleAt j ρ) ?_ ?_).trans ?_
  · intro σ hσ hneq
    have hne' : deleteTupleAt j ρ ≠ σ := by
      intro hEq
      exact hneq hEq.symm
    simp [hne']
  · intro hNotMem
    exfalso
    exact hNotMem (Finset.mem_univ _)
  · by_cases hτ : deleteTupleAt i (deleteTupleAt j ρ) = τ
    · simp [hτ, pow_add]
    · simp [hτ]

/-- The inner sum over face-index pairs vanishes by the simplicial involution. -/
theorem unnormDoubleCoeff_sum_eq_zero {α : Type u} [DecidableEq α] {n : Nat}
    (ρ : Fin (n + 3) → α) (τ : Fin (n + 1) → α) :
    Finset.sum Finset.univ
      (fun ji : Fin (n + 3) × Fin (n + 2) => unnormDoubleCoeff ρ ji.1 ji.2 τ) = 0 := by
  apply Finset.sum_ninvolution
    (fun ji => (Fin.succAbove ji.1 ji.2, Fin.predAbove ji.2 ji.1))
  · -- Pairs sum to zero
    intro ⟨j, i⟩
    rw [unnormDoubleCoeff_involution_neg]
    simp
  · -- Fixed-point free on support
    intro ⟨j, i⟩ h
    exact succAbove_predAbove_ne j i
  · -- Maps into Finset.univ
    intro ji
    simp
  · -- Involutive
    intro ⟨j, i⟩
    simpa using succAbove_predAbove_involutive j i

/-- The unnormalized differential squares to zero. -/
theorem unnormDiff_squared {α : Type u} [Fintype α] [DecidableEq α] (n : Nat)
    (f : (Fin (n + 3) → α) → ℤ) (τ : Fin (n + 1) → α) :
    unnormDiff n (unnormDiff (n + 1) f) τ = 0 := by
  classical
  simp_rw [unnormDiff, Finset.mul_sum, Finset.sum_mul]
  have hreorder :
      Finset.sum Finset.univ (fun x =>
        Finset.sum Finset.univ (fun x_1 =>
          Finset.sum Finset.univ (fun x_2 =>
            Finset.sum Finset.univ (fun i =>
              f x_2 * unnormSignedFaceCoeff x_2 i x * unnormSignedFaceCoeff x x_1 τ)))) =
      Finset.sum Finset.univ (fun x_2 =>
        Finset.sum Finset.univ (fun x_1 =>
          Finset.sum Finset.univ (fun i =>
            Finset.sum Finset.univ (fun x =>
              f x_2 * unnormSignedFaceCoeff x_2 i x * unnormSignedFaceCoeff x x_1 τ)))) := by
    calc
      Finset.sum Finset.univ (fun x =>
          Finset.sum Finset.univ (fun x_1 =>
            Finset.sum Finset.univ (fun x_2 =>
              Finset.sum Finset.univ (fun i =>
                f x_2 * unnormSignedFaceCoeff x_2 i x * unnormSignedFaceCoeff x x_1 τ))))
        = Finset.sum Finset.univ (fun x =>
            Finset.sum Finset.univ (fun x_2 =>
              Finset.sum Finset.univ (fun x_1 =>
                Finset.sum Finset.univ (fun i =>
                  f x_2 * unnormSignedFaceCoeff x_2 i x * unnormSignedFaceCoeff x x_1 τ)))) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [Finset.sum_comm]
      _ = Finset.sum Finset.univ (fun x_2 =>
            Finset.sum Finset.univ (fun x =>
              Finset.sum Finset.univ (fun x_1 =>
                Finset.sum Finset.univ (fun i =>
                  f x_2 * unnormSignedFaceCoeff x_2 i x * unnormSignedFaceCoeff x x_1 τ)))) := by
          rw [Finset.sum_comm]
      _ = Finset.sum Finset.univ (fun x_2 =>
            Finset.sum Finset.univ (fun x_1 =>
              Finset.sum Finset.univ (fun x =>
                Finset.sum Finset.univ (fun i =>
                  f x_2 * unnormSignedFaceCoeff x_2 i x * unnormSignedFaceCoeff x x_1 τ)))) := by
          refine Finset.sum_congr rfl ?_
          intro x_2 hx_2
          rw [Finset.sum_comm]
      _ = Finset.sum Finset.univ (fun x_2 =>
            Finset.sum Finset.univ (fun x_1 =>
              Finset.sum Finset.univ (fun i =>
                Finset.sum Finset.univ (fun x =>
                  f x_2 * unnormSignedFaceCoeff x_2 i x * unnormSignedFaceCoeff x x_1 τ)))) := by
          refine Finset.sum_congr rfl ?_
          intro x_2 hx_2
          refine Finset.sum_congr rfl ?_
          intro x_1 hx_1
          rw [Finset.sum_comm]
  rw [hreorder]
  refine Finset.sum_eq_zero ?_
  intro ρ hρ
  have hcollapse :
      Finset.sum Finset.univ (fun x_1 =>
        Finset.sum Finset.univ (fun i =>
          Finset.sum Finset.univ (fun x =>
            f ρ * unnormSignedFaceCoeff ρ i x * unnormSignedFaceCoeff x x_1 τ))) =
      f ρ * Finset.sum Finset.univ (fun x_1 =>
        Finset.sum Finset.univ (fun i => unnormDoubleCoeff ρ i x_1 τ)) := by
    calc
      Finset.sum Finset.univ (fun x_1 =>
          Finset.sum Finset.univ (fun i =>
            Finset.sum Finset.univ (fun x =>
              f ρ * unnormSignedFaceCoeff ρ i x * unnormSignedFaceCoeff x x_1 τ)))
          = Finset.sum Finset.univ (fun x_1 =>
              Finset.sum Finset.univ (fun i =>
                f ρ * Finset.sum Finset.univ (fun x =>
                  unnormSignedFaceCoeff ρ i x * unnormSignedFaceCoeff x x_1 τ))) := by
                refine Finset.sum_congr rfl ?_
                intro x_1 hx_1
                refine Finset.sum_congr rfl ?_
                intro i hi
                simp [Finset.mul_sum, mul_left_comm, mul_comm]
      _ = Finset.sum Finset.univ (fun x_1 =>
            Finset.sum Finset.univ (fun i =>
              f ρ * unnormDoubleCoeff ρ i x_1 τ)) := by
            refine Finset.sum_congr rfl ?_
            intro x_1 hx_1
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [unnormSignedFaceCoeff_comp]
      _ = f ρ * Finset.sum Finset.univ (fun x_1 =>
            Finset.sum Finset.univ (fun i => unnormDoubleCoeff ρ i x_1 τ)) := by
            simp [Finset.mul_sum]
  rw [hcollapse]
  have hpair :
      Finset.sum Finset.univ (fun x_1 =>
        Finset.sum Finset.univ (fun i => unnormDoubleCoeff ρ i x_1 τ)) = 0 := by
    have hpair' :
        Finset.sum Finset.univ (fun i =>
          Finset.sum Finset.univ (fun x_1 => unnormDoubleCoeff ρ i x_1 τ)) = 0 := by
      have hprodEq :
          Finset.sum (Finset.univ ×ˢ Finset.univ)
            (fun ji : Fin (n + 3) × Fin (n + 2) => unnormDoubleCoeff ρ ji.1 ji.2 τ) =
          Finset.sum Finset.univ (fun i =>
            Finset.sum Finset.univ (fun x_1 => unnormDoubleCoeff ρ i x_1 τ)) := by
        simpa using
          (Finset.sum_product'
            (s := (Finset.univ : Finset (Fin (n + 3))))
            (t := (Finset.univ : Finset (Fin (n + 2))))
            (f := fun i x_1 => unnormDoubleCoeff ρ i x_1 τ))
      calc
        Finset.sum Finset.univ (fun i =>
          Finset.sum Finset.univ (fun x_1 => unnormDoubleCoeff ρ i x_1 τ))
            = Finset.sum (Finset.univ ×ˢ Finset.univ)
                (fun ji : Fin (n + 3) × Fin (n + 2) => unnormDoubleCoeff ρ ji.1 ji.2 τ) := by
                  exact hprodEq.symm
        _ = 0 := by
              simpa [Finset.univ_product_univ] using unnormDoubleCoeff_sum_eq_zero (ρ := ρ) (τ := τ)
    rw [Finset.sum_comm]
    exact hpair'
  simp [hpair]

/-- The normalized differential factors through the unnormalized one.
    Specifically, for any function `f` on ConsecutiveDistinct chains,
    the normalized differential `magnitudeDifferential n f τ` equals
    the unnormalized differential applied to the zero-extension of `f`. -/
theorem magnitudeDifferential_eq_unnorm {α : Type u} [Fintype α] [DecidableEq α] (n : Nat)
    (f : MagnitudeChain α (n + 1) → ℤ) (τ : MagnitudeChain α n) :
    magnitudeDifferential n f τ =
      unnormDiff n
        (fun σ => if h : ConsecutiveDistinct σ then f ⟨σ, h⟩ else 0) τ.1 := by
  classical
  unfold magnitudeDifferential unnormDiff signedFaceCoeff unnormSignedFaceCoeff
  let B : (Fin (n + 2) → α) → ℤ := fun x =>
    if h : ConsecutiveDistinct x then
      f ⟨x, h⟩ * Finset.sum Finset.univ (fun i => if deleteTupleAt i x = τ.1 then (-1 : ℤ) ^ i.val else 0)
    else 0
  have hsplit := Fintype.sum_subtype_add_sum_subtype (p := ConsecutiveDistinct) (f := B)
  have hbad :
      (∑ x : {x : Fin (n + 2) → α // ¬ConsecutiveDistinct x}, B x) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x hx
    have hxNot : ¬ConsecutiveDistinct (x : Fin (n + 2) → α) := x.2
    simp [B, hxNot]
  have hgood :
      (∑ x : {x : Fin (n + 2) → α // ConsecutiveDistinct x}, B x) =
      ∑ σ : MagnitudeChain α (n + 1),
        f σ *
          ∑ i,
            (if h : ConsecutiveDistinct (deleteTupleAt i σ.1) then
              if (⟨deleteTupleAt i σ.1, h⟩ : MagnitudeChain α n) = τ then (-1 : ℤ) ^ i.val else 0
            else 0) := by
    refine Finset.sum_congr rfl ?_
    intro σ hσ
    have hσcd : ConsecutiveDistinct (σ : Fin (n + 2) → α) := σ.2
    have hsum :
        (∑ i, if deleteTupleAt i σ.1 = τ.1 then (-1 : ℤ) ^ i.val else 0) =
        ∑ i,
          (if h : ConsecutiveDistinct (deleteTupleAt i σ.1) then
            if (⟨deleteTupleAt i σ.1, h⟩ : MagnitudeChain α n) = τ then (-1 : ℤ) ^ i.val else 0
          else 0) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        by_cases hface : ConsecutiveDistinct (deleteTupleAt i σ.1)
        · have hEq :
            ((⟨deleteTupleAt i σ.1, hface⟩ : MagnitudeChain α n) = τ) ↔
              (deleteTupleAt i σ.1 = τ.1) := by
              constructor
              · intro h
                exact congrArg Subtype.val h
              · intro h
                cases τ with
                | mk τval hτ =>
                    apply Subtype.ext
                    simpa using h
          simp [hface, hEq]
        · have hneq : deleteTupleAt i σ.1 ≠ τ.1 := by
            intro hdel
            apply hface
            simpa [hdel] using τ.2
          simp [hface, hneq]
    simp [B, hσcd, hsum]
  have hR :
      (∑ x : Fin (n + 2) → α, B x) =
      ∑ x, if h : ConsecutiveDistinct x then
        f ⟨x, h⟩ * ∑ i, if deleteTupleAt i x = τ.1 then (-1 : ℤ) ^ i.val else 0
      else 0 := by
    simp [B]
  calc
    ∑ σ : MagnitudeChain α (n + 1),
        f σ *
          ∑ i,
            (if h : ConsecutiveDistinct (deleteTupleAt i σ.1) then
              if (⟨deleteTupleAt i σ.1, h⟩ : MagnitudeChain α n) = τ then (-1 : ℤ) ^ i.val else 0
            else 0)
        = ∑ x : {x : Fin (n + 2) → α // ConsecutiveDistinct x}, B x := by
            symm
            exact hgood
    _ = ∑ x : Fin (n + 2) → α, B x := by
            have := hsplit
            simpa [hbad] using this
    _ = ∑ x, if h : ConsecutiveDistinct x then
          f ⟨x, h⟩ * ∑ i, if deleteTupleAt i x = τ.1 then (-1 : ℤ) ^ i.val else 0
        else 0 := hR
    _ = ∑ σ,
          (fun σ => if h : ConsecutiveDistinct σ then f ⟨σ, h⟩ else 0) σ *
            ∑ i, if deleteTupleAt i σ = τ.1 then (-1 : ℤ) ^ i.val else 0 := by
            simp [zero_mul]

/-- Auxiliary: `signedFaceCoeff` on MagnitudeChain subtypes reduces to raw tuple
    face matching, because the ConsecutiveDistinct check on the face is redundant
    when the target τ is already ConsecutiveDistinct. -/
theorem signedFaceCoeff_eq_unnorm {α : Type u} [Fintype α] [DecidableEq α] {n : Nat}
    (σ : MagnitudeChain α (n + 1)) (i : Fin (n + 2)) (τ : MagnitudeChain α n) :
    signedFaceCoeff σ i τ =
      if deleteTupleAt i σ.1 = τ.1 then (-1 : ℤ) ^ i.val else 0 := by
  unfold signedFaceCoeff
  by_cases hface : ConsecutiveDistinct (deleteTupleAt i σ.1)
  · simp only [hface, dite_true]
    by_cases hEq : (⟨deleteTupleAt i σ.1, hface⟩ : MagnitudeChain α n) = τ
    · have hval : deleteTupleAt i σ.1 = τ.1 := congrArg Subtype.val hEq
      simp [hval]
    · have hval : deleteTupleAt i σ.1 ≠ τ.1 := fun h => hEq (Subtype.ext h)
      simp [hEq, hval]
  · simp only [hface, dite_false]
    have hval : deleteTupleAt i σ.1 ≠ τ.1 := fun h => hface (h ▸ τ.2)
    simp [hval]

/-- Deleting adjacent equal elements from a tuple produces the same result.
    If σ(k) = σ(k+1), then d_k(σ) = d_{k+1}(σ). -/
theorem deleteTupleAt_castSucc_eq_succ_of_eq {α : Type u} {n : Nat}
    (σ : Fin (n + 2) → α) (k : Fin (n + 1)) (hk : σ k.castSucc = σ k.succ) :
    deleteTupleAt k.castSucc σ = deleteTupleAt k.succ σ := by
  unfold deleteTupleAt
  funext p
  simp only [Function.comp]
  -- Need: σ(succAbove k.castSucc p) = σ(succAbove k.succ p)
  -- Use Mathlib's succAbove lemmas for castSucc and succ
  rcases Fin.lt_or_ge p k with hp | hp
  · -- p < k: both map p to p.castSucc
    rw [Fin.succAbove_castSucc_of_lt k p hp, Fin.succAbove_succ_of_le k p hp.le]
  · -- p ≥ k: castSucc maps p to p.succ
    rw [Fin.succAbove_castSucc_of_le k p hp]
    -- Goal: σ p.succ = σ (k.succ.succAbove p)
    rcases hp.eq_or_lt' with hp | hp
    · -- p = k
      subst hp
      rw [Fin.succAbove_succ_self]
      exact hk.symm
    · -- k < p: succ maps p to p.succ
      rw [Fin.succAbove_succ_of_lt k p hp]

/-- If `i` skips both endpoints of a consecutive equal pair in `σ`, then the
    face `d_i(σ)` inherits a consecutive equal pair and so is not CD. -/
theorem deleteTupleAt_not_cd_of_skip_pair {α : Type u} [DecidableEq α] {n : Nat}
    (σ : Fin (n + 2) → α) (k : Fin (n + 1)) (hk : σ k.castSucc = σ k.succ)
    (i : Fin (n + 2)) (hi1 : i ≠ k.castSucc) (hi2 : i ≠ k.succ) :
    ¬ConsecutiveDistinct (deleteTupleAt i σ) := by
  intro hcd
  simp only [ConsecutiveDistinct, deleteTupleAt, Function.comp] at hcd
  -- Convert Fin inequalities to Nat
  have hiv1 : i.val ≠ k.val :=
    fun h => hi1 (Fin.ext (by simp [Fin.coe_castSucc]; exact h))
  have hiv2 : i.val ≠ k.val + 1 :=
    fun h => hi2 (Fin.ext (by simp [Fin.val_succ]; exact h))
  by_cases hcase : i.val < k.val
  · -- Case 1: i.val < k.val. Witness p.val = k.val - 1.
    -- succAbove maps both p.castSucc and p.succ via the "succ" branch
    -- (both have val ≥ i.val), hitting k.castSucc and k.succ.
    have hpbound : k.val - 1 < n := by have := k.isLt; omega
    have hp := hcd ⟨k.val - 1, hpbound⟩
    apply hp; clear hp
    -- Evaluate succAbove at p.castSucc: val = k.val - 1 ≥ i.val, so → succ
    have hle1 : i ≤ Fin.castSucc (Fin.castSucc (⟨k.val - 1, hpbound⟩ : Fin n)) := by
      show i.val ≤ k.val - 1
      omega
    rw [Fin.succAbove_of_le_castSucc i _ hle1]
    -- Evaluate succAbove at p.succ: val = k.val ≥ i.val, so → succ
    have hle2 : i ≤ Fin.castSucc (Fin.succ (⟨k.val - 1, hpbound⟩ : Fin n)) := by
      show i.val ≤ k.val - 1 + 1
      omega
    rw [Fin.succAbove_of_le_castSucc i _ hle2]
    -- LHS = σ(val k.val) = σ(k.castSucc), RHS = σ(val k.val+1) = σ(k.succ)
    have h1 : Fin.succ (Fin.castSucc (⟨k.val - 1, hpbound⟩ : Fin n)) = k.castSucc :=
      Fin.ext (by simp [Fin.coe_castSucc]; omega)
    have h2 : Fin.succ (Fin.succ (⟨k.val - 1, hpbound⟩ : Fin n)) = k.succ :=
      Fin.ext (by simp [Fin.val_succ]; omega)
    rw [h1, h2]; exact hk
  · -- Case 2: i.val > k.val + 1. Witness p.val = k.val.
    -- succAbove maps both p.castSucc and p.succ via the "castSucc" branch
    -- (both have val < i.val), hitting k.castSucc and k.succ.
    have hgt : k.val + 1 < i.val := by omega
    have hpbound : k.val < n := by have := i.isLt; omega
    have hp := hcd ⟨k.val, hpbound⟩
    apply hp; clear hp
    -- Evaluate succAbove at p.castSucc: val = k.val < i.val, so → castSucc
    have hlt1 : Fin.castSucc (Fin.castSucc (⟨k.val, hpbound⟩ : Fin n)) < i := by
      show k.val < i.val
      omega
    rw [Fin.succAbove_of_castSucc_lt i _ hlt1]
    -- Evaluate succAbove at p.succ: val = k.val + 1 < i.val, so → castSucc
    have hlt2 : Fin.castSucc (Fin.succ (⟨k.val, hpbound⟩ : Fin n)) < i := by
      show k.val + 1 < i.val
      omega
    rw [Fin.succAbove_of_castSucc_lt i _ hlt2]
    -- LHS = σ(val k.val) = σ(k.castSucc), RHS = σ(val k.val+1) = σ(k.succ)
    have h1 : Fin.castSucc (Fin.castSucc (⟨k.val, hpbound⟩ : Fin n)) = k.castSucc :=
      Fin.ext (by simp [Fin.coe_castSucc])
    have h2 : Fin.castSucc (Fin.succ (⟨k.val, hpbound⟩ : Fin n)) = k.succ :=
      Fin.ext (by simp [Fin.val_succ])
    rw [h1, h2]; exact hk

/-- Key lemma: if σ is NOT ConsecutiveDistinct, then the alternating face sum
    `∑_i [d_i(σ) = τ] * (-1)^i` vanishes for any ConsecutiveDistinct target τ.

    Proof: σ has a consecutive equal pair at some position k. Only faces i=k.castSucc
    and i=k.succ can yield a CD target (all other faces preserve the equal pair).
    Since σ(k.castSucc) = σ(k.succ), deleting either gives the same result, and
    their signs (-1)^k + (-1)^(k+1) = 0 cancel. -/
theorem unnormFaceSum_vanishes_at_nonCD {α : Type u} [DecidableEq α] {n : Nat}
    (σ : Fin (n + 2) → α) (hσ : ¬ConsecutiveDistinct σ)
    (τ : Fin (n + 1) → α) (hτ : ConsecutiveDistinct τ) :
    (∑ i : Fin (n + 2), if deleteTupleAt i σ = τ then (-1 : ℤ) ^ i.val else 0) = 0 := by
  classical
  unfold ConsecutiveDistinct at hσ
  push_neg at hσ
  obtain ⟨k, hk⟩ := hσ
  have hother : ∀ i : Fin (n + 2), i ≠ k.castSucc → i ≠ k.succ →
      deleteTupleAt i σ ≠ τ := by
    intro i hi1 hi2 hdel
    exact deleteTupleAt_not_cd_of_skip_pair σ k hk i hi1 hi2 (hdel ▸ hτ)
  have hsame : deleteTupleAt k.castSucc σ = deleteTupleAt k.succ σ :=
    deleteTupleAt_castSucc_eq_succ_of_eq σ k hk
  -- Each term is 0 except possibly at i = k.castSucc and i = k.succ
  -- Rewrite each term
  have hrewrite : ∀ i : Fin (n + 2),
      (if deleteTupleAt i σ = τ then (-1 : ℤ) ^ i.val else 0) =
      (if i = k.castSucc then (if deleteTupleAt k.castSucc σ = τ then (-1 : ℤ) ^ k.castSucc.val else 0) else 0) +
      (if i = k.succ then (if deleteTupleAt k.castSucc σ = τ then (-1 : ℤ) ^ k.succ.val else 0) else 0) := by
    intro i
    by_cases hi1 : i = k.castSucc
    · subst hi1
      have hne : k.castSucc ≠ k.succ := by
        intro h; exact absurd (Fin.ext_iff.mp h) (by simp [Fin.val_succ, Fin.coe_castSucc])
      simp [hne]
    · by_cases hi2 : i = k.succ
      · subst hi2
        simp [hi1, ← hsame]
      · simp [hi1, hi2, hother i hi1 hi2]
  have hsum := Finset.sum_congr (rfl : Finset.univ = Finset.univ) (fun i _ => hrewrite i)
  rw [hsum, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases htarget : deleteTupleAt k.castSucc σ = τ
  · simp only [htarget, ite_true, Fin.val_succ, pow_succ, mul_neg, mul_one]
    simp [Fin.coe_castSucc]
  · simp [htarget]

/-- The unnormalized differential is insensitive to function values at non-ConsecutiveDistinct
    inputs when the target is ConsecutiveDistinct. -/
private theorem unnormDiff_congr_cd {α : Type u} [Fintype α] [DecidableEq α] {n : Nat}
    (g h : (Fin (n + 2) → α) → ℤ) (τ : Fin (n + 1) → α) (hτ : ConsecutiveDistinct τ)
    (heq : ∀ σ, ConsecutiveDistinct σ → g σ = h σ) :
    unnormDiff n g τ = unnormDiff n h τ := by
  simp only [unnormDiff, unnormSignedFaceCoeff]
  refine Finset.sum_congr rfl ?_
  intro σ _
  by_cases hcd : ConsecutiveDistinct σ
  · rw [heq σ hcd]
  · have hvanish : (∑ i : Fin (n + 2),
        if deleteTupleAt i σ = τ then (-1 : ℤ) ^ i.val else 0) = 0 :=
      unnormFaceSum_vanishes_at_nonCD σ hcd τ hτ
    rw [hvanish, mul_zero, mul_zero]

theorem magnitudeDifferential_squared {α : Type u} [Fintype α] [DecidableEq α] (n : Nat)
    (f : MagnitudeChain α (n + 2) → ℤ) (τ : MagnitudeChain α n) :
    magnitudeDifferential n (magnitudeDifferential (n + 1) f) τ = 0 := by
  classical
  calc magnitudeDifferential n (magnitudeDifferential (n + 1) f) τ
      = unnormDiff n (fun σ => if h : ConsecutiveDistinct σ then
          (magnitudeDifferential (n + 1) f) ⟨σ, h⟩ else 0) τ.1 :=
        magnitudeDifferential_eq_unnorm n _ τ
    _ = unnormDiff n (unnormDiff (n + 1)
          (fun ρ => if h : ConsecutiveDistinct ρ then f ⟨ρ, h⟩ else 0)) τ.1 := by
        exact unnormDiff_congr_cd _ _ τ.1 τ.2 fun σ hcd => by
          simp only [hcd, dite_true]
          exact magnitudeDifferential_eq_unnorm (n + 1) f ⟨σ, hcd⟩
    _ = 0 := unnormDiff_squared n _ τ.1

/-- The magnitude chain complex in the spectral-sequence interface. -/
def magnitudeChainComplex (α : Type u) [Fintype α] [DecidableEq α] :
    Algebra.SpectralSequence.DifferentialComplex where
  E := fun n => MagnitudeChain α n → ℤ
  zero := fun _ _ => 0
  d := fun n => magnitudeDifferential n
  d_zero := by
    intro n
    funext τ
    simp [magnitudeDifferential, signedFaceCoeff]
  d_squared := by
    intro n f
    funext τ
    exact magnitudeDifferential_squared n f τ

/-- For subsingleton carriers, positive-degree chain spaces are empty. -/
theorem magnitudeChain_empty_above_one_for_singleton (α : Type u) [Fintype α] [DecidableEq α]
    [Subsingleton α] (n : Nat) (hn : 0 < n) :
    IsEmpty (MagnitudeChain α n) := by
  refine ⟨?_⟩
  intro x
  let i0 : Fin n := ⟨0, hn⟩
  have hneq := x.2 i0
  have heq : x.1 i0.castSucc = x.1 i0.succ := Subsingleton.elim _ _
  exact hneq heq

/-- `MC₁(Bool)` has rank `2`. -/
theorem chainRank_bool_one : chainRank Bool 1 = 2 := by
  decide

/-- `MC₁(Fin 3)` has rank `6`. -/
theorem chainRank_fin3_one : chainRank (Fin 3) 1 = 6 := by
  decide

/-- `MC₂(Fin 3)` has rank `12`. -/
theorem chainRank_fin3_two : chainRank (Fin 3) 2 = 12 := by
  decide

end Magnitude
end Metrics
end HeytingLean
