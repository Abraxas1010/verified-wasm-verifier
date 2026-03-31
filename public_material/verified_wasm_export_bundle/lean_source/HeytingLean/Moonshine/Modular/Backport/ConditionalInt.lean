/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Int
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Order.Filter.Interval
import Mathlib.Topology.Algebra.InfiniteSum.Defs


/-!
# Sums over symmetric integer intervals

This file contains some lemmas about sums over symmetric integer intervals `Ixx -N N` used, for
example in the definition of the Eisenstein series `E2`.
In particular we define `symmetricIcc`, `symmetricIco`, `symmetricIoc` and `symmetricIoo` as
`SummationFilter`s corresponding to the intervals `Icc -N N`, `Ico -N N`, `Ioc -N N` respectively.
We also prove that these filters are all `NeBot` and `LeAtTop`.

-/

section

open Finset Topology Function Filter SummationFilter

namespace SummationFilter

section IntervalFilters

variable (G : Type*) [Neg G] [Preorder G] [LocallyFiniteOrder G]

/-- The SummationFilter on a locally finite order `G` corresponding to the symmetric
intervals `Icc (-N) N`· -/
@[simps]
def symmetricIcc : SummationFilter G where
  filter := atTop.map (fun g ↦ Icc (-g) g)

/-- The SummationFilter on a locally finite order `G` corresponding to the symmetric
intervals `Ioo (-N) N`· Note that for `G = ℤ` this coincides with
`symmetricIcc` so one should use that. See `symmetricIcc_eq_symmetricIoo_int`. -/
@[simps]
def symmetricIoo : SummationFilter G where
  filter := atTop.map (fun g ↦ Ioo (-g) g)

/-- The SummationFilter on a locally finite order `G` corresponding to the symmetric
intervals `Ico (-N) N`· -/
@[simps]
def symmetricIco : SummationFilter G where
  filter := atTop.map (fun N ↦ Ico (-N) N)

/-- The SummationFilter on a locally finite order `G` corresponding to the symmetric
intervals `Ioc (-N) N`· -/
@[simps]
def symmetricIoc : SummationFilter G where
  filter := atTop.map (fun N ↦ Ioc (-N) N)

variable [(atTop : Filter G).NeBot]

instance : (symmetricIcc G).NeBot where
  ne_bot := by simp [symmetricIcc, Filter.NeBot.map]

instance : (symmetricIco G).NeBot where
  ne_bot := by simp [symmetricIco, Filter.NeBot.map]

instance : (symmetricIoc G).NeBot where
  ne_bot := by simp [symmetricIoc, Filter.NeBot.map]

instance : (symmetricIoo G).NeBot where
  ne_bot := by simp [symmetricIoo, Filter.NeBot.map]

section LeAtTop

variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G] [LocallyFiniteOrder G]

lemma symmetricIcc_le_Conditional :
    (symmetricIcc G).filter ≤ (conditional G).filter :=
  Filter.map_mono (tendsto_neg_atTop_atBot.prodMk tendsto_id)

instance : (symmetricIcc G).LeAtTop where
  le_atTop := le_trans symmetricIcc_le_Conditional (conditional G).le_atTop

variable [NoTopOrder G] [NoBotOrder G]

end LeAtTop

end IntervalFilters
section Int

variable {α : Type*} {f : ℤ → α} [CommGroup α] [TopologicalSpace α] [ContinuousMul α]

lemma symmetricIcc_eq_map_Icc_nat :
    (symmetricIcc ℤ).filter = atTop.map (fun N : ℕ ↦ Icc (-(N : ℤ)) N) := by
  simp [← Nat.map_cast_int_atTop, Function.comp_def]

lemma symmetricIcc_eq_symmetricIoo_int : symmetricIcc ℤ = symmetricIoo ℤ := by
  simp only [symmetricIcc, symmetricIoo, mk.injEq]
  ext s
  simp only [← Nat.map_cast_int_atTop, Filter.map_map, Filter.mem_map, mem_atTop_sets, ge_iff_le,
    Set.mem_preimage, comp_apply]
  refine ⟨fun ⟨a, ha⟩ ↦ ⟨a + 1, fun b hb ↦ ?_⟩, fun ⟨a, ha⟩ ↦ ⟨a - 1, fun b hb ↦ ?_⟩⟩ <;>
  [convert ha (b - 1) (by grind) using 1; convert ha (b + 1) (by grind) using 1] <;>
  simpa [Finset.ext_iff] using by grind

lemma _root_.HasSum.hasSum_symmetricIco_of_hasSum_symmetricIcc
    {F : Type*} [AddCommGroup F] [TopologicalSpace F] [ContinuousAdd F] [ContinuousSub F]
    {f : ℤ → F} {a : F}
    (hf : HasSum f a (symmetricIcc ℤ)) (hf2 : Tendsto (fun N : ℕ ↦ f N) atTop (𝓝 0)) :
    HasSum f a (symmetricIco ℤ) := by
  simp only [HasSum, tendsto_map'_iff, symmetricIcc_eq_map_Icc_nat,
    ← Nat.map_cast_int_atTop, symmetricIco] at hf ⊢
  have hsum :
      Tendsto (fun N : ℕ ↦ (∑ n ∈ Ico (-(N : ℤ)) (N : ℤ), f n) + f N) atTop (𝓝 a) := by
    refine hf.congr' ?_
    · refine Filter.Eventually.of_forall ?_
      intro N
      simpa using (Finset.sum_Ico_add_eq_sum_Icc (f := f) (a := (-(N : ℤ))) (b := (N : ℤ))
        (by omega)).symm
  have hIco : Tendsto (fun N : ℕ ↦ ∑ n ∈ Ico (-(N : ℤ)) (N : ℤ), f n) atTop (𝓝 a) := by
    simpa [add_assoc, add_comm, add_left_comm] using hsum.sub hf2
  simpa using hIco

lemma _root_.Summable.summable_symmetricIco_of_summable_symmetricIcc
    {F : Type*} [AddCommGroup F] [TopologicalSpace F] [ContinuousAdd F] [ContinuousSub F]
    {f : ℤ → F}
    (hf : Summable f (symmetricIcc ℤ)) (hf2 : Tendsto (fun N : ℕ ↦ f N) atTop (𝓝 0)) :
    Summable f (symmetricIco ℤ) :=
  (hf.hasSum.hasSum_symmetricIco_of_hasSum_symmetricIcc hf2).summable

lemma tsum_symmetricIcc_eq_tsum_symmetricIco
    {F : Type*} [AddCommGroup F] [TopologicalSpace F] [T2Space F]
    [ContinuousAdd F] [ContinuousSub F]
    {f : ℤ → F}
    (hf : Summable f (symmetricIcc ℤ)) (hf2 : Tendsto (fun N : ℕ ↦ f N) atTop (𝓝 0)) :
    ∑'[symmetricIcc ℤ] b, f b = ∑'[symmetricIco ℤ] b, f b := by
  have hIco : HasSum f (∑'[symmetricIcc ℤ] b, f b) (symmetricIco ℤ) :=
    (hf.hasSum).hasSum_symmetricIco_of_hasSum_symmetricIcc hf2
  exact (hf.hasSum.tsum_eq).trans hIco.tsum_eq.symm

@[to_additive]
lemma hasProd_symmetricIcc_iff {α : Type*} [CommMonoid α] [TopologicalSpace α]
    {f : ℤ → α} {a : α} : HasProd f a (symmetricIcc ℤ) ↔
    Tendsto (fun N : ℕ ↦ ∏ n ∈ Icc (-(N : ℤ)) N, f n) atTop (𝓝 a) := by
  simp [HasProd, symmetricIcc, ← Nat.map_cast_int_atTop, comp_def]

@[to_additive]
lemma hasProd_symmetricIco_int_iff {α : Type*} [CommMonoid α] [TopologicalSpace α]
    {f : ℤ → α} {a : α} : HasProd f a (symmetricIco ℤ) ↔
    Tendsto (fun N : ℕ ↦ ∏ n ∈ Ico (-(N : ℤ)) (N : ℤ), f n) atTop (𝓝 a) := by
  simp [HasProd, symmetricIco, ← Nat.map_cast_int_atTop, comp_def]

@[to_additive]
lemma hasProd_symmetricIoc_int_iff {α : Type*} [CommMonoid α] [TopologicalSpace α]
    {f : ℤ → α} {a : α} : HasProd f a (symmetricIoc ℤ) ↔
    Tendsto (fun N : ℕ ↦ ∏ n ∈ Ioc (-(N : ℤ)) (N : ℤ), f n) atTop (𝓝 a) := by
  simp [HasProd, symmetricIoc, ← Nat.map_cast_int_atTop, comp_def]

lemma _root_.Summable.tendsto_zero_of_even_summable_symmetricIcc {F : Type*} [NormedAddCommGroup F]
    [NormSMulClass ℤ F] {f : ℤ → F} (hf : Summable f (symmetricIcc ℤ))
    (hs : ∀ n : ℤ, f (-n) = f n) :
    Tendsto f atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  obtain ⟨L, hL⟩ := hf
  rw [HasSum, symmetricIcc_filter, tendsto_map'_iff, Function.comp_def] at hL
  have := hL.sub (hL.comp (tendsto_atTop_add_const_right _ (-1) tendsto_id))
  simp only [id_eq, Int.reduceNeg, Function.comp_apply, sub_self, ← sub_eq_add_neg] at this
  rw [tendsto_zero_iff_norm_tendsto_zero] at this
  refine (mul_zero (_ : ℝ) ▸ this.const_mul 2⁻¹).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hxle : (-(x : ℤ)) ≤ x := by omega
  have hIoc : Ioc (-(x : ℤ)) x = Icc (-(x - 1)) x := by
    ext n
    constructor <;> intro hn
    · rcases Finset.mem_Ioc.mp hn with ⟨h1, h2⟩
      exact Finset.mem_Icc.mpr (by omega)
    · rcases Finset.mem_Icc.mp hn with ⟨h1, h2⟩
      exact Finset.mem_Ioc.mpr (by omega)
  have hSx :
      (∑ b ∈ Icc (-(x : ℤ)) x, f b)
        = f (-x) + ∑ b ∈ Icc (-(x - 1)) x, f b := by
    have haux :
        f (-x) + ∑ b ∈ Ioc (-(x : ℤ)) x, f b = ∑ b ∈ Icc (-(x : ℤ)) x, f b := by
      simpa using (Finset.add_sum_Ioc_eq_sum_Icc (f := f) (a := (-(x : ℤ))) (b := x) hxle)
    simpa [hIoc] using haux.symm
  have hIco : Ico (-(x - 1)) x = Icc (-(x - 1)) (x - 1) := by
    ext n
    constructor <;> intro hn
    · rcases Finset.mem_Ico.mp hn with ⟨h1, h2⟩
      exact Finset.mem_Icc.mpr (by omega)
    · rcases Finset.mem_Icc.mp hn with ⟨h1, h2⟩
      exact Finset.mem_Ico.mpr (by omega)
  have hSprev :
      (∑ b ∈ Icc (-(x - 1)) x, f b)
        = (∑ b ∈ Icc (-(x - 1)) (x - 1), f b) + f x := by
    have haux :
        (∑ b ∈ Ico (-(x - 1)) x, f b) + f x = ∑ b ∈ Icc (-(x - 1)) x, f b :=
      Finset.sum_Ico_add_eq_sum_Icc (f := f) (a := (-(x - 1))) (b := x) (by omega)
    calc
      (∑ b ∈ Icc (-(x - 1)) x, f b)
          = (∑ b ∈ Ico (-(x - 1)) x, f b) + f x := haux.symm
      _ = (∑ b ∈ Icc (-(x - 1)) (x - 1), f b) + f x := by rw [hIco]
  have hdiff :
      (∑ b ∈ Icc (-(x : ℤ)) x, f b) - (∑ b ∈ Icc (-(x - 1)) (x - 1), f b) = f (-x) + f x := by
    calc
      (∑ b ∈ Icc (-(x : ℤ)) x, f b) - (∑ b ∈ Icc (-(x - 1)) (x - 1), f b)
          = (f (-x) + ∑ b ∈ Icc (-(x - 1)) x, f b) - (∑ b ∈ Icc (-(x - 1)) (x - 1), f b) := by
              rw [hSx]
      _ = (f (-x) + ((∑ b ∈ Icc (-(x - 1)) (x - 1), f b) + f x))
            - (∑ b ∈ Icc (-(x - 1)) (x - 1), f b) := by rw [hSprev]
      _ = f (-x) + f x := by abel_nf
  have h2 : f (-x) + f x = (2 : ℤ) • f x := by
    rw [hs x]
    simp [two_zsmul]
  calc
    (2⁻¹ : ℝ) * ‖(∑ b ∈ Icc (-(x : ℤ)) x, f b) - (∑ b ∈ Icc (-(x - 1)) (x - 1), f b)‖
        = (2⁻¹ : ℝ) * ‖f (-x) + f x‖ := by rw [hdiff]
    _ = (2⁻¹ : ℝ) * ‖(2 : ℤ) • f x‖ := by rw [h2]
    _ = (2⁻¹ : ℝ) * ((2 : ℝ) * ‖f x‖) := by
      have hnorm : ‖(2 : ℤ) • f x‖ = ‖(2 : ℤ)‖ * ‖f x‖ := by
        simpa using (norm_smul (2 : ℤ) (f x))
      have hnorm2 : ‖(2 : ℤ)‖ = (2 : ℝ) := by
        exact_mod_cast (Int.norm_natCast (n := 2))
      rw [hnorm, hnorm2]
    _ = ‖f x‖ := by ring

end Int

end SummationFilter
