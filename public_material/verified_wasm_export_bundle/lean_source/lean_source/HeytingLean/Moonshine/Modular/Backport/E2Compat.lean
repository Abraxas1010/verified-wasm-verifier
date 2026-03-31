import HeytingLean.Moonshine.Modular.Backport.E2Defs
import Mathlib.NumberTheory.TsumDivsorsAntidiagonal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Algebra.Group.EvenFunction

open UpperHalfPlane hiding I σ
open Filter Complex Finset SummationFilter ArithmeticFunction
open scoped Interval Real Topology Nat

noncomputable section

namespace Finset

lemma Icc_negSucc_succ_eq_insert_insert_Icc (N : ℕ) :
    Icc (-(N + 1 : ℤ)) (N + 1 : ℤ) =
      insert (-(N + 1 : ℤ)) (insert (N + 1 : ℤ) (Icc (-N : ℤ) (N : ℤ))) := by
  ext x
  simp [mem_Icc]
  omega

lemma Ico_negSucc_succ_eq_insert_insert_Ico (N : ℕ) :
    Ico (-(N + 1 : ℤ)) (N + 1 : ℤ) =
      insert (-(N + 1 : ℤ)) (insert (N : ℤ) (Ico (-N : ℤ) (N : ℤ))) := by
  ext x
  simp [mem_Ico]
  omega

lemma sum_Icc_of_even_eq_range {α : Type*} [AddCommGroup α] {f : ℤ → α}
    (hf : ∀ n : ℤ, f (-n) = f n) (N : ℕ) :
    ∑ m ∈ Icc (-N : ℤ) N, f m = (2 : ℕ) • (∑ m ∈ range (N + 1), f m) - f 0 := by
  induction N with
  | zero =>
      simp [two_nsmul, sub_eq_add_neg, add_assoc]
  | succ N ih =>
      have hnot1 : (-(N + 1 : ℤ)) ∉ insert (N + 1 : ℤ) (Icc (-N : ℤ) (N : ℤ)) := by
        simp [mem_Icc]
        omega
      have hnot2 : (N + 1 : ℤ) ∉ Icc (-N : ℤ) (N : ℤ) := by
        simp [mem_Icc]
      rw [Nat.cast_add, Nat.cast_one, Icc_negSucc_succ_eq_insert_insert_Icc, sum_insert hnot1,
        sum_insert hnot2]
      have hEvenTop : f (-(↑N + 1)) = f (↑N + 1) := by simpa using hf (↑N + 1)
      rw [hEvenTop, ih]
      simp [sum_range_succ, two_nsmul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

lemma sum_Ico_int_sub (b : ℕ) {α : Type*} [AddCommGroup α] (f : ℤ → α) :
    ∑ n ∈ Ico (-b : ℤ) b, (f n - f (n + 1)) = f (-b) - f b := by
  induction b with
  | zero => simp
  | succ b ih =>
      have hnot1 : (-(b + 1 : ℤ)) ∉ insert (b : ℤ) (Ico (-b : ℤ) (b : ℤ)) := by
        simp
      have hnot2 : (b : ℤ) ∉ Ico (-b : ℤ) (b : ℤ) := by
        simp [mem_Ico]
      rw [Nat.cast_add, Nat.cast_one, Ico_negSucc_succ_eq_insert_insert_Ico,
        sum_insert hnot1, sum_insert hnot2]
      rw [ih]
      abel

end Finset

namespace PNat

theorem tendsto_comp_val_iff {β : Type*} {f : ℕ → β} {l : Filter β} :
    Tendsto (fun x : ℕ+ => f x) atTop l ↔ Tendsto f atTop l := by
  exact tendsto_comp_val_Ioi_atTop

end PNat

lemma summable_pnat_iff_summable_nat {α : Type*} [AddCommGroup α] [TopologicalSpace α]
    [IsTopologicalAddGroup α]
    {f : ℕ → α} : Summable (fun x : ℕ+ => f x) ↔ Summable f := by
  constructor
  · intro h
    exact (summable_nat_add_iff 1).1 ((summable_pnat_iff_summable_succ (f := f)).1 h)
  · intro h
    exact (summable_pnat_iff_summable_succ (f := f)).2 ((summable_nat_add_iff 1).2 h)

lemma tsum_int_eq_zero_add_tsum_pnat {G : Type*} [AddCommGroup G] [UniformSpace G]
    [IsUniformAddGroup G] [CompleteSpace G] [T2Space G] {f : ℤ → G}
    (hf : ∀ n : ℤ, f (-n) = f n) (hf2 : Summable f) :
    ∑' n : ℤ, f n = f 0 + ∑' n : ℕ+, (f n + f (-n)) := by
  have hsplit := tsum_int_eq_zero_add_two_mul_tsum_pnat (f := f) hf hf2
  have hfp : Summable (fun n : ℕ+ => f n) := by
    simpa using hf2.comp_injective (show Function.Injective (fun n : ℕ+ => (n : ℤ)) from by
      intro a b h
      exact Subtype.ext (Int.ofNat.inj h))
  calc
    ∑' n : ℤ, f n = f 0 + (2 : ℕ) • ∑' n : ℕ+, f n := hsplit
    _ = f 0 + ∑' n : ℕ+, (f n + f (-n)) := by
      congr 1
      rw [two_nsmul, ← Summable.tsum_add hfp hfp]
      refine tsum_congr ?_
      intro n
      simp [hf]

lemma tendsto_inv_atTop_nhds_zero_nat {𝕜 : Type*} [RCLike 𝕜] :
    Tendsto (fun n : ℕ ↦ (n : 𝕜)⁻¹) atTop (𝓝 0) :=
  RCLike.tendsto_inverse_atTop_nhds_zero_nat 𝕜

lemma tendsto_PNat_val_atTop_atTop : Tendsto PNat.val atTop atTop :=
  tendsto_atTop_atTop_of_monotone (fun _ _ h ↦ h) fun a ↦ ⟨Nat.succPNat a, Nat.le_succ a⟩

lemma tendsto_zero_geometric_tsum_pnat {r : ℂ} (hr : ‖r‖ < 1) :
    Tendsto (fun m : ℕ+ ↦ ∑' n : ℕ+, r ^ (n * m : ℕ)) atTop (𝓝 0) := by
  have h1 (m : ℕ+) : ‖r ^ (m : ℕ)‖ < 1 := by
    rwa [norm_pow, pow_lt_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne _)]
  have h2 (m : ℕ+) : ∑' n : ℕ+, r ^ (n * m : ℕ) = (1 - r ^ (m : ℕ))⁻¹ - 1 := by
    have := tsum_geometric_of_norm_lt_one (h1 m)
    rw [← tsum_zero_pnat_eq_tsum_nat (summable_geometric_of_norm_lt_one (h1 m))] at this
    simp_rw [← this, pow_zero, add_sub_cancel_left, mul_comm, pow_mul]
  rw [funext h2, (by simp : 𝓝 (0 : ℂ) = 𝓝 ((1 - 0)⁻¹ - 1)), tendsto_sub_const_iff,
    tendsto_inv_iff₀ (by simp), tendsto_const_sub_iff]
  exact (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr).comp tendsto_PNat_val_atTop_atTop

lemma coe_mem_integerComplement (x : ℍ) : (x : ℂ) ∈ Complex.integerComplement := by
  rw [Complex.integerComplement, Set.mem_compl_iff, Set.mem_range]
  rintro ⟨n, hn⟩
  have him : (x : ℂ).im = (n : ℂ).im := by simp [hn]
  have him0 : (x : ℂ).im = 0 := by simpa using him
  have hx : (0 : ℝ) < (x : ℂ).im := x.2
  nlinarith [hx, him0]

lemma summable_cotTerm {x : ℂ} (hx : x ∈ Complex.integerComplement) : Summable (fun n ↦ cotTerm x n) :=
  Summable_cotTerm hx

lemma summable_cotTerm_pnat {x : ℂ} (hx : x ∈ Complex.integerComplement) :
    Summable (fun n : ℕ+ ↦ 1 / (x - n) + 1 / (x + n)) := by
  have hNat : Summable (fun n : ℕ ↦ 1 / (x - (n + 1)) + 1 / (x + (n + 1))) := by
    simpa [cotTerm, one_div] using (Summable_cotTerm hx)
  exact (summable_pnat_iff_summable_succ
    (f := fun n : ℕ ↦ 1 / (x - n) + 1 / (x + n))).2 <| by
      simpa [Nat.cast_add, Nat.cast_one] using hNat

lemma im_pnat_div_pos (N : ℕ+) (z : ℍ) : 0 < ((-((N : ℂ) / (z : ℂ))).im) := by
  have hz0 : (z : ℂ) ≠ 0 := ne_zero z
  have hzNorm : 0 < Complex.normSq (z : ℂ) := Complex.normSq_pos.mpr hz0
  have hN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
  have hIm : ((-((N : ℂ) / (z : ℂ))).im) = (N : ℝ) * (z : ℂ).im / Complex.normSq (z : ℂ) := by
    simp [Complex.div_im]
  rw [hIm]
  exact div_pos (mul_pos hN z.2) hzNorm

lemma UpperHalfPlane.int_div_mem_integerComplement (z : ℍ) (n : ℤ) (hn : n ≠ 0) :
    (-((n : ℂ) / (z : ℂ))) ∈ Complex.integerComplement := by
  rw [Complex.integerComplement, Set.mem_compl_iff, Set.mem_range]
  rintro ⟨m, hm⟩
  have hz0 : (z : ℂ) ≠ 0 := ne_zero z
  have hzNorm : Complex.normSq (z : ℂ) ≠ 0 := by
    intro h
    exact hz0 (Complex.normSq_eq_zero.mp h)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have him_ne : ((-((n : ℂ) / (z : ℂ))).im) ≠ 0 := by
    have hIm : ((-((n : ℂ) / (z : ℂ))).im) = (n : ℝ) * (z : ℂ).im / Complex.normSq (z : ℂ) := by
      simp [Complex.div_im]
    rw [hIm]
    exact div_ne_zero (mul_ne_zero hn0 (ne_of_gt z.2)) hzNorm
  have him0 : ((-((n : ℂ) / (z : ℂ))).im) = 0 := by
    calc
      ((-((n : ℂ) / (z : ℂ))).im) = (m : ℂ).im := by simp [hm]
      _ = 0 := by simp
  exact him_ne him0

namespace EisensteinSeries

lemma linear_isTheta_right_add (c e : ℤ) (z : ℂ) :
    (fun d : ℤ ↦ c * z + d + e) =Θ[cofinite] fun n ↦ (n : ℝ) := by
  apply Asymptotics.IsTheta.add_isLittleO <;>
  [refine Asymptotics.IsLittleO.add_isTheta ?_ (Int.cast_complex_isTheta_cast_real); skip] <;>
  simpa [-Int.cofinite_eq] using
    .inr <| tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding Int.isClosedEmbedding_coe_real

lemma linear_inv_isBigO_right_add (c e : ℤ) (z : ℂ) :
    (fun (d : ℤ) ↦ (c * z + d + e)⁻¹) =O[cofinite] fun n ↦ (n : ℝ)⁻¹ :=
  (linear_isTheta_right_add c e z).inv.isBigO

lemma tendsto_zero_inv_linear (z : ℂ) (b : ℤ) :
    Tendsto (fun d : ℕ ↦ 1 / ((b : ℂ) * z + d)) atTop (𝓝 0) := by
  have hInt : (fun d : ℤ ↦ (↑b * z + d)⁻¹) =O[atTop] fun d => (d : ℝ)⁻¹ :=
    (linear_inv_isBigO_right b z).mono atTop_le_cofinite
  have hNat : (fun d : ℕ ↦ (↑b * z + d)⁻¹) =O[atTop] fun d => (d : ℝ)⁻¹ := hInt.natCast_atTop
  have h0 : Tendsto (fun d : ℕ ↦ (↑b * z + d)⁻¹) atTop (𝓝 0) :=
    Asymptotics.IsBigO.trans_tendsto hNat (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact h0.congr' (Filter.Eventually.of_forall (by intro d; simp [one_div]))

lemma tendsto_zero_inv_linear_sub (z : ℂ) (b : ℤ) :
    Tendsto (fun d : ℕ ↦ 1 / ((b : ℂ) * z - d)) atTop (𝓝 0) := by
  have h : Tendsto (fun d : ℕ ↦ -(1 / (((-b : ℂ) * z + d)))) atTop (𝓝 0) := by
    simpa using (tendsto_zero_inv_linear z (-b)).neg
  refine h.congr' (Filter.Eventually.of_forall ?_)
  intro d
  calc
    -(1 / (((-b : ℂ) * z + d))) = -(((-b : ℂ) * z + d)⁻¹) := by simp [one_div]
    _ = (-↑d + ↑b * z : ℂ)⁻¹ := by
      have harg : (-↑b * z + ↑d : ℂ) = -(-↑d + ↑b * z) := by ring
      rw [harg, inv_neg, neg_neg]
    _ = 1 / ((b : ℂ) * z - d) := by
      have harg : (-↑d + ↑b * z : ℂ) = (↑b * z - d) := by ring
      simp [harg, one_div]

lemma summable_linear_right_add_one_mul_linear_right (z : ℂ) (c₁ c₂ : ℤ) :
    Summable fun n : ℤ ↦ ((c₁ * z + n + 1) * (c₂ * z + n))⁻¹ := by
  apply summable_inv_of_isBigO_rpow_inv (a := 2) (by norm_cast)
  simpa [pow_two] using (linear_inv_isBigO_right c₂ z).mul
    (linear_inv_isBigO_right_add c₁ 1 z)

lemma summable_linear_left_mul_linear_left {z : ℂ} (hz : z ≠ 0) (c₁ c₂ : ℤ) :
    Summable fun n : ℤ ↦ ((n * z + c₁) * (n * z + c₂))⁻¹ := by
  apply summable_inv_of_isBigO_rpow_inv (a := 2) (by norm_cast)
  simp only [Real.rpow_two, abs_mul_abs_self, pow_two]
  simpa using (linear_inv_isBigO_left c₂ hz).mul (linear_inv_isBigO_left c₁ hz)

private lemma aux_isBigO_linear (z : ℍ) (a b : ℤ) :
    (fun (m : Fin 2 → ℤ) ↦ ((m 0 + a : ℂ) * z + m 1 + b)⁻¹) =O[cofinite]
    fun (m : Fin 2 → ℤ) ↦ ‖![m 0 + a, m 1 + b]‖⁻¹ := by
  rw [Asymptotics.isBigO_iff]
  have h0 : z ∈ verticalStrip |z.re| z.im := by simp [mem_verticalStrip_iff]
  use ‖r ⟨⟨|z.re|, z.im⟩, z.2⟩‖⁻¹
  filter_upwards with m
  apply le_trans (by
    simpa [Real.rpow_neg_one, add_assoc] using
      summand_bound_of_mem_verticalStrip (k := (1 : ℝ)) zero_le_one ![m 0 + a, m 1 + b] z.2 h0)
  have hfactor :
      (r ⟨{ re := |z.re|, im := (z : ℂ).im }, by simpa using z.2⟩ : ℝ) =
      r ⟨{ re := |z.re|, im := z.im }, z.2⟩ := by
    simp [UpperHalfPlane.coe_im]
  have hr0 : 0 ≤ r ⟨{ re := |z.re|, im := z.im }, z.2⟩ := (r_pos _).le
  calc
    (r ⟨{ re := |z.re|, im := (z : ℂ).im }, by simpa using z.2⟩)⁻¹ * ‖![m 0 + a, m 1 + b]‖⁻¹ =
        (r ⟨{ re := |z.re|, im := z.im }, z.2⟩)⁻¹ * ‖![m 0 + a, m 1 + b]‖⁻¹ := by simp
    _ ≤ ‖r ⟨{ re := |z.re|, im := z.im }, z.2⟩‖⁻¹ * ‖‖![m 0 + a, m 1 + b]‖⁻¹‖ := by
        simp [Real.norm_eq_abs, abs_of_nonneg hr0]

lemma isLittleO_const_left_of_properSpace_of_discreteTopology
    {α : Type*} (a : α) [NormedAddCommGroup α] [DiscreteTopology α]
    [ProperSpace α] : (fun _ : α ↦ a) =o[cofinite] (‖·‖) := by
  rw [Asymptotics.isLittleO_const_left]
  exact Or.inr <| by
    have hnorm : Tendsto (fun x : α => ‖x‖) cofinite atTop := by
      simpa [Function.comp] using
      (tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding
        (e := (fun x : α => x)) Topology.IsClosedEmbedding.id)
    simpa [Function.comp] using (tendsto_norm_atTop_atTop.comp hnorm)

lemma vec_add_const_isTheta (a b : ℤ) :
    (fun (m : Fin 2 → ℤ) => ‖![m 0 + a, m 1 + b]‖⁻¹) =Θ[cofinite] (fun m => ‖m‖⁻¹) := by
  have hadd (x : Fin 2 → ℤ) : ![x 0 + a, x 1 + b] = x + ![a, b] := List.ofFn_inj.mp rfl
  simpa only [Asymptotics.isTheta_inv, Asymptotics.isTheta_norm_left, hadd] using
    (Asymptotics.IsTheta.add_isLittleO
      (by rw [← Asymptotics.isTheta_norm_left])
      (isLittleO_const_left_of_properSpace_of_discreteTopology ![a, b]))

lemma isBigO_linear_add_const_vec (z : ℍ) (a b : ℤ) :
    (fun m : (Fin 2 → ℤ) => (((m 0 : ℂ) + a) * z + m 1 + b)⁻¹) =O[cofinite] (fun m => ‖m‖⁻¹) :=
  (aux_isBigO_linear z a b).trans (vec_add_const_isTheta a b).isBigO

/-- If a function `ℤ² → E` is `O (‖n‖ ^ a)⁻¹` for `2 < a`, then it is summable. -/
lemma summable_of_isBigO_rpow_norm {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : (Fin 2 → ℤ) → E} {a : ℝ} (hab : 2 < a)
    (hf : f =O[cofinite] fun n ↦ (‖n‖ ^ a)⁻¹) : Summable f :=
  summable_of_isBigO
    ((summable_one_div_norm_rpow hab).congr fun b ↦ Real.rpow_neg (norm_nonneg b) a) hf

end EisensteinSeries

lemma tsum_eq_of_summable_unconditional {α β : Type*} [AddCommMonoid β]
    [TopologicalSpace β] [ContinuousAdd β] [T2Space β]
    {L : SummationFilter α} [L.LeAtTop] [L.NeBot] {f : α → β} (hf : Summable f) :
    ∑'[L] x, f x = ∑' x, f x := by
  have hsumUnc : HasSum f (∑' x, f x) := hf.hasSum
  have hsumL : HasSum f (∑' x, f x) L := by
    simpa [HasSum] using Filter.Tendsto.mono_left (show HasSum f (∑' x, f x) from hsumUnc)
      (SummationFilter.LeAtTop.le_atTop (L := L))
  exact (hsumL.summable.hasSum_iff).1 hsumL

lemma tsum_eq_of_summable_unconditional_symmetricIco {β : Type*} [AddCommGroup β]
    [TopologicalSpace β] [ContinuousAdd β] [ContinuousSub β] [T2Space β]
    [IsTopologicalAddGroup β]
    {f : ℤ → β} (hf : Summable f) : ∑'[symmetricIco ℤ] x, f x = ∑' x, f x := by
  have hsumIcc : HasSum f (∑' x, f x) (symmetricIcc ℤ) := by
    simpa [HasSum] using Filter.Tendsto.mono_left (show HasSum f (∑' x, f x) from hf.hasSum)
      (SummationFilter.LeAtTop.le_atTop (L := symmetricIcc ℤ))
  have hsIcc : Summable f (symmetricIcc ℤ) := hsumIcc.summable
  have hzeroNat : Tendsto (fun N : ℕ => f N) atTop (𝓝 0) := by
    have hcof : Tendsto f cofinite (𝓝 0) := hf.tendsto_cofinite_zero
    have hcast : Tendsto (fun N : ℕ => (N : ℤ)) atTop cofinite := by
      simpa [Nat.cofinite_eq_atTop] using
        (Int.ofNat_injective.tendsto_cofinite :
          Tendsto (fun N : ℕ => (N : ℤ)) cofinite cofinite)
    exact hcof.comp hcast
  have hIccIco : ∑'[symmetricIcc ℤ] x, f x = ∑'[symmetricIco ℤ] x, f x :=
    tsum_symmetricIcc_eq_tsum_symmetricIco hsIcc hzeroNat
  calc
    ∑'[symmetricIco ℤ] x, f x = ∑'[symmetricIcc ℤ] x, f x := hIccIco.symm
    _ = ∑' x, f x := (hsIcc.hasSum_iff).1 hsumIcc
