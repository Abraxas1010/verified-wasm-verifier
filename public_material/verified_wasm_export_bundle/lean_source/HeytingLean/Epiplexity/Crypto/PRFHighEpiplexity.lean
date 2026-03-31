import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import HeytingLean.Epiplexity.Bounds
import HeytingLean.Epiplexity.Crypto.Axioms
import HeytingLean.Epiplexity.Crypto.HeavySet

namespace HeytingLean
namespace Epiplexity
namespace Crypto

open scoped BigOperators

noncomputable section

open HeytingLean.Probability
open HeytingLean.Probability.InfoTheory
open HeytingLean.Epiplexity.Info

open FinDist

/-!
Theorem 24 (paper): PRF ⇒ existence of high-epiplexity distributions.

This file formalizes the **counting/union-bound core** of the proof, phrased on finite types.

Key point: our `Distinguisher` is deterministic, so we use a *majority* test over all inputs
`x : BitStr m` rather than sampling a random query inside the distinguisher.
-/

namespace PRFHighEpiplexity

namespace BitStr

instance (n : Nat) : Nonempty (BitStr n) := by
  refine ⟨⟨0, ?_⟩⟩
  exact Nat.pow_pos (a := 2) (n := n) (Nat.succ_pos 1)

end BitStr

variable {m k : Nat}

/-! ### PRF-induced pair distribution `P_K` -/

/-- The paper’s `P_K`: sample `x ~ U_m` and output `z = (x, F_K x)`. -/
noncomputable def prfPairDist (F : BitStr m → BitStr m → BitStr k) (K : BitStr m) :
    FinDist (BitStr m × BitStr k) where
  pmf z := if z.2 = F K z.1 then 1 / (Fintype.card (BitStr m) : ℝ) else 0
  nonneg z := by
    by_cases h : z.2 = F K z.1 <;> simp [h]
  sum_one := by
    classical
    -- Sum over `x`, then over `y`.
    have hswap :
        (∑ z : BitStr m × BitStr k, (if z.2 = F K z.1 then 1 / (Fintype.card (BitStr m) : ℝ) else 0))
          = ∑ x : BitStr m, ∑ y : BitStr k,
              (if y = F K x then 1 / (Fintype.card (BitStr m) : ℝ) else 0) := by
      simpa using (Fintype.sum_prod_type
        (fun z : BitStr m × BitStr k =>
          (if z.2 = F K z.1 then 1 / (Fintype.card (BitStr m) : ℝ) else 0)))
    -- Each inner sum has exactly one nonzero term.
    have hinner : ∀ x : BitStr m,
        (∑ y : BitStr k, (if y = F K x then 1 / (Fintype.card (BitStr m) : ℝ) else 0))
          = 1 / (Fintype.card (BitStr m) : ℝ) := by
      intro x
      simp
    calc
      (∑ z : BitStr m × BitStr k, (if z.2 = F K z.1 then 1 / (Fintype.card (BitStr m) : ℝ) else 0))
          = ∑ x : BitStr m, ∑ y : BitStr k,
              (if y = F K x then 1 / (Fintype.card (BitStr m) : ℝ) else 0) := hswap
      _ = ∑ x : BitStr m, (1 / (Fintype.card (BitStr m) : ℝ)) := by
            simp
      _ = (Fintype.card (BitStr m) : ℝ) * (1 / (Fintype.card (BitStr m) : ℝ)) := by
            simp [Finset.sum_const]
      _ = 1 := by
            have hcard0 : (Fintype.card (BitStr m) : ℝ) ≠ 0 := by
              exact_mod_cast (ne_of_gt (Fintype.card_pos (α := BitStr m)))
            simp [one_div]

theorem entropyNat_prfPairDist (F : BitStr m → BitStr m → BitStr k) (K : BitStr m) :
    FinDist.entropy (prfPairDist (m := m) (k := k) F K) =
      Real.log (Fintype.card (BitStr m) : ℝ) := by
  classical
  -- Compute directly: `P_K` is uniform on `2^m` points, with zeros elsewhere (which contribute `0`).
  let c : ℝ := 1 / (Fintype.card (BitStr m) : ℝ)
  have hc_pos : 0 < c := by
    have hcard_pos : 0 < (Fintype.card (BitStr m) : ℝ) := by
      exact_mod_cast (Fintype.card_pos (α := BitStr m))
    dsimp [c]
    exact one_div_pos.mpr hcard_pos
  have hc_not_le : ¬c ≤ 0 := not_le_of_gt hc_pos
  have hterm_c :
      InfoTheory.entropyTerm c = (-c) * Real.log c := by
    simp [InfoTheory.entropyTerm, hc_not_le, InfoTheory.safeLog_of_pos hc_pos]
  have hterm0 : InfoTheory.entropyTerm (0 : ℝ) = 0 := by
    simp [InfoTheory.entropyTerm]
  -- Expand entropy over `x,y` and simplify the inner `y` sum.
  unfold FinDist.entropy prfPairDist
  have hswap :
      (∑ z : BitStr m × BitStr k,
          InfoTheory.entropyTerm
            (if z.2 = F K z.1 then (1 / (Fintype.card (BitStr m) : ℝ)) else 0))
        = ∑ x : BitStr m, ∑ y : BitStr k,
            InfoTheory.entropyTerm
              (if y = F K x then (1 / (Fintype.card (BitStr m) : ℝ)) else 0) := by
    simpa using (Fintype.sum_prod_type
      (fun z : BitStr m × BitStr k =>
        InfoTheory.entropyTerm
          (if z.2 = F K z.1 then (1 / (Fintype.card (BitStr m) : ℝ)) else 0)))
  have hinner : ∀ x : BitStr m,
      (∑ y : BitStr k,
          InfoTheory.entropyTerm
            (if y = F K x then (1 / (Fintype.card (BitStr m) : ℝ)) else 0))
        = InfoTheory.entropyTerm c := by
    intro x
    -- Exactly one `y` hits, the rest contribute `0`.
    have hfun :
        (fun y : BitStr k =>
            InfoTheory.entropyTerm (if y = F K x then (1 / (Fintype.card (BitStr m) : ℝ)) else 0))
          =
        (fun y : BitStr k =>
            if y = F K x then InfoTheory.entropyTerm (1 / (Fintype.card (BitStr m) : ℝ))
            else InfoTheory.entropyTerm 0) := by
      funext y
      by_cases hy : y = F K x <;> simp [hy]
    have hsum_rewrite :
        (∑ y : BitStr k,
            InfoTheory.entropyTerm (if y = F K x then (1 / (Fintype.card (BitStr m) : ℝ)) else 0))
          =
        ∑ y : BitStr k,
          if y = F K x then InfoTheory.entropyTerm (1 / (Fintype.card (BitStr m) : ℝ))
          else InfoTheory.entropyTerm 0 := by
      simpa using congrArg (fun g : BitStr k → ℝ => (∑ y : BitStr k, g y)) hfun
    rw [hsum_rewrite]
    simp [c]
  calc
    (∑ z : BitStr m × BitStr k,
        InfoTheory.entropyTerm
          (if z.2 = F K z.1 then (1 / (Fintype.card (BitStr m) : ℝ)) else 0))
        = ∑ x : BitStr m, ∑ y : BitStr k,
            InfoTheory.entropyTerm
              (if y = F K x then (1 / (Fintype.card (BitStr m) : ℝ)) else 0) := hswap
    _ = ∑ x : BitStr m, InfoTheory.entropyTerm c := by
          refine Fintype.sum_congr _ _ ?_
          intro x
          exact hinner x
    _ = (Fintype.card (BitStr m) : ℝ) * InfoTheory.entropyTerm c := by
          simp [Finset.sum_const]
    _ = (Fintype.card (BitStr m) : ℝ) * ((-c) * Real.log c) := by
          simp [hterm_c]
    _ = -Real.log c := by
          have hcardc : (Fintype.card (BitStr m) : ℝ) * c = 1 := by
            simp [c, one_div]
          calc
            (Fintype.card (BitStr m) : ℝ) * ((-c) * Real.log c)
                = -((Fintype.card (BitStr m) : ℝ) * c) * Real.log c := by
                    ring
            _ = -Real.log c := by
                  rw [hcardc]
                  simp
    _ = Real.log (Fintype.card (BitStr m) : ℝ) := by
          simp [c, one_div, Real.log_inv]

theorem entropyBits_prfPairDist (F : BitStr m → BitStr m → BitStr k) (K : BitStr m) :
    Info.entropyBits (prfPairDist (m := m) (k := k) F K) = m := by
  classical
  unfold Info.entropyBits
  have hnat :
      FinDist.entropy (prfPairDist (m := m) (k := k) F K)
        = Real.log (Fintype.card (BitStr m) : ℝ) :=
    entropyNat_prfPairDist (m := m) (k := k) (F := F) (K := K)
  have hlog2_pos : 0 < Real.log (2 : ℝ) := by
    have : (1 : ℝ) < 2 := by norm_num
    simpa using Real.log_pos this
  have hlog2_ne0 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt hlog2_pos
  calc
    FinDist.entropy (prfPairDist (m := m) (k := k) F K) / Real.log 2
        = Real.log (Fintype.card (BitStr m) : ℝ) / Real.log 2 := by
            simp [hnat]
    _ = ((m : ℝ) * Real.log 2) / Real.log 2 := by
          simp [BitStr, Nat.cast_pow, Real.log_pow]
    _ = m := by simp [hlog2_ne0]

/-! ### Heavy-set distinguisher (deterministic via majority) -/

variable (m k)

/-- Uniform distribution over PRF queries `x : BitStr m`. -/
noncomputable def UX : FinDist (BitStr m) :=
  Epiplexity.FinDist.uniform (α := BitStr m)

/-- Uniform distribution over outputs `y : BitStr k`. -/
noncomputable def UY : FinDist (BitStr k) :=
  Epiplexity.FinDist.uniform (α := BitStr k)

/-- Uniform distribution over oracle functions `O : BitStr m → BitStr k`. -/
noncomputable def UO : FinDist (BitStr m → BitStr k) :=
  Epiplexity.FinDist.uniform (α := (BitStr m → BitStr k))

/-- The heavy-set mass (under uniform `x`) induced by an oracle `O`. -/
noncomputable def heavyFraction (Q : FinDist (BitStr m × BitStr k)) (t : Nat)
    (O : BitStr m → BitStr k) : ℝ :=
  probEvent (UX m) (fun x => heavyThreshold m t ≤ Q.pmf (x, O x))

/-- Deterministic distinguisher: output `true` iff at least half of inputs land in the heavy set. -/
noncomputable def heavySetMajorityDistinguisher (Q : FinDist (BitStr m × BitStr k)) (t : Nat) :
    Distinguisher (BitStr m → BitStr k) where
  run O := if (1 / 2 : ℝ) ≤ heavyFraction (m := m) (k := k) Q t O then true else false
  runtime := 0

theorem heavySetMajorityDistinguisher_spec (Q : FinDist (BitStr m × BitStr k)) (t : Nat)
    (O : BitStr m → BitStr k) :
    (heavySetMajorityDistinguisher (m := m) (k := k) Q t).run O = true ↔
      (1 / 2 : ℝ) ≤ heavyFraction (m := m) (k := k) Q t O := by
  by_cases h : (1 / 2 : ℝ) ≤ heavyFraction (m := m) (k := k) Q t O <;>
    simp [heavySetMajorityDistinguisher]

/-! ### Uniform oracle evaluation is uniform -/

theorem uniform_eval_apply_eq_uniform (x : BitStr m) :
    FinDist.map (fun O : BitStr m → BitStr k => O x) (UO (m := m) (k := k))
      = UY (k := k) := by
  classical
  ext y
  unfold UO UY Epiplexity.FinDist.uniform FinDist.map
  simp only
  -- Rewrite the pmf as `(#fiber) * (1 / cardFun)`.
  let fiber : Finset (BitStr m → BitStr k) := {O | O x = y}
  have hsum :
      (∑ O : BitStr m → BitStr k,
          if O x = y then 1 / (Fintype.card (BitStr m → BitStr k) : ℝ) else 0)
        =
        ((fiber.card : ℝ) * (1 / (Fintype.card (BitStr m → BitStr k) : ℝ))) := by
    have hfilter :
        (∑ O : BitStr m → BitStr k,
            if O x = y then 1 / (Fintype.card (BitStr m → BitStr k) : ℝ) else 0)
          =
        ∑ _O ∈ fiber, (1 / (Fintype.card (BitStr m → BitStr k) : ℝ)) := by
      simpa [fiber] using
        (Finset.sum_filter (s := (Finset.univ : Finset (BitStr m → BitStr k)))
          (p := fun O : BitStr m → BitStr k => O x = y)
          (f := fun _ : BitStr m → BitStr k => (1 / (Fintype.card (BitStr m → BitStr k) : ℝ)))).symm
    rw [hfilter]
    simp [Finset.sum_const]
  have hfiber_card :
      (fiber.card : ℝ) = (Fintype.card {O : BitStr m → BitStr k // O x = y} : ℝ) := by
    have hnat :
        Fintype.card {O : BitStr m → BitStr k // O x = y} = fiber.card := by
      simpa [fiber] using (Fintype.card_subtype (p := fun O : BitStr m → BitStr k => O x = y))
    exact_mod_cast hnat.symm
  -- Cardinality of the fiber `O x = y`.
  have hcard_fiber :
      Fintype.card {O : BitStr m → BitStr k // O x = y} =
        (Fintype.card (BitStr k)) ^ (Fintype.card (BitStr m) - 1) := by
    -- Equivalence: functions on the complement of `x` determine the fiber.
    let δ : BitStr m → Prop := fun x' => x' ≠ x
    have heqv : {O : BitStr m → BitStr k // O x = y} ≃ ({x' : BitStr m // δ x'} → BitStr k) := by
      refine
        { toFun := fun O => fun x' => O.1 x'.1
          invFun := fun g =>
            ⟨fun x' => if hx : x' = x then y else g ⟨x', hx⟩, by simp⟩
          left_inv := ?_
          right_inv := ?_ }
      · intro O
        apply Subtype.ext
        funext x'
        by_cases hx : x' = x
        · subst hx
          simpa using O.2.symm
        · simp [hx]
      · intro g
        funext x'
        have hx : (x'.1 : BitStr m) ≠ x := x'.2
        simp [δ, hx]
    have hcard_dom : Fintype.card {x' : BitStr m // δ x'} = Fintype.card (BitStr m) - 1 := by
      simp [δ, Fintype.card_subtype_compl (α := BitStr m) (p := fun x' : BitStr m => x' = x)]
    calc
      Fintype.card {O : BitStr m → BitStr k // O x = y}
          = Fintype.card ({x' : BitStr m // δ x'} → BitStr k) := Fintype.card_congr heqv
      _ = (Fintype.card (BitStr k)) ^ (Fintype.card {x' : BitStr m // δ x'}) := by
            exact Fintype.card_fun
      _ = (Fintype.card (BitStr k)) ^ (Fintype.card (BitStr m) - 1) := by simp [hcard_dom]
  have hcard_fun :
      Fintype.card (BitStr m → BitStr k) = (Fintype.card (BitStr k)) ^ (Fintype.card (BitStr m)) := by
    exact Fintype.card_fun
  -- Evaluate the resulting ratio.
  rw [hsum, hfiber_card]
  have hratio :
      ((Fintype.card {O : BitStr m → BitStr k // O x = y} : ℝ) /
          (Fintype.card (BitStr m → BitStr k) : ℝ))
        = 1 / (Fintype.card (BitStr k) : ℝ) := by
    have hfiberR :
        (Fintype.card {O : BitStr m → BitStr k // O x = y} : ℝ)
          = (Fintype.card (BitStr k) : ℝ) ^ (Fintype.card (BitStr m) - 1) := by
      simp [hcard_fiber]
    have hfunR :
        (Fintype.card (BitStr m → BitStr k) : ℝ)
          = (Fintype.card (BitStr k) : ℝ) ^ (Fintype.card (BitStr m)) := by
      simp [hcard_fun]
    have hcardX_pos : 0 < Fintype.card (BitStr m) := Fintype.card_pos (α := BitStr m)
    have hcardX_ge1 : 1 ≤ Fintype.card (BitStr m) := (Nat.succ_le_iff).2 hcardX_pos
    have hsub : Fintype.card (BitStr m) - 1 + 1 = Fintype.card (BitStr m) :=
      Nat.sub_add_cancel hcardX_ge1
    have hdenom :
        ((Fintype.card (BitStr k) : ℝ) ^ (Fintype.card (BitStr m)))
          =
        ((Fintype.card (BitStr k) : ℝ) ^ (Fintype.card (BitStr m) - 1)) *
          (Fintype.card (BitStr k) : ℝ) := by
      rw [hsub.symm, pow_add]
      simp
    have hbase_ne0 : (Fintype.card (BitStr k) : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Fintype.card_pos (α := BitStr k)))
    have hpow_ne0 :
        ((Fintype.card (BitStr k) : ℝ) ^ (Fintype.card (BitStr m) - 1)) ≠ 0 := by
      exact pow_ne_zero _ hbase_ne0
    calc
      (Fintype.card {O : BitStr m → BitStr k // O x = y} : ℝ) /
          (Fintype.card (BitStr m → BitStr k) : ℝ)
          = ((Fintype.card (BitStr k) : ℝ) ^ (Fintype.card (BitStr m) - 1)) /
              ((Fintype.card (BitStr k) : ℝ) ^ (Fintype.card (BitStr m))) := by
                rw [hfiberR, hfunR]
      _ = ((Fintype.card (BitStr k) : ℝ) ^ (Fintype.card (BitStr m) - 1)) /
            (((Fintype.card (BitStr k) : ℝ) ^ (Fintype.card (BitStr m) - 1)) *
              (Fintype.card (BitStr k) : ℝ)) := by
              rw [hdenom]
      _ = (1 : ℝ) / (Fintype.card (BitStr k) : ℝ) := by
            field_simp [hpow_ne0]
      _ = 1 / (Fintype.card (BitStr k) : ℝ) := by simp
  -- `card * (1/cardFun) = card/cardFun`.
  simpa [div_eq_mul_inv] using hratio

/-! ### Core bound `p_{Q,t}` (paper Eq. 32), using the majority distinguisher -/

variable (F : BitStr m → BitStr m → BitStr k) (ε : Nat → ℝ) (T : Nat)

noncomputable def PRFOracleDist : FinDist (BitStr m → BitStr k) :=
  FinDist.map (fun key : BitStr m => F key) (Epiplexity.FinDist.uniform (α := BitStr m))

theorem probTrue_map_eq_probEvent {α β : Type u} [Fintype α] [Fintype β]
    (P : FinDist α) (f : α → β) (D : β → Bool) :
    probTrue (FinDist.map f P) D = probEvent P (fun a => D (f a) = true) := by
  classical
  unfold probTrue probEvent FinDist.map
  simp [mul_ite]
  -- Pull the `D x = true` test inside the inner sum.
  have hpull :
      (∑ x : β, if D x = true then ∑ a : α, if f a = x then P.pmf a else 0 else 0)
        =
      ∑ x : β, ∑ a : α, if D x = true then if f a = x then P.pmf a else 0 else 0 := by
    refine Fintype.sum_congr _ _ ?_
    intro x
    by_cases hx : D x = true <;> simp [hx]
  -- Swap the order of summation (`x` then `a`).
  have hswap :
      (∑ x : β, ∑ a : α, if D x = true then if f a = x then P.pmf a else 0 else 0)
        =
      ∑ a : α, ∑ x : β, if D x = true then if f a = x then P.pmf a else 0 else 0 := by
    have h1 :
        (∑ xa : β × α,
            if D xa.1 = true then if f xa.2 = xa.1 then P.pmf xa.2 else 0 else 0)
          =
        ∑ x : β, ∑ a : α, if D x = true then if f a = x then P.pmf a else 0 else 0 := by
      simpa using
        (Fintype.sum_prod_type (fun xa : β × α =>
          if D xa.1 = true then if f xa.2 = xa.1 then P.pmf xa.2 else 0 else 0))
    have h2 :
        (∑ xa : β × α,
            if D xa.1 = true then if f xa.2 = xa.1 then P.pmf xa.2 else 0 else 0)
          =
        ∑ a : α, ∑ x : β, if D x = true then if f a = x then P.pmf a else 0 else 0 := by
      simpa using
        (Fintype.sum_prod_type_right (fun xa : β × α =>
          if D xa.1 = true then if f xa.2 = xa.1 then P.pmf xa.2 else 0 else 0))
    exact h1.symm.trans h2
  -- Evaluate the inner sum: only `x = f a` can contribute.
  have hinner :
      ∀ a : α,
        (∑ x : β, if D x = true then if f a = x then P.pmf a else 0 else 0)
          = if D (f a) = true then P.pmf a else 0 := by
    intro a
    have hfun :
        (fun x : β => if D x = true then if f a = x then P.pmf a else 0 else 0)
          =
        (fun x : β => if f a = x then if D x = true then P.pmf a else 0 else 0) := by
      funext x
      by_cases hx : f a = x <;> simp [hx]
    have hsum_rewrite :
        (∑ x : β, if D x = true then if f a = x then P.pmf a else 0 else 0)
          =
        ∑ x : β, if f a = x then if D x = true then P.pmf a else 0 else 0 := by
      simpa using congrArg (fun g : β → ℝ => (∑ x : β, g x)) hfun
    rw [hsum_rewrite]
    simp
  calc
    (∑ x : β, if D x = true then ∑ a : α, if f a = x then P.pmf a else 0 else 0)
        = ∑ x : β, ∑ a : α, if D x = true then if f a = x then P.pmf a else 0 else 0 := hpull
    _ = ∑ a : α, ∑ x : β, if D x = true then if f a = x then P.pmf a else 0 else 0 := hswap
    _ = ∑ a : α, if D (f a) = true then P.pmf a else 0 := by
          refine Fintype.sum_congr _ _ ?_
          intro a
          exact hinner a

theorem probEvent_goodKey_le_probTrue_prf (Q : FinDist (BitStr m × BitStr k)) (t : Nat)
    (hQ : Q.Pos) (hmt : 0 < m + t) :
    probEvent (Epiplexity.FinDist.uniform (α := BitStr m))
        (fun key =>
          (FinDist.klDiv (prfPairDist (m := m) (k := k) F key) Q) / Real.log 2 ≤ t)
      ≤
      probTrue (PRFOracleDist (m := m) (k := k) F)
        (heavySetMajorityDistinguisher (m := m) (k := k) Q t).run := by
  classical
  -- If a key is "good" (KL ≤ t), Lemma 22 forces at least half the mass in the heavy set,
  -- hence the majority distinguisher outputs `true`.
  let Ukey : FinDist (BitStr m) := Epiplexity.FinDist.uniform (α := BitStr m)
  have hgood_imp :
      ∀ key : BitStr m,
        ((FinDist.klDiv (prfPairDist (m := m) (k := k) F key) Q) / Real.log 2 ≤ t) →
          (heavySetMajorityDistinguisher (m := m) (k := k) Q t).run (F key) = true := by
    intro key hKL
    have hH : Info.entropyBits (prfPairDist (m := m) (k := k) F key) = m :=
      entropyBits_prfPairDist (m := m) (k := k) (F := F) (K := key)
    -- Lemma 22 gives heavy-set probability ≥ 1/2 under `P_K`.
    have hhalf :
        probEvent (prfPairDist (m := m) (k := k) F key)
            (fun z => heavyThreshold m t ≤ Q.pmf z) ≥ (1 / 2 : ℝ) :=
      HeavySet.lemma22_prob_heavySet_ge_half (P := prfPairDist (m := m) (k := k) F key) (Q := Q)
        (hq := hQ) (m := m) (t := t) hH hKL hmt
    -- Rewrite `probEvent P_K` as the `heavyFraction` of the oracle `F key`.
    have hrewrite :
        probEvent (prfPairDist (m := m) (k := k) F key)
            (fun z => heavyThreshold m t ≤ Q.pmf z)
          = heavyFraction (m := m) (k := k) Q t (F key) := by
      -- Expand `P_K` and sum over `(x,y)`.
      unfold heavyFraction UX prfPairDist
      classical
      -- `probEvent` over `P_K` collapses to a sum over `x` only.
      unfold probEvent
      -- Swap sums over `x,y`.
      have hswap :
          (∑ z : BitStr m × BitStr k,
              if heavyThreshold m t ≤ Q.pmf z then
                (if z.2 = F key z.1 then 1 / (Fintype.card (BitStr m) : ℝ) else 0)
              else 0)
            =
            ∑ x : BitStr m, ∑ y : BitStr k,
              if heavyThreshold m t ≤ Q.pmf (x, y) then
                (if y = F key x then 1 / (Fintype.card (BitStr m) : ℝ) else 0)
              else 0 := by
          simpa using (Fintype.sum_prod_type
            (fun z : BitStr m × BitStr k =>
              if heavyThreshold m t ≤ Q.pmf z then
                (if z.2 = F key z.1 then 1 / (Fintype.card (BitStr m) : ℝ) else 0)
              else 0))
      -- Inner sum reduces to the single `y = F key x`.
      have hinner : ∀ x : BitStr m,
          (∑ y : BitStr k,
              if heavyThreshold m t ≤ Q.pmf (x, y) then
                (if y = F key x then 1 / (Fintype.card (BitStr m) : ℝ) else 0)
              else 0)
            =
            if heavyThreshold m t ≤ Q.pmf (x, F key x) then 1 / (Fintype.card (BitStr m) : ℝ) else 0 := by
        intro x
        classical
        have hfun :
            (fun y : BitStr k =>
                if heavyThreshold m t ≤ Q.pmf (x, y) then
                  (if y = F key x then 1 / (Fintype.card (BitStr m) : ℝ) else 0)
                else 0)
              =
            (fun y : BitStr k =>
                if y = F key x then
                  (if heavyThreshold m t ≤ Q.pmf (x, y) then 1 / (Fintype.card (BitStr m) : ℝ) else 0)
                else 0) := by
          funext y
          by_cases hy : y = F key x <;> simp [hy]
        have hsum_rewrite :
            (∑ y : BitStr k,
                if heavyThreshold m t ≤ Q.pmf (x, y) then
                  (if y = F key x then 1 / (Fintype.card (BitStr m) : ℝ) else 0)
                else 0)
              =
            ∑ y : BitStr k,
                if y = F key x then
                  (if heavyThreshold m t ≤ Q.pmf (x, y) then 1 / (Fintype.card (BitStr m) : ℝ) else 0)
                else 0 := by
          simpa using congrArg (fun g : BitStr k → ℝ => (∑ y : BitStr k, g y)) hfun
        -- Only the term `y = F key x` can contribute.
        -- (When `y ≠ F key x`, the inner `if` forces `0`.)
        rw [hsum_rewrite]
        simp
      -- Now match the definition of `probEvent (UX m)`.
      have hUx : ∀ x : BitStr m, (UX (m := m)).pmf x = 1 / (Fintype.card (BitStr m) : ℝ) := by
        intro x
        simp [UX, Epiplexity.FinDist.uniform]
      calc
        (∑ z : BitStr m × BitStr k,
            if heavyThreshold m t ≤ Q.pmf z then
              (if z.2 = F key z.1 then 1 / (Fintype.card (BitStr m) : ℝ) else 0)
            else 0)
            = ∑ x : BitStr m, ∑ y : BitStr k,
                if heavyThreshold m t ≤ Q.pmf (x, y) then
                  (if y = F key x then 1 / (Fintype.card (BitStr m) : ℝ) else 0)
                else 0 := hswap
        _ = ∑ x : BitStr m,
              if heavyThreshold m t ≤ Q.pmf (x, F key x) then 1 / (Fintype.card (BitStr m) : ℝ) else 0 := by
              refine Fintype.sum_congr _ _ ?_
              intro x
              exact hinner x
        _ = ∑ x : BitStr m,
              if heavyThreshold m t ≤ Q.pmf (x, F key x) then (UX (m := m)).pmf x else 0 := by
              simp [hUx]
    -- Conclude the majority test is true.
    have : (1 / 2 : ℝ) ≤ heavyFraction (m := m) (k := k) Q t (F key) := by
      simpa [hrewrite] using hhalf
    exact (heavySetMajorityDistinguisher_spec (m := m) (k := k) (Q := Q) (t := t) (O := F key)).2 this
  -- Compare event probabilities: the good-key event is contained in `{key | D(F key)=true}`.
  have hmono :
      probEvent Ukey
          (fun key =>
            (FinDist.klDiv (prfPairDist (m := m) (k := k) F key) Q) / Real.log 2 ≤ t)
        ≤
        probEvent Ukey (fun key => (heavySetMajorityDistinguisher (m := m) (k := k) Q t).run (F key) = true) := by
    refine probEvent_mono (P := Ukey)
      (E := fun key => (FinDist.klDiv (prfPairDist (m := m) (k := k) F key) Q) / Real.log 2 ≤ t)
      (F := fun key => (heavySetMajorityDistinguisher (m := m) (k := k) Q t).run (F key) = true)
      (fun key h => hgood_imp key h)
  -- Rewrite the RHS as `probTrue (PRFOracleDist F) D` via the pushforward property.
  have hprobTrue_eq :
      probEvent Ukey (fun key => (heavySetMajorityDistinguisher (m := m) (k := k) Q t).run (F key) = true)
        =
      probTrue (PRFOracleDist (m := m) (k := k) F) (heavySetMajorityDistinguisher (m := m) (k := k) Q t).run := by
    symm
    simpa [PRFOracleDist, Ukey] using
      (probTrue_map_eq_probEvent (P := Ukey) (f := fun key : BitStr m => F key)
        (D := (heavySetMajorityDistinguisher (m := m) (k := k) Q t).run))
  simpa [hprobTrue_eq] using hmono

/-! ### Random-oracle bound for the majority distinguisher -/

theorem probTrue_eq_probEvent {α : Type u} [Fintype α] (P : FinDist α) (D : α → Bool) :
    probTrue P D = probEvent P (fun a => D a = true) := by
  classical
  unfold probTrue probEvent
  refine Finset.sum_congr rfl ?_
  intro a _
  cases h : D a <;> simp [h]

theorem probEvent_map_eq {α β : Type u} [Fintype α] [Fintype β]
    (P : FinDist α) (f : α → β) (E : β → Prop) [DecidablePred E] :
    probEvent (FinDist.map f P) E = probEvent P (fun a => E (f a)) := by
  classical
  unfold probEvent FinDist.map
  -- Pull the `E x` test inside the inner sum.
  have hpull :
      (∑ x : β, if E x then ∑ a : α, if f a = x then P.pmf a else 0 else 0)
        =
      ∑ x : β, ∑ a : α, if E x then if f a = x then P.pmf a else 0 else 0 := by
    refine Fintype.sum_congr _ _ ?_
    intro x
    by_cases hx : E x <;> simp [hx]
  -- Swap the order of summation (`x` then `a`).
  have hswap :
      (∑ x : β, ∑ a : α, if E x then if f a = x then P.pmf a else 0 else 0)
        =
      ∑ a : α, ∑ x : β, if E x then if f a = x then P.pmf a else 0 else 0 := by
    have h1 :
        (∑ xa : β × α,
            if E xa.1 then if f xa.2 = xa.1 then P.pmf xa.2 else 0 else 0)
          =
        ∑ x : β, ∑ a : α, if E x then if f a = x then P.pmf a else 0 else 0 := by
      simpa using
        (Fintype.sum_prod_type (fun xa : β × α =>
          if E xa.1 then if f xa.2 = xa.1 then P.pmf xa.2 else 0 else 0))
    have h2 :
        (∑ xa : β × α,
            if E xa.1 then if f xa.2 = xa.1 then P.pmf xa.2 else 0 else 0)
          =
        ∑ a : α, ∑ x : β, if E x then if f a = x then P.pmf a else 0 else 0 := by
      simpa using
        (Fintype.sum_prod_type_right (fun xa : β × α =>
          if E xa.1 then if f xa.2 = xa.1 then P.pmf xa.2 else 0 else 0))
    exact h1.symm.trans h2
  -- Evaluate the inner sum: only `x = f a` can contribute.
  have hinner :
      ∀ a : α,
        (∑ x : β, if E x then if f a = x then P.pmf a else 0 else 0)
          = if E (f a) then P.pmf a else 0 := by
    intro a
    have hfun :
        (fun x : β => if E x then if f a = x then P.pmf a else 0 else 0)
          =
        (fun x : β => if f a = x then if E x then P.pmf a else 0 else 0) := by
      funext x
      by_cases hx : f a = x <;> simp [hx]
    have hsum_rewrite :
        (∑ x : β, if E x then if f a = x then P.pmf a else 0 else 0)
          =
        ∑ x : β, if f a = x then if E x then P.pmf a else 0 else 0 := by
      simpa using congrArg (fun g : β → ℝ => (∑ x : β, g x)) hfun
    rw [hsum_rewrite]
    simp
  calc
    (∑ x : β, if E x then ∑ a : α, if f a = x then P.pmf a else 0 else 0)
        = ∑ x : β, ∑ a : α, if E x then if f a = x then P.pmf a else 0 else 0 := hpull
    _ = ∑ a : α, ∑ x : β, if E x then if f a = x then P.pmf a else 0 else 0 := hswap
    _ = ∑ a : α, if E (f a) then P.pmf a else 0 := by
          refine Fintype.sum_congr _ _ ?_
          intro a
          exact hinner a

theorem heavyFraction_nonneg (Q : FinDist (BitStr m × BitStr k)) (t : Nat) (O : BitStr m → BitStr k) :
    0 ≤ heavyFraction (m := m) (k := k) Q t O := by
  classical
  unfold heavyFraction probEvent
  refine Finset.sum_nonneg ?_
  intro x _
  by_cases hx : heavyThreshold m t ≤ Q.pmf (x, O x) <;> simp [hx, (UX (m := m)).nonneg x]

theorem expect_heavyFraction_eq_probEvent_uniformPair (Q : FinDist (BitStr m × BitStr k)) (t : Nat) :
    (∑ O : BitStr m → BitStr k,
        (UO (m := m) (k := k)).pmf O * heavyFraction (m := m) (k := k) Q t O)
      =
      probEvent (Epiplexity.FinDist.uniform (α := BitStr m × BitStr k))
        (fun z => heavyThreshold m t ≤ Q.pmf z) := by
  classical
  -- Expand the expectation and swap sums (`O` outside, then `x`).
  unfold heavyFraction probEvent
  have hmul_sum :
      (∑ O : BitStr m → BitStr k,
          (UO (m := m) (k := k)).pmf O *
            (∑ x : BitStr m, if heavyThreshold m t ≤ Q.pmf (x, O x) then (UX (m := m)).pmf x else 0))
        =
      ∑ O : BitStr m → BitStr k, ∑ x : BitStr m,
          (UO (m := m) (k := k)).pmf O *
            (if heavyThreshold m t ≤ Q.pmf (x, O x) then (UX (m := m)).pmf x else 0) := by
    refine Fintype.sum_congr _ _ ?_
    intro O
    simp [Finset.mul_sum]
  rw [hmul_sum]
  have hswap :
      (∑ O : BitStr m → BitStr k, ∑ x : BitStr m,
          (UO (m := m) (k := k)).pmf O *
            (if heavyThreshold m t ≤ Q.pmf (x, O x) then (UX (m := m)).pmf x else 0))
        =
      ∑ x : BitStr m, ∑ O : BitStr m → BitStr k,
          (UO (m := m) (k := k)).pmf O *
            (if heavyThreshold m t ≤ Q.pmf (x, O x) then (UX (m := m)).pmf x else 0) := by
    -- Both sides are sums over `((BitStr m → BitStr k) × BitStr m)`.
    have h1 :
        (∑ Ox : (BitStr m → BitStr k) × BitStr m,
            (UO (m := m) (k := k)).pmf Ox.1 *
              (if heavyThreshold m t ≤ Q.pmf (Ox.2, Ox.1 Ox.2) then (UX (m := m)).pmf Ox.2 else 0))
          =
        ∑ O : BitStr m → BitStr k, ∑ x : BitStr m,
          (UO (m := m) (k := k)).pmf O *
            (if heavyThreshold m t ≤ Q.pmf (x, O x) then (UX (m := m)).pmf x else 0) := by
      simpa using (Fintype.sum_prod_type (fun Ox : (BitStr m → BitStr k) × BitStr m =>
        (UO (m := m) (k := k)).pmf Ox.1 *
          (if heavyThreshold m t ≤ Q.pmf (Ox.2, Ox.1 Ox.2) then (UX (m := m)).pmf Ox.2 else 0)))
    have h2 :
        (∑ Ox : (BitStr m → BitStr k) × BitStr m,
            (UO (m := m) (k := k)).pmf Ox.1 *
              (if heavyThreshold m t ≤ Q.pmf (Ox.2, Ox.1 Ox.2) then (UX (m := m)).pmf Ox.2 else 0))
          =
        ∑ x : BitStr m, ∑ O : BitStr m → BitStr k,
          (UO (m := m) (k := k)).pmf O *
            (if heavyThreshold m t ≤ Q.pmf (x, O x) then (UX (m := m)).pmf x else 0) := by
      simpa using (Fintype.sum_prod_type_right (fun Ox : (BitStr m → BitStr k) × BitStr m =>
        (UO (m := m) (k := k)).pmf Ox.1 *
          (if heavyThreshold m t ≤ Q.pmf (Ox.2, Ox.1 Ox.2) then (UX (m := m)).pmf Ox.2 else 0)))
    exact h1.symm.trans h2
  rw [hswap]
  -- Reduce the inner `O`-sum using evaluation-uniformity.
  have hinner :
      ∀ x : BitStr m,
        (∑ O : BitStr m → BitStr k,
            (UO (m := m) (k := k)).pmf O *
              (if heavyThreshold m t ≤ Q.pmf (x, O x) then (UX (m := m)).pmf x else 0))
          =
        (UX (m := m)).pmf x *
          probEvent (UY (k := k)) (fun y => heavyThreshold m t ≤ Q.pmf (x, y)) := by
    intro x
    -- Pull out the constant factor `(UX).pmf x`.
    have hfactor :
        (∑ O : BitStr m → BitStr k,
            (UO (m := m) (k := k)).pmf O *
              (if heavyThreshold m t ≤ Q.pmf (x, O x) then (UX (m := m)).pmf x else 0))
          =
        (UX (m := m)).pmf x *
          (∑ O : BitStr m → BitStr k,
              if heavyThreshold m t ≤ Q.pmf (x, O x) then (UO (m := m) (k := k)).pmf O else 0) := by
      calc
        (∑ O : BitStr m → BitStr k,
            (UO (m := m) (k := k)).pmf O *
              (if heavyThreshold m t ≤ Q.pmf (x, O x) then (UX (m := m)).pmf x else 0))
            =
            ∑ O : BitStr m → BitStr k,
              if heavyThreshold m t ≤ Q.pmf (x, O x) then
                (UX (m := m)).pmf x * (UO (m := m) (k := k)).pmf O
              else 0 := by
                refine Fintype.sum_congr _ _ ?_
                intro O
                by_cases hO : heavyThreshold m t ≤ Q.pmf (x, O x) <;> simp [hO, mul_comm]
        _ = (UX (m := m)).pmf x *
              (∑ O : BitStr m → BitStr k,
                if heavyThreshold m t ≤ Q.pmf (x, O x) then (UO (m := m) (k := k)).pmf O else 0) := by
              simp [Finset.mul_sum]
    -- Identify the inner sum as an event probability under `UY`.
    have hprob :
        (∑ O : BitStr m → BitStr k,
            if heavyThreshold m t ≤ Q.pmf (x, O x) then (UO (m := m) (k := k)).pmf O else 0)
          =
        probEvent (UY (k := k)) (fun y => heavyThreshold m t ≤ Q.pmf (x, y)) := by
      -- Pushforward along evaluation, then use `uniform_eval_apply_eq_uniform`.
      have hpush :
          probEvent (UO (m := m) (k := k))
              (fun O : BitStr m → BitStr k => heavyThreshold m t ≤ Q.pmf (x, O x))
            =
          probEvent (FinDist.map (fun O : BitStr m → BitStr k => O x) (UO (m := m) (k := k)))
              (fun y => heavyThreshold m t ≤ Q.pmf (x, y)) := by
        -- `probEvent_map_eq` gives the reverse direction, so we use symmetry.
        simpa using (probEvent_map_eq (P := UO (m := m) (k := k))
          (f := fun O : BitStr m → BitStr k => O x)
          (E := fun y => heavyThreshold m t ≤ Q.pmf (x, y))).symm
      have hev : FinDist.map (fun O : BitStr m → BitStr k => O x) (UO (m := m) (k := k)) = UY (k := k) :=
        uniform_eval_apply_eq_uniform (m := m) (k := k) (x := x)
      -- Rewrite the event probability under `UY`.
      calc
        (∑ O : BitStr m → BitStr k,
            if heavyThreshold m t ≤ Q.pmf (x, O x) then (UO (m := m) (k := k)).pmf O else 0)
            =
          probEvent (UO (m := m) (k := k))
            (fun O : BitStr m → BitStr k => heavyThreshold m t ≤ Q.pmf (x, O x)) := by
              rfl
        _ =
          probEvent (FinDist.map (fun O : BitStr m → BitStr k => O x) (UO (m := m) (k := k)))
            (fun y => heavyThreshold m t ≤ Q.pmf (x, y)) := hpush
        _ =
          probEvent (UY (k := k)) (fun y => heavyThreshold m t ≤ Q.pmf (x, y)) := by
            simp [hev]
    -- Conclude.
    simpa [hprob] using hfactor
  -- Use `hinner` and identify the uniform distribution on pairs.
  have hUxy :
      ∀ z : BitStr m × BitStr k,
        (Epiplexity.FinDist.uniform (α := BitStr m × BitStr k)).pmf z =
          (UX (m := m)).pmf z.1 * (UY (k := k)).pmf z.2 := by
    intro z
    simp [UX, UY, Epiplexity.FinDist.uniform, Fintype.card_prod, div_eq_mul_inv, mul_comm]
  -- Expand the RHS `probEvent` as a sum over `x,y`.
  calc
    (∑ x : BitStr m, ∑ O : BitStr m → BitStr k,
        (UO (m := m) (k := k)).pmf O *
          (if heavyThreshold m t ≤ Q.pmf (x, O x) then (UX (m := m)).pmf x else 0))
        = ∑ x : BitStr m, (UX (m := m)).pmf x *
            probEvent (UY (k := k)) (fun y => heavyThreshold m t ≤ Q.pmf (x, y)) := by
            refine Fintype.sum_congr _ _ ?_
            intro x
            exact hinner x
    _ = ∑ x : BitStr m, ∑ y : BitStr k,
          if heavyThreshold m t ≤ Q.pmf (x, y) then
            (UX (m := m)).pmf x * (UY (k := k)).pmf y
          else 0 := by
            refine Fintype.sum_congr _ _ ?_
            intro x
            unfold probEvent
            simp [Finset.mul_sum, mul_comm]
    _ = ∑ z : BitStr m × BitStr k,
          if heavyThreshold m t ≤ Q.pmf z then
            (Epiplexity.FinDist.uniform (α := BitStr m × BitStr k)).pmf z
          else 0 := by
            -- Convert the double sum to a sum over the product type.
            have :
                (∑ z : BitStr m × BitStr k,
                    if heavyThreshold m t ≤ Q.pmf z then
                      (UX (m := m)).pmf z.1 * (UY (k := k)).pmf z.2
                    else 0)
                  =
                ∑ x : BitStr m, ∑ y : BitStr k,
                    if heavyThreshold m t ≤ Q.pmf (x, y) then
                      (UX (m := m)).pmf x * (UY (k := k)).pmf y
                    else 0 := by
              simpa using (Fintype.sum_prod_type
                (fun z : BitStr m × BitStr k =>
                  if heavyThreshold m t ≤ Q.pmf z then
                    (UX (m := m)).pmf z.1 * (UY (k := k)).pmf z.2
                  else 0))
            rw [this.symm]
            refine Fintype.sum_congr _ _ ?_
            intro z
            by_cases hz : heavyThreshold m t ≤ Q.pmf z <;>
              simp [hz, UX, UY, Epiplexity.FinDist.uniform, Fintype.card_prod, div_eq_mul_inv, mul_comm]

theorem probTrue_uniformOracle_majority_le (Q : FinDist (BitStr m × BitStr k)) (t : Nat) :
    probTrue (UO (m := m) (k := k)) (heavySetMajorityDistinguisher (m := m) (k := k) Q t).run ≤
      2 * (((2 : ℝ) ^ (2 * (m + t))) / (Fintype.card (BitStr m × BitStr k) : ℝ)) := by
  classical
  -- Rewrite `probTrue` as an event probability for `heavyFraction ≥ 1/2`.
  have hprobEvent :
      probTrue (UO (m := m) (k := k)) (heavySetMajorityDistinguisher (m := m) (k := k) Q t).run
        =
      probEvent (UO (m := m) (k := k))
        (fun O => (1 / 2 : ℝ) ≤ heavyFraction (m := m) (k := k) Q t O) := by
    -- First convert `probTrue` to `probEvent` for the Boolean predicate `run O = true`.
    have h0 :
        probTrue (UO (m := m) (k := k)) (heavySetMajorityDistinguisher (m := m) (k := k) Q t).run
          =
        probEvent (UO (m := m) (k := k))
          (fun O => (heavySetMajorityDistinguisher (m := m) (k := k) Q t).run O = true) := by
      simpa using
        (probTrue_eq_probEvent (P := UO (m := m) (k := k))
          (D := (heavySetMajorityDistinguisher (m := m) (k := k) Q t).run))
    -- Then rewrite the event pointwise using the iff-spec.
    rw [h0]
    unfold probEvent
    refine Finset.sum_congr rfl ?_
    intro O _
    by_cases hO : (1 / 2 : ℝ) ≤ heavyFraction (m := m) (k := k) Q t O
    · have hrun :
        (heavySetMajorityDistinguisher (m := m) (k := k) Q t).run O = true :=
          (heavySetMajorityDistinguisher_spec (m := m) (k := k) (Q := Q) (t := t) (O := O)).2 hO
      have hO' : (2⁻¹ : ℝ) ≤ heavyFraction (m := m) (k := k) Q t O := by
        simpa [one_div] using hO
      simp [hO', hrun]
    · have hrun :
        (heavySetMajorityDistinguisher (m := m) (k := k) Q t).run O ≠ true := by
          intro hEq
          have : (1 / 2 : ℝ) ≤ heavyFraction (m := m) (k := k) Q t O :=
            (heavySetMajorityDistinguisher_spec (m := m) (k := k) (Q := Q) (t := t) (O := O)).1 hEq
          exact hO this
      have hO' : ¬(2⁻¹ : ℝ) ≤ heavyFraction (m := m) (k := k) Q t O := by
        -- Convert `¬(1/2 ≤ …)` to the syntactic form used by simp.
        simpa [one_div] using hO
      simp [hO', hrun]
  -- Markov bound.
  have hmarkov :
      probEvent (UO (m := m) (k := k))
          (fun O => (1 / 2 : ℝ) ≤ heavyFraction (m := m) (k := k) Q t O)
        ≤
      (∑ O : BitStr m → BitStr k,
          (UO (m := m) (k := k)).pmf O * heavyFraction (m := m) (k := k) Q t O) / (1 / 2 : ℝ) :=
    FinDist.markov (P := UO (m := m) (k := k))
      (f := fun O => heavyFraction (m := m) (k := k) Q t O)
      (hf := fun O => heavyFraction_nonneg (m := m) (k := k) (Q := Q) (t := t) O)
      (c := (1 / 2 : ℝ)) (by norm_num)
  have hexpect :
      (∑ O : BitStr m → BitStr k,
          (UO (m := m) (k := k)).pmf O * heavyFraction (m := m) (k := k) Q t O)
        =
      probEvent (Epiplexity.FinDist.uniform (α := BitStr m × BitStr k))
        (fun z => heavyThreshold m t ≤ Q.pmf z) :=
    expect_heavyFraction_eq_probEvent_uniformPair (m := m) (k := k) (Q := Q) (t := t)
  -- Bound the expectation using Lemma 23.
  have hlemma23 :
      probEvent (Epiplexity.FinDist.uniform (α := BitStr m × BitStr k))
          (fun z => heavyThreshold m t ≤ Q.pmf z)
        ≤
      ((2 : ℝ) ^ (2 * (m + t))) / (Fintype.card (BitStr m × BitStr k) : ℝ) := by
    -- Use `prob_heavySet` + Lemma 23 on `γ := BitStr m × BitStr k`.
    let U : FinDist (BitStr m × BitStr k) := Epiplexity.FinDist.uniform (α := BitStr m × BitStr k)
    have hprob :
        (heavySet (α := BitStr m × BitStr k) Q m t).sum (fun z => U.pmf z) =
          probEvent U (fun z => heavyThreshold m t ≤ Q.pmf z) := by
      simpa [U] using
        (HeavySet.prob_heavySet (P := U) (Q := Q) (m := m) (t := t))
    have hbound :
        (heavySet (α := BitStr m × BitStr k) Q m t).sum (fun z => U.pmf z) ≤
          ((2 : ℝ) ^ (2 * (m + t))) / (Fintype.card (BitStr m × BitStr k) : ℝ) := by
      simpa [U] using
        (HeavySet.lemma23_prob_uniform_heavySet_le_general
          (γ := BitStr m × BitStr k) (m := m) (t := t) (Q := Q))
    -- Rewrite the `probEvent` via `hprob` and apply the heavy-set bound.
    have : probEvent U (fun z => heavyThreshold m t ≤ Q.pmf z) ≤
        ((2 : ℝ) ^ (2 * (m + t))) / (Fintype.card (BitStr m × BitStr k) : ℝ) := by
      simpa [hprob] using hbound
    simpa [U] using this
  -- Combine: `probTrue = probEvent` and Markov + Lemma 23.
  rw [hprobEvent]
  have hmarkov' :
      probEvent (UO (m := m) (k := k))
          (fun O => (1 / 2 : ℝ) ≤ heavyFraction (m := m) (k := k) Q t O)
        ≤
      (probEvent (Epiplexity.FinDist.uniform (α := BitStr m × BitStr k))
        (fun z => heavyThreshold m t ≤ Q.pmf z)) / (1 / 2 : ℝ) := by
    simpa [hexpect] using hmarkov
  -- Replace `/ (1/2)` by multiplication by `2`, and apply Lemma 23.
  have hscale :
      (probEvent (Epiplexity.FinDist.uniform (α := BitStr m × BitStr k))
            (fun z => heavyThreshold m t ≤ Q.pmf z)) / (1 / 2 : ℝ)
        ≤
        2 * (((2 : ℝ) ^ (2 * (m + t))) / (Fintype.card (BitStr m × BitStr k) : ℝ)) := by
    have hmul :
        (2 : ℝ) *
            probEvent (Epiplexity.FinDist.uniform (α := BitStr m × BitStr k))
              (fun z => heavyThreshold m t ≤ Q.pmf z)
          ≤
        (2 : ℝ) * (((2 : ℝ) ^ (2 * (m + t))) / (Fintype.card (BitStr m × BitStr k) : ℝ)) := by
      have h2 : (0 : ℝ) ≤ 2 := by norm_num
      exact mul_le_mul_of_nonneg_left hlemma23 h2
    -- `a / (1/2) = 2 * a`.
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  exact le_trans hmarkov' hscale

/-! ### Theorem 24 (finite-family form): existence of a hard key -/

theorem probEvent_goodKey_le_bound (Q : FinDist (BitStr m × BitStr k)) (t : Nat)
    (hQ : Q.Pos) (hmt : 0 < m + t)
    (hPRF : PRFSecure (k := m) (n := m) (m := k) T F ε) :
    probEvent (Epiplexity.FinDist.uniform (α := BitStr m))
        (fun key =>
          (FinDist.klDiv (prfPairDist (m := m) (k := k) F key) Q) / Real.log 2 ≤ t)
      ≤
      (ε m) + 2 * (((2 : ℝ) ^ (2 * (m + t))) / (Fintype.card (BitStr m × BitStr k) : ℝ)) := by
  classical
  -- Step 1: reduce to `probTrue` on the PRF oracle distribution.
  have h1 :
      probEvent (Epiplexity.FinDist.uniform (α := BitStr m))
          (fun key =>
            (FinDist.klDiv (prfPairDist (m := m) (k := k) F key) Q) / Real.log 2 ≤ t)
        ≤
        probTrue (PRFOracleDist (m := m) (k := k) F)
          (heavySetMajorityDistinguisher (m := m) (k := k) Q t).run :=
    probEvent_goodKey_le_probTrue_prf (m := m) (k := k) (F := F) (Q := Q) (t := t) hQ hmt
  -- Step 2: PRF security bounds `probTrue` by the uniform-oracle probability plus `ε(m)`.
  have hDtime : (heavySetMajorityDistinguisher (m := m) (k := k) Q t).runtime ≤ T := by
    simp [heavySetMajorityDistinguisher]
  have hAdv :
      advantage
          (PRFOracleDist (m := m) (k := k) F)
          (UO (m := m) (k := k))
          (heavySetMajorityDistinguisher (m := m) (k := k) Q t).run
        ≤ ε m := by
    -- Unfold `PRFOracleDist`/`UO` to match `PRFSecure`.
    simpa [PRFOracleDist, UO] using hPRF (heavySetMajorityDistinguisher (m := m) (k := k) Q t) hDtime
  have hAbs :
      |probTrue (PRFOracleDist (m := m) (k := k) F) (heavySetMajorityDistinguisher (m := m) (k := k) Q t).run -
          probTrue (UO (m := m) (k := k)) (heavySetMajorityDistinguisher (m := m) (k := k) Q t).run|
        ≤ ε m := by
    simpa [advantage] using hAdv
  have hDiff :
      probTrue (PRFOracleDist (m := m) (k := k) F) (heavySetMajorityDistinguisher (m := m) (k := k) Q t).run -
          probTrue (UO (m := m) (k := k)) (heavySetMajorityDistinguisher (m := m) (k := k) Q t).run
        ≤ ε m :=
    le_trans (le_abs_self _) hAbs
  have hPRF_le :
      probTrue (PRFOracleDist (m := m) (k := k) F) (heavySetMajorityDistinguisher (m := m) (k := k) Q t).run
        ≤ probTrue (UO (m := m) (k := k)) (heavySetMajorityDistinguisher (m := m) (k := k) Q t).run + ε m := by
    have : probTrue (PRFOracleDist (m := m) (k := k) F) (heavySetMajorityDistinguisher (m := m) (k := k) Q t).run
        ≤ ε m +
          probTrue (UO (m := m) (k := k)) (heavySetMajorityDistinguisher (m := m) (k := k) Q t).run :=
      (sub_le_iff_le_add).1 hDiff
    simpa [add_comm, add_left_comm, add_assoc] using this
  -- Step 3: bound the uniform-oracle probability via Lemma 23 + Markov.
  have hUO_le :
      probTrue (UO (m := m) (k := k)) (heavySetMajorityDistinguisher (m := m) (k := k) Q t).run
        ≤ 2 * (((2 : ℝ) ^ (2 * (m + t))) / (Fintype.card (BitStr m × BitStr k) : ℝ)) :=
    probTrue_uniformOracle_majority_le (m := m) (k := k) (Q := Q) (t := t)
  -- Combine all bounds.
  have h2 :
      probEvent (Epiplexity.FinDist.uniform (α := BitStr m))
          (fun key =>
            (FinDist.klDiv (prfPairDist (m := m) (k := k) F key) Q) / Real.log 2 ≤ t)
        ≤
        probTrue (UO (m := m) (k := k)) (heavySetMajorityDistinguisher (m := m) (k := k) Q t).run + ε m :=
    le_trans h1 hPRF_le
  have h3 :
      probTrue (UO (m := m) (k := k)) (heavySetMajorityDistinguisher (m := m) (k := k) Q t).run + ε m
        ≤ (ε m) + 2 * (((2 : ℝ) ^ (2 * (m + t))) / (Fintype.card (BitStr m × BitStr k) : ℝ)) := by
    linarith [hUO_le]
  exact le_trans h2 h3

theorem probEvent_exists_le_sum {α : Type u} {ι : Type v} [Fintype α] [Fintype ι]
    (P : FinDist α) (E : ι → α → Prop) [∀ i, DecidablePred (E i)] :
    probEvent P (fun a => ∃ i, E i a) ≤ ∑ i : ι, probEvent P (E i) := by
  classical
  -- Expand everything and swap the `ι`/`α` sums on the RHS.
  unfold probEvent
  have hswap :
      (∑ i : ι, ∑ a : α, if E i a then P.pmf a else 0)
        = ∑ a : α, ∑ i : ι, if E i a then P.pmf a else 0 := by
    have h1 :
        (∑ ia : ι × α, if E ia.1 ia.2 then P.pmf ia.2 else 0)
          = ∑ i : ι, ∑ a : α, if E i a then P.pmf a else 0 := by
      simpa using
        (Fintype.sum_prod_type (fun ia : ι × α => if E ia.1 ia.2 then P.pmf ia.2 else 0))
    have h2 :
        (∑ ia : ι × α, if E ia.1 ia.2 then P.pmf ia.2 else 0)
          = ∑ a : α, ∑ i : ι, if E i a then P.pmf a else 0 := by
      simpa using
        (Fintype.sum_prod_type_right (fun ia : ι × α => if E ia.1 ia.2 then P.pmf ia.2 else 0))
    exact h1.symm.trans h2
  have hpoint :
      ∀ a : α,
        (if (∃ i : ι, E i a) then P.pmf a else 0) ≤
          ∑ i : ι, if E i a then P.pmf a else 0 := by
    intro a
    by_cases ha : (∃ i : ι, E i a)
    · rcases ha with ⟨i0, hi0⟩
      have hnonneg : ∀ i : ι, 0 ≤ (if E i a then P.pmf a else 0) := by
        intro i
        by_cases hi : E i a <;> simp [hi, P.nonneg a]
      have hle :
          (if E i0 a then P.pmf a else 0) ≤ ∑ i : ι, if E i a then P.pmf a else 0 := by
        simpa using
          (Finset.single_le_sum (s := (Finset.univ : Finset ι)) (a := i0)
            (f := fun i : ι => if E i a then P.pmf a else 0)
            (fun i _ => hnonneg i)
            (by simp))
      have hfi0 : (if E i0 a then P.pmf a else 0) = P.pmf a := by simp [hi0]
      -- In this branch, `∃ i, E i a` holds, so the LHS is `P.pmf a`.
      have : (if (∃ i : ι, E i a) then P.pmf a else 0) ≤
          ∑ i : ι, if E i a then P.pmf a else 0 := by
        have ha' : (∃ i : ι, E i a) := ⟨i0, hi0⟩
        simpa [ha', hfi0] using hle
      exact this
    · have : (if (∃ i : ι, E i a) then P.pmf a else 0) = 0 := by simp [ha]
      have hnonneg_sum : 0 ≤ ∑ i : ι, if E i a then P.pmf a else 0 := by
        refine Finset.sum_nonneg ?_
        intro i _
        by_cases hi : E i a <;> simp [hi, P.nonneg a]
      simpa [this] using hnonneg_sum
  -- Sum the pointwise inequality and swap sums on the RHS.
  have hsum_le :
      (∑ a : α, if (∃ i : ι, E i a) then P.pmf a else 0)
        ≤ ∑ a : α, ∑ i : ι, if E i a then P.pmf a else 0 := by
    refine Finset.sum_le_sum ?_
    intro a _
    exact hpoint a
  -- Conclude by rewriting the RHS back to `∑ i, probEvent ...`.
  have :
      (∑ a : α, if (∃ i : ι, E i a) then P.pmf a else 0)
        ≤ ∑ i : ι, ∑ a : α, if E i a then P.pmf a else 0 := by
    simpa [hswap] using hsum_le
  simpa using this

theorem theorem24
    {ι : Type u} [Fintype ι]
    (Q : ι → FinDist (BitStr m × BitStr k))
    (hQ : ∀ i, (Q i).Pos)
    (t : Nat) (hmt : 0 < m + t)
    (hPRF : PRFSecure (k := m) (n := m) (m := k) T F ε)
    (hBound :
      (Fintype.card ι : ℝ) *
          ((ε m) + 2 * (((2 : ℝ) ^ (2 * (m + t))) / (Fintype.card (BitStr m × BitStr k) : ℝ)))
        < 1) :
    ∃ key : BitStr m,
      ∀ i : ι,
        ¬((FinDist.klDiv (prfPairDist (m := m) (k := k) F key) (Q i)) / Real.log 2 ≤ t) := by
  classical
  let Ukey : FinDist (BitStr m) := Epiplexity.FinDist.uniform (α := BitStr m)
  let bound : ℝ :=
    (ε m) + 2 * (((2 : ℝ) ^ (2 * (m + t))) / (Fintype.card (BitStr m × BitStr k) : ℝ))
  -- Union bound over the finite family of candidate models.
  have hEach :
      ∀ i : ι,
        probEvent Ukey
            (fun key =>
              (FinDist.klDiv (prfPairDist (m := m) (k := k) F key) (Q i)) / Real.log 2 ≤ t)
          ≤ bound := by
    intro i
    simpa [Ukey, bound] using
      (probEvent_goodKey_le_bound (m := m) (k := k) (F := F) (ε := ε) (T := T)
        (Q := Q i) (t := t) (hQ := hQ i) hmt hPRF)
  have hUnion_le :
      probEvent Ukey
          (fun key =>
            ∃ i : ι,
              (FinDist.klDiv (prfPairDist (m := m) (k := k) F key) (Q i)) / Real.log 2 ≤ t)
        ≤ (Fintype.card ι : ℝ) * bound := by
    -- Apply union bound, then bound each summand by `bound`.
    have hUB :
        probEvent Ukey
            (fun key =>
              ∃ i : ι,
                (FinDist.klDiv (prfPairDist (m := m) (k := k) F key) (Q i)) / Real.log 2 ≤ t)
          ≤
        ∑ i : ι,
          probEvent Ukey
            (fun key =>
              (FinDist.klDiv (prfPairDist (m := m) (k := k) F key) (Q i)) / Real.log 2 ≤ t) := by
      exact probEvent_exists_le_sum (P := Ukey)
        (E := fun i key =>
          (FinDist.klDiv (prfPairDist (m := m) (k := k) F key) (Q i)) / Real.log 2 ≤ t)
    have hsum :
        (∑ i : ι,
            probEvent Ukey
              (fun key =>
                (FinDist.klDiv (prfPairDist (m := m) (k := k) F key) (Q i)) / Real.log 2 ≤ t))
          ≤ ∑ _i : ι, bound := by
      refine Finset.sum_le_sum ?_
      intro i _
      exact hEach i
    have hsum_const : (∑ _i : ι, bound) = (Fintype.card ι : ℝ) * bound := by
      simp [Finset.sum_const]
    have hsum_le : (∑ _i : ι, bound) ≤ (Fintype.card ι : ℝ) * bound := by
      simp [hsum_const]
    exact le_trans hUB (le_trans hsum hsum_le)
  have hUnion_lt : probEvent Ukey
          (fun key =>
            ∃ i : ι,
              (FinDist.klDiv (prfPairDist (m := m) (k := k) F key) (Q i)) / Real.log 2 ≤ t) < 1 := by
    have : (Fintype.card ι : ℝ) * bound < 1 := by
      simpa [bound] using hBound
    exact lt_of_le_of_lt hUnion_le this
  -- If the union event has probability < 1, there exists a key outside it.
  have hexists :
      ∃ key : BitStr m,
        ¬(∃ i : ι,
            (FinDist.klDiv (prfPairDist (m := m) (k := k) F key) (Q i)) / Real.log 2 ≤ t) := by
    by_contra hno
    have hall : ∀ key : BitStr m,
        (∃ i : ι,
          (FinDist.klDiv (prfPairDist (m := m) (k := k) F key) (Q i)) / Real.log 2 ≤ t) := by
      intro key
      by_contra hk
      exact hno ⟨key, hk⟩
    have hprob1 :
        probEvent Ukey
            (fun key =>
              ∃ i : ι,
                (FinDist.klDiv (prfPairDist (m := m) (k := k) F key) (Q i)) / Real.log 2 ≤ t)
          = 1 := by
      unfold probEvent
      simp [hall, Ukey.sum_one]
    have hUnion_lt' := hUnion_lt
    simp [hprob1] at hUnion_lt'
  rcases hexists with ⟨key, hkey⟩
  refine ⟨key, ?_⟩
  intro i hi
  exact hkey ⟨i, hi⟩

end PRFHighEpiplexity

end

end Crypto
end Epiplexity
end HeytingLean
