import Mathlib.Algebra.Group.End
import HeytingLean.Topology.Knot.ArtinBraidGroup

/-!
# Artin braid group: permutation representation (Phase 4)

This file defines the standard map `Bₙ → Sₙ` sending the braid generator `σᵢ`
to the adjacent transposition `(i i+1)` on `Fin n`.

This is the classical quotient map from the braid group to the symmetric group,
obtained by imposing additional relations `σᵢ^2 = 1`.
-/

namespace HeytingLean
namespace Topology
namespace Knot

namespace ArtinBraid

open PresentedGroup

namespace PermRep

open Equiv

private def strand (n k : Nat) (hk : k < n) : Fin n :=
  ⟨k, hk⟩

/-- Adjacent-transposition interpretation of a braid generator on `n` strands. -/
def sigmaPerm (n : Nat) : Gen n → Equiv.Perm (Fin n) := fun i =>
  let a : Fin n := strand n i.1 (Nat.lt_of_lt_pred i.2)
  let b : Fin n := strand n (i.1 + 1) <| by
    have hi : i.1 < n.pred := by
      rw [Nat.pred_eq_sub_one]
      exact i.2
    have hi' : i.1.succ < n := (Nat.lt_pred_iff).1 hi
    rw [← Nat.succ_eq_add_one]
    exact hi'
  Equiv.swap a b

@[simp] theorem sigmaPerm_apply (n : Nat) (i : Gen n) (x : Fin n) :
    sigmaPerm n i x =
      let a : Fin n := strand n i.1 (Nat.lt_of_lt_pred i.2)
      let b : Fin n := strand n (i.1 + 1) (by
        have hi : i.1 < n.pred := by
          rw [Nat.pred_eq_sub_one]
          exact i.2
        have hi' : i.1.succ < n := (Nat.lt_pred_iff).1 hi
        rw [← Nat.succ_eq_add_one]
        exact hi')
      if x = a then b else if x = b then a else x := by
  classical
  simp [sigmaPerm, Equiv.swap_apply_def]

private theorem swap_mul_swap_comm_of_disjoint {α : Type} [DecidableEq α] {a b c d : α}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Equiv.swap a b * Equiv.swap c d = Equiv.swap c d * Equiv.swap a b := by
  ext x
  by_cases hxa : x = a
  · subst x
    have hcd_a : Equiv.swap c d a = a := Equiv.swap_apply_of_ne_of_ne hac had
    have hcd_b : Equiv.swap c d b = b := Equiv.swap_apply_of_ne_of_ne hbc hbd
    simp [Equiv.Perm.mul_apply, hcd_a, hcd_b]
  by_cases hxb : x = b
  · subst x
    have hcd_a : Equiv.swap c d a = a := Equiv.swap_apply_of_ne_of_ne hac had
    have hcd_b : Equiv.swap c d b = b := Equiv.swap_apply_of_ne_of_ne hbc hbd
    simp [Equiv.Perm.mul_apply, hcd_a, hcd_b]
  by_cases hxc : x = c
  · subst x
    have hab_c : Equiv.swap a b c = c := Equiv.swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc)
    have hab_d : Equiv.swap a b d = d := Equiv.swap_apply_of_ne_of_ne (Ne.symm had) (Ne.symm hbd)
    simp [Equiv.Perm.mul_apply, hab_c, hab_d]
  by_cases hxd : x = d
  · subst x
    have hab_c : Equiv.swap a b c = c := Equiv.swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc)
    have hab_d : Equiv.swap a b d = d := Equiv.swap_apply_of_ne_of_ne (Ne.symm had) (Ne.symm hbd)
    simp [Equiv.Perm.mul_apply, hab_c, hab_d]
  have hab : Equiv.swap a b x = x := Equiv.swap_apply_of_ne_of_ne hxa hxb
  have hcd : Equiv.swap c d x = x := Equiv.swap_apply_of_ne_of_ne hxc hxd
  simp [Equiv.Perm.mul_apply, hab, hcd]

private theorem sigmaPerm_comm {n i j : Nat} (hi : i < n - 1) (hj : j < n - 1)
    (hfar : i + 1 < j ∨ j + 1 < i) :
    sigmaPerm n ⟨i, hi⟩ * sigmaPerm n ⟨j, hj⟩ = sigmaPerm n ⟨j, hj⟩ * sigmaPerm n ⟨i, hi⟩ := by
  classical
  -- Expand both generators as swaps and use the disjointness commutation lemma.
  let ai : Fin n := strand n i (Nat.lt_of_lt_pred hi)
  let bi : Fin n :=
    strand n (i + 1) <| by
      have hiPred : i < n.pred := by
        rw [Nat.pred_eq_sub_one]
        exact hi
      have hiSucc : i.succ < n := (Nat.lt_pred_iff).1 hiPred
      rw [← Nat.succ_eq_add_one]
      exact hiSucc
  let aj : Fin n := strand n j (Nat.lt_of_lt_pred hj)
  let bj : Fin n :=
    strand n (j + 1) <| by
      have hjPred : j < n.pred := by
        rw [Nat.pred_eq_sub_one]
        exact hj
      have hjSucc : j.succ < n := (Nat.lt_pred_iff).1 hjPred
      rw [← Nat.succ_eq_add_one]
      exact hjSucc

  have hij : i ≠ j := by
    cases hfar with
    | inl h => exact Nat.ne_of_lt (Nat.lt_trans (Nat.lt_succ_self i) h)
    | inr h => exact Nat.ne_of_gt (Nat.lt_trans (Nat.lt_succ_self j) h)
  have hij1 : i ≠ j + 1 := by
    cases hfar with
    | inl h =>
        have hij : i < j := Nat.lt_of_succ_lt h
        exact Nat.ne_of_lt (Nat.lt_trans hij (Nat.lt_succ_self j))
    | inr h =>
        exact Nat.ne_of_gt h
  have hi1j : i + 1 ≠ j := by
    cases hfar with
    | inl h => exact Nat.ne_of_lt h
    | inr h =>
        exact Nat.ne_of_gt <| Nat.lt_trans (Nat.lt_of_succ_lt h) (Nat.lt_succ_self i)
  have hi1j1 : i + 1 ≠ j + 1 := by
    cases hfar with
    | inl h => exact Nat.ne_of_lt (Nat.lt_trans h (Nat.lt_succ_self j))
    | inr h => exact Nat.ne_of_gt (Nat.lt_trans h (Nat.lt_succ_self i))

  have hac : ai ≠ aj := by
    intro h
    exact hij (congrArg Fin.val h)
  have had : ai ≠ bj := by
    intro h
    exact hij1 (congrArg Fin.val h)
  have hbc : bi ≠ aj := by
    intro h
    exact hi1j (congrArg Fin.val h)
  have hbd : bi ≠ bj := by
    intro h
    exact hi1j1 (congrArg Fin.val h)

  have :
      Equiv.swap ai bi * Equiv.swap aj bj = Equiv.swap aj bj * Equiv.swap ai bi :=
    swap_mul_swap_comm_of_disjoint (a := ai) (b := bi) (c := aj) (d := bj) hac had hbc hbd
  simpa [sigmaPerm, ai, bi, aj, bj]

private theorem sigmaPerm_braid {n i : Nat} (hi : i + 2 < n) :
    let hi0 : i < n - 1 :=
      lt_sub_one_of_succ_lt (n := n) (i := i) <|
        Nat.lt_trans (Nat.lt_succ_self (i + 1)) hi
    let hi1 : i + 1 < n - 1 :=
      lt_sub_one_of_succ_lt (n := n) (i := i + 1) <| by
        simpa [Nat.add_assoc, Nat.succ_eq_add_one] using hi
    sigmaPerm n ⟨i, hi0⟩ * sigmaPerm n ⟨i + 1, hi1⟩ * sigmaPerm n ⟨i, hi0⟩ =
      sigmaPerm n ⟨i + 1, hi1⟩ * sigmaPerm n ⟨i, hi0⟩ * sigmaPerm n ⟨i + 1, hi1⟩ := by
  classical
  simp (config := { zeta := false }) only
  intro hi0 hi1
  -- Expand the two adjacent generators as swaps `(i i+1)` and `(i+1 i+2)`.
  let a : Fin n := strand n i (Nat.lt_of_lt_pred hi0)
  let b₀ : Fin n :=
    strand n (i + 1) <| by
      have hiPred : i < n.pred := by
        rw [Nat.pred_eq_sub_one]
        exact hi0
      have hiSucc : i.succ < n := (Nat.lt_pred_iff).1 hiPred
      rw [← Nat.succ_eq_add_one]
      exact hiSucc
  let b₁ : Fin n := strand n (i + 1) (Nat.lt_of_lt_pred hi1)
  let c : Fin n := strand n (i + 2) hi

  have hb : b₀ = b₁ := by
    apply Fin.ext
    rfl

  have hab : a ≠ b₀ := by
    intro h
    exact Nat.ne_of_lt (Nat.lt_succ_self i) (congrArg Fin.val h)
  have hcb : c ≠ b₀ := by
    intro h
    exact Nat.ne_of_gt (Nat.lt_succ_self (i + 1)) (congrArg Fin.val h)
  have hca : c ≠ a := by
    intro h
    exact Nat.ne_of_gt (Nat.lt_trans (Nat.lt_succ_self i) (Nat.lt_succ_self (i + 1)))
      (congrArg Fin.val h)

  have h_left :
      Equiv.swap a b₀ * Equiv.swap b₀ c * Equiv.swap a b₀ = Equiv.swap a c := by
    -- Use `swap_mul_swap_mul_swap` with `(x,y,z) = (c,b₀,a)`.
    simpa [Equiv.swap_comm, mul_assoc] using
      (Equiv.swap_mul_swap_mul_swap (x := c) (y := b₀) (z := a) hcb hca)

  have h_right :
      Equiv.swap b₀ c * Equiv.swap a b₀ * Equiv.swap b₀ c = Equiv.swap a c := by
    -- `(x,y,z) = (a,b₀,c)` gives `swap b₀ c * swap a b₀ * swap b₀ c = swap c a`.
    simpa [Equiv.swap_comm, mul_assoc] using
      (Equiv.swap_mul_swap_mul_swap (x := a) (y := b₀) (z := c) hab (Ne.symm hca))

  have hs0 : sigmaPerm n ⟨i, hi0⟩ = Equiv.swap a b₀ := by
    simp [sigmaPerm, a, b₀, strand]

  have hs1 : sigmaPerm n ⟨i + 1, hi1⟩ = Equiv.swap b₀ c := by
    -- The `σ_{i+1}` swap uses the same values, but potentially different proof objects.
    -- Align the shared endpoints via `Fin.ext` and then rewrite.
    let c₁ : Fin n :=
      strand n ((i + 1) + 1) <| by
        have hiPred : i + 1 < n.pred := by
          rw [Nat.pred_eq_sub_one]
          exact hi1
        have hiSucc : (i + 1).succ < n := (Nat.lt_pred_iff).1 hiPred
        rw [← Nat.succ_eq_add_one]
        exact hiSucc
    have hb' : b₁ = b₀ := hb.symm
    have hc' : c₁ = c := by
      apply Fin.ext
      simp [c₁, c, strand, Nat.add_assoc]
    have hs1raw : sigmaPerm n ⟨i + 1, hi1⟩ = Equiv.swap b₁ c₁ := by
      rfl
    calc
      sigmaPerm n ⟨i + 1, hi1⟩ = Equiv.swap b₁ c₁ := hs1raw
      _ = Equiv.swap b₀ c := by
            simp [hb', hc']

  -- Conclude the braid relation by rewriting both sides to `swap a c`.
  calc
    sigmaPerm n ⟨i, hi0⟩ * sigmaPerm n ⟨i + 1, hi1⟩ * sigmaPerm n ⟨i, hi0⟩
        = Equiv.swap a b₀ * Equiv.swap b₀ c * Equiv.swap a b₀ := by
            simp [hs0, hs1, mul_assoc]
    _ = Equiv.swap a c := h_left
    _ = Equiv.swap b₀ c * Equiv.swap a b₀ * Equiv.swap b₀ c := by
            symm
            exact h_right
    _ = sigmaPerm n ⟨i + 1, hi1⟩ * sigmaPerm n ⟨i, hi0⟩ * sigmaPerm n ⟨i + 1, hi1⟩ := by
            simp [hs0, hs1, mul_assoc]

/-- The canonical map `Bₙ → Sₙ` sending `σᵢ ↦ (i i+1)`. -/
def toPerm (n : Nat) : BraidGroup n →* Equiv.Perm (Fin n) :=
  PresentedGroup.toGroup (rels := rels n) (f := sigmaPerm n) <| by
    classical
    intro r hr
    rcases hr with hr | hr
    · rcases hr with ⟨i, j, hi, hj, hfar, rfl⟩
      have hcomm :
          sigmaPerm n ⟨i, hi⟩ * sigmaPerm n ⟨j, hj⟩ =
            sigmaPerm n ⟨j, hj⟩ * sigmaPerm n ⟨i, hi⟩ :=
        sigmaPerm_comm (n := n) (i := i) (j := j) hi hj hfar
      let lhs : FreeGroup (Gen n) := fgNat n i hi * fgNat n j hj
      let rhs : FreeGroup (Gen n) := fgNat n j hj * fgNat n i hi
      have hlift :
          (FreeGroup.lift (sigmaPerm n)) lhs = (FreeGroup.lift (sigmaPerm n)) rhs := by
        simp [lhs, rhs, fgNat, fgOf, FreeGroup.lift_apply_of, hcomm]
      calc
        (FreeGroup.lift (sigmaPerm n)) (commRelator n i j hi hj)
            = (FreeGroup.lift (sigmaPerm n)) (lhs * rhs⁻¹) := by
                simp [commRelator, lhs, rhs]
        _ = (FreeGroup.lift (sigmaPerm n)) lhs * ((FreeGroup.lift (sigmaPerm n)) rhs)⁻¹ := by
                simp
        _ = (FreeGroup.lift (sigmaPerm n)) rhs * ((FreeGroup.lift (sigmaPerm n)) rhs)⁻¹ := by
                simp [hlift]
        _ = 1 := by simp
    · rcases hr with ⟨i, hi, rfl⟩
      -- Use the same internal witnesses as `braidRelator`.
      let hi0 : i < n - 1 :=
        lt_sub_one_of_succ_lt (n := n) (i := i) <|
          Nat.lt_trans (Nat.lt_succ_self (i + 1)) hi
      let hi1 : i + 1 < n - 1 :=
        lt_sub_one_of_succ_lt (n := n) (i := i + 1) <| by
          -- goal: (i+1).succ < n
          rw [Nat.succ_eq_add_one]
          have e : i + 2 = i + 1 + 1 := by
            simp [Nat.add_assoc]
          rw [← e]
          exact hi
      let lhs : FreeGroup (Gen n) := fgNat n i hi0 * fgNat n (i + 1) hi1 * fgNat n i hi0
      let rhs : FreeGroup (Gen n) := fgNat n (i + 1) hi1 * fgNat n i hi0 * fgNat n (i + 1) hi1
      have hbraid :
          sigmaPerm n ⟨i, hi0⟩ * sigmaPerm n ⟨i + 1, hi1⟩ * sigmaPerm n ⟨i, hi0⟩ =
            sigmaPerm n ⟨i + 1, hi1⟩ * sigmaPerm n ⟨i, hi0⟩ * sigmaPerm n ⟨i + 1, hi1⟩ := by
        simpa [hi0, hi1] using (sigmaPerm_braid (n := n) (i := i) hi)
      have hlift :
          (FreeGroup.lift (sigmaPerm n)) lhs = (FreeGroup.lift (sigmaPerm n)) rhs := by
        -- Reduce to the braid relation in `Sₙ`.
        simp [lhs, rhs, fgNat, fgOf, FreeGroup.lift_apply_of]
        simpa [mul_assoc] using hbraid
      calc
        (FreeGroup.lift (sigmaPerm n)) (braidRelator n i hi)
            = (FreeGroup.lift (sigmaPerm n)) (lhs * rhs⁻¹) := by
                simp [braidRelator, lhs, rhs]
        _ = (FreeGroup.lift (sigmaPerm n)) lhs * ((FreeGroup.lift (sigmaPerm n)) rhs)⁻¹ := by
                simp
        _ = (FreeGroup.lift (sigmaPerm n)) rhs * ((FreeGroup.lift (sigmaPerm n)) rhs)⁻¹ := by
                simp [hlift]
        _ = 1 := by simp

@[simp]
theorem toPerm_sigma (n : Nat) (i : Gen n) : toPerm n (sigma i) = sigmaPerm n i := by
  classical
  simp [toPerm, sigma]

end PermRep

end ArtinBraid

end Knot
end Topology
end HeytingLean
