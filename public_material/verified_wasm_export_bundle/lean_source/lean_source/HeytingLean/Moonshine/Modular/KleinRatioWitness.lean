import HeytingLean.Moonshine.Modular.KleinDiscriminantIdentityProof
import HeytingLean.Moonshine.Modular.Hauptmodul
import Mathlib.NumberTheory.ModularForms.LevelOne
import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Modular

open UpperHalfPlane
open scoped CongruenceSubgroup

/--
Structured witness for the CV-3 closure contract:
a level-one weight-zero modular form equal to `kleinDenom / Delta`
with one anchor evaluation.
-/
structure KleinRatioWitness (τ0 : ℍ) where
  f : ModularForm Γ(1) 0
  ratio_eq : ∀ τ : ℍ, f τ = kleinDenom τ / Delta τ
  anchor_eq : f τ0 = (1728 : ℂ)

theorem kleinDiscriminantIdentity_of_witness {τ0 : ℍ}
    (w : KleinRatioWitness τ0) :
    KleinDiscriminantIdentity := by
  exact kleinDiscriminantIdentity_of_ratio_modularForm_weight_zero
    w.f w.ratio_eq τ0 w.anchor_eq

theorem kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_of_witness {τ0 : ℍ}
    (w : KleinRatioWitness τ0) :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk := by
  exact kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_of_ratio_modularForm_weight_zero
    w.f w.ratio_eq τ0 w.anchor_eq

def witnessOfKleinDiscriminantIdentity (τ0 : ℍ)
    (hDisc : KleinDiscriminantIdentity) :
    KleinRatioWitness τ0 := by
  refine ⟨ModularForm.const (Γ := Γ(1)) (1728 : ℂ), ?_, ?_⟩
  · intro τ
    have hDiv : kleinDenom τ / Delta τ = (1728 : ℂ) :=
      kleinDenom_div_Delta_eq_1728_of_kleinDiscriminantIdentity hDisc τ
    simpa using hDiv.symm
  · simp

theorem kleinDiscriminantIdentity_iff_nonempty_witness (τ0 : ℍ) :
    KleinDiscriminantIdentity ↔ Nonempty (KleinRatioWitness τ0) := by
  constructor
  · intro hDisc
    exact ⟨witnessOfKleinDiscriminantIdentity τ0 hDisc⟩
  · rintro ⟨w⟩
    exact kleinDiscriminantIdentity_of_witness w

theorem nonempty_witness_of_kleinDiscriminantIdentity (τ0 : ℍ)
    (hDisc : KleinDiscriminantIdentity) :
    Nonempty (KleinRatioWitness τ0) :=
  (kleinDiscriminantIdentity_iff_nonempty_witness τ0).1 hDisc

theorem kleinDiscriminantIdentity_of_nonempty_witness (τ0 : ℍ)
    (hW : Nonempty (KleinRatioWitness τ0)) :
    KleinDiscriminantIdentity :=
  (kleinDiscriminantIdentity_iff_nonempty_witness τ0).2 hW

theorem nonempty_witness_of_kleinDenom_div_Delta_eq_1728 (τ0 : ℍ)
    (hDiv : ∀ τ : ℍ, kleinDenom τ / Delta τ = (1728 : ℂ)) :
    Nonempty (KleinRatioWitness τ0) := by
  exact nonempty_witness_of_kleinDiscriminantIdentity τ0
    (kleinDiscriminantIdentity_of_kleinDenom_div_Delta_eq_1728 hDiv)

theorem hDiv_of_kleinDiscriminantIdentity
    (hDisc : KleinDiscriminantIdentity) :
    ∀ τ : ℍ, kleinDenom τ / Delta τ = (1728 : ℂ) :=
  kleinDenom_div_Delta_eq_1728_of_kleinDiscriminantIdentity hDisc

theorem hDiv_of_kleinBfunExtDeltaIdentityCusp
    (hCusp : KleinBfunExtDeltaIdentityCusp) :
    ∀ τ : ℍ, kleinDenom τ / Delta τ = (1728 : ℂ) := by
  exact hDiv_of_kleinDiscriminantIdentity
    (kleinDiscriminantIdentity_of_kleinBfunExtDeltaIdentityCusp hCusp)

theorem hDiv_of_kleinBfunExtDeltaIdentityOnPuncturedUnitDisk
    (hPunct : KleinBfunExtDeltaIdentityOnPuncturedUnitDisk) :
    ∀ τ : ℍ, kleinDenom τ / Delta τ = (1728 : ℂ) := by
  exact hDiv_of_kleinDiscriminantIdentity
    (kleinDiscriminantIdentity_of_kleinBfunExtDeltaIdentityOnPuncturedUnitDisk hPunct)

theorem hDiv_of_eisensteinEtaIdentity
    (hEta : ∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat)) :
    ∀ τ : ℍ, kleinDenom τ / Delta τ = (1728 : ℂ) := by
  exact hDiv_of_kleinDiscriminantIdentity
    (kleinDiscriminantIdentity_of_eisensteinEtaIdentity hEta)

theorem hDiv_of_exists_ratio_modularForm_weight_zero
    (hRatio :
      ∃ f : ModularForm Γ(1) 0, ∀ τ : ℍ, f τ = kleinDenom τ / Delta τ) :
    ∀ τ : ℍ, kleinDenom τ / Delta τ = (1728 : ℂ) := by
  rcases hRatio with ⟨f, hf⟩
  exact kleinDenom_div_Delta_eq_1728_of_ratio_modularForm_weight_zero_atImInfty f hf

theorem hDiv
    (hCusp : KleinBfunExtDeltaIdentityCusp) :
    ∀ τ : ℍ, kleinDenom τ / Delta τ = (1728 : ℂ) :=
  hDiv_of_kleinBfunExtDeltaIdentityCusp hCusp

theorem nonempty_witness_of_hDiv (τ0 : ℍ)
    (hDiv : ∀ τ : ℍ, kleinDenom τ / Delta τ = (1728 : ℂ)) :
    Nonempty (KleinRatioWitness τ0) :=
  nonempty_witness_of_kleinDenom_div_Delta_eq_1728 τ0 hDiv

theorem nonempty_witness_of_hDiv_cusp (τ0 : ℍ)
    (hCusp : KleinBfunExtDeltaIdentityCusp) :
    Nonempty (KleinRatioWitness τ0) :=
  nonempty_witness_of_hDiv τ0 (hDiv hCusp)

theorem nonempty_witness_of_exists_ratio_modularForm_weight_zero
    (τ0 : ℍ)
    (hRatio :
      ∃ f : ModularForm Γ(1) 0, ∀ τ : ℍ, f τ = kleinDenom τ / Delta τ) :
    Nonempty (KleinRatioWitness τ0) :=
  nonempty_witness_of_hDiv τ0 (hDiv_of_exists_ratio_modularForm_weight_zero hRatio)

theorem exists_ratio_modularForm_weight_zero_iff_nonempty_witness (τ0 : ℍ) :
    (∃ f : ModularForm Γ(1) 0,
      (∀ τ : ℍ, f τ = kleinDenom τ / Delta τ) ∧ f τ0 = (1728 : ℂ)) ↔
      Nonempty (KleinRatioWitness τ0) := by
  constructor
  · rintro ⟨f, hRatio, hAt⟩
    exact ⟨⟨f, hRatio, hAt⟩⟩
  · rintro ⟨w⟩
    exact ⟨w.f, w.ratio_eq, w.anchor_eq⟩

theorem eisensteinEtaIdentity_iff_nonempty_witness (τ0 : ℍ) :
    (∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat)) ↔
      Nonempty (KleinRatioWitness τ0) := by
  calc
    (∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat)) ↔ KleinDiscriminantIdentity := by
        exact (kleinDiscriminantIdentity_iff_eisensteinEtaIdentity).symm
    _ ↔ Nonempty (KleinRatioWitness τ0) := by
        exact kleinDiscriminantIdentity_iff_nonempty_witness τ0

theorem nonempty_witness_of_eisensteinEtaIdentity (τ0 : ℍ)
    (hEta : ∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat)) :
    Nonempty (KleinRatioWitness τ0) :=
  (eisensteinEtaIdentity_iff_nonempty_witness τ0).1 hEta

theorem eisensteinEtaIdentity_of_nonempty_witness (τ0 : ℍ)
    (hW : Nonempty (KleinRatioWitness τ0)) :
    ∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) =
      (1728 : ℂ) * (eta τ) ^ (24 : Nat) :=
  (eisensteinEtaIdentity_iff_nonempty_witness τ0).2 hW

theorem kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_iff_nonempty_witness (τ0 : ℍ) :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk ↔ Nonempty (KleinRatioWitness τ0) := by
  calc
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk ↔ KleinDiscriminantIdentity := by
      exact (kleinDiscriminantIdentity_iff_kleinBfunExtDeltaIdentityOnPuncturedUnitDisk).symm
    _ ↔ Nonempty (KleinRatioWitness τ0) := by
      exact kleinDiscriminantIdentity_iff_nonempty_witness τ0

theorem nonempty_witness_of_kleinBfunExtDeltaIdentityOnPuncturedUnitDisk (τ0 : ℍ)
    (hB : KleinBfunExtDeltaIdentityOnPuncturedUnitDisk) :
    Nonempty (KleinRatioWitness τ0) :=
  (kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_iff_nonempty_witness τ0).1 hB

theorem kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_of_nonempty_witness (τ0 : ℍ)
    (hW : Nonempty (KleinRatioWitness τ0)) :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk :=
  (kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_iff_nonempty_witness τ0).2 hW

theorem kleinBfunExtDeltaIdentityCusp_iff_nonempty_witness (τ0 : ℍ) :
    KleinBfunExtDeltaIdentityCusp ↔ Nonempty (KleinRatioWitness τ0) := by
  calc
    KleinBfunExtDeltaIdentityCusp ↔ KleinDiscriminantIdentity := by
      exact (kleinDiscriminantIdentity_iff_kleinBfunExtDeltaIdentityCusp).symm
    _ ↔ Nonempty (KleinRatioWitness τ0) := by
      exact kleinDiscriminantIdentity_iff_nonempty_witness τ0

theorem nonempty_witness_of_kleinBfunExtDeltaIdentityCusp (τ0 : ℍ)
    (hB : KleinBfunExtDeltaIdentityCusp) :
    Nonempty (KleinRatioWitness τ0) :=
  (kleinBfunExtDeltaIdentityCusp_iff_nonempty_witness τ0).1 hB

theorem kleinBfunExtDeltaIdentityCusp_of_nonempty_witness (τ0 : ℍ)
    (hW : Nonempty (KleinRatioWitness τ0)) :
    KleinBfunExtDeltaIdentityCusp :=
  (kleinBfunExtDeltaIdentityCusp_iff_nonempty_witness τ0).2 hW

theorem exists_ratio_modularForm_weight_zero_of_kleinBfunExtDeltaIdentityOnPuncturedUnitDisk
    (τ0 : ℍ) (hB : KleinBfunExtDeltaIdentityOnPuncturedUnitDisk) :
    ∃ f : ModularForm Γ(1) 0,
      (∀ τ : ℍ, f τ = kleinDenom τ / Delta τ) ∧ f τ0 = (1728 : ℂ) := by
  exact (exists_ratio_modularForm_weight_zero_iff_nonempty_witness τ0).2
    (nonempty_witness_of_kleinBfunExtDeltaIdentityOnPuncturedUnitDisk τ0 hB)

theorem exists_ratio_modularForm_weight_zero_of_kleinBfunExtDeltaIdentityCusp
    (τ0 : ℍ) (hB : KleinBfunExtDeltaIdentityCusp) :
    ∃ f : ModularForm Γ(1) 0,
      (∀ τ : ℍ, f τ = kleinDenom τ / Delta τ) ∧ f τ0 = (1728 : ℂ) := by
  exact (exists_ratio_modularForm_weight_zero_iff_nonempty_witness τ0).2
    (nonempty_witness_of_kleinBfunExtDeltaIdentityCusp τ0 hB)

theorem kleinDenom_ne_zero_global_of_nonempty_witness (τ0 : ℍ)
    (hW : Nonempty (KleinRatioWitness τ0)) :
    ∀ τ : ℍ, kleinDenom τ ≠ 0 := by
  exact
    kleinDenom_ne_zero_global_of_kleinBfunExtDeltaIdentityCusp
      (kleinBfunExtDeltaIdentityCusp_of_nonempty_witness τ0 hW)

theorem kleinJ₀_isHauptmodulWithDenom_of_nonempty_witness (τ0 : ℍ)
    (hW : Nonempty (KleinRatioWitness τ0)) :
    IsHauptmodulWithDenom (⊤ : Subgroup SL2Z) kleinJ₀ kleinDenom := by
  refine ⟨kleinJ₀_isHauptmodul, ?_⟩
  exact kleinDenom_ne_zero_global_of_nonempty_witness τ0 hW

theorem q_tau0_ne_zero (τ0 : ℍ) : q τ0 ≠ 0 :=
  q_ne_zero τ0

theorem norm_q_tau0_lt_one (τ0 : ℍ) : ‖q τ0‖ < 1 :=
  norm_q_lt_one τ0

theorem delta_tau0_ne_zero (τ0 : ℍ) : Delta τ0 ≠ 0 :=
  Delta_ne_zero τ0

theorem Delta_cusp_q_tau0_ne_zero (τ0 : ℍ) : Delta_cusp (q τ0) ≠ 0 :=
  Delta_cusp_ne_zero_of_eq_q τ0

theorem one_sub_qpow_tau0_ne_zero (τ0 : ℍ) (n : ℕ) :
    (1 : ℂ) - (q τ0) ^ (n + 1) ≠ 0 := by
  have hlt : ‖(q τ0) ^ (n + 1)‖ < (1 : ℝ) := by
    simpa [norm_pow] using
      pow_lt_one₀ (norm_nonneg (q τ0)) (norm_q_lt_one τ0) (n := n + 1)
        (Nat.succ_ne_zero n)
  exact sub_ne_zero.mpr (by
    intro hEq
    have hnorm : ‖(q τ0) ^ (n + 1)‖ = (1 : ℝ) := by
      simpa using (congrArg norm hEq).symm
    exact (ne_of_lt hlt) hnorm)

theorem one_sub_qpow_tau0_pow24_ne_zero (τ0 : ℍ) (n : ℕ) :
    ((1 : ℂ) - (q τ0) ^ (n + 1)) ^ (24 : Nat) ≠ 0 :=
  pow_ne_zero _ (one_sub_qpow_tau0_ne_zero τ0 n)

theorem finite_q_product_factor_ne_zero (τ0 : ℍ) (N : ℕ) :
    ((Finset.Icc (1 : ℕ) N).prod (fun i => ((1 : ℂ) - (q τ0) ^ i) ^ (24 : Nat))) ≠ 0 := by
  classical
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro i hi
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  rcases Nat.exists_eq_add_of_le hi1 with ⟨k, hk⟩
  simpa [hk, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    one_sub_qpow_tau0_pow24_ne_zero τ0 k

end HeytingLean.Moonshine.Modular
