import HeytingLean.Moonshine.Modular.DeltaCusp
import HeytingLean.Moonshine.Modular.KleinDenomCuspBridge
import HeytingLean.Moonshine.Modular.KleinDenominatorGlobalReduction

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Modular

open UpperHalfPlane

open scoped MatrixGroups

/-- Preferred global identity for the level-1 denominator:
`(E4 τ)^3 - (E6 τ)^2 = 1728 * Δ(τ)`. -/
def KleinDiscriminantIdentity : Prop :=
  ∀ τ : ℍ, kleinDenom τ = (1728 : ℂ) * Delta τ

/-- Stronger disk-level version in `q`-coordinates. -/
def KleinDiscriminantIdentityOnUnitDisk : Prop :=
  ∀ q : ℂ, ‖q‖ < 1 → kleinDfun q = (1728 : ℂ) * Delta_cusp q

/-- Punctured-disk version in `q`-coordinates (the only points needed for `q τ`, since `q τ ≠ 0`). -/
def KleinDiscriminantIdentityOnPuncturedUnitDisk : Prop :=
  ∀ q : ℂ, ‖q‖ < 1 → q ≠ 0 → kleinDfun q = (1728 : ℂ) * Delta_cusp q

/-- Cusp-coordinate version of the same identity:
`kleinDfun (q τ) = 1728 * Delta_cusp (q τ)`. -/
def KleinDiscriminantIdentityCusp : Prop :=
  ∀ τ : ℍ, kleinDfun (q τ) = (1728 : ℂ) * Delta_cusp (q τ)

/-- Disk-level reduction of `kleinBfunExt` to `Delta_cusp` away from `q = 0`. -/
def KleinBfunExtDeltaIdentityOnUnitDisk : Prop :=
  ∀ q : ℂ, ‖q‖ < 1 → q ≠ 0 →
    kleinBfunExt q = (1728 : ℂ) * q⁻¹ * Delta_cusp q

/-- Same `kleinBfunExt`-to-`Delta_cusp` reduction, named by the true domain of use
(the punctured unit disk). -/
def KleinBfunExtDeltaIdentityOnPuncturedUnitDisk : Prop :=
  ∀ q : ℂ, ‖q‖ < 1 → q ≠ 0 →
    kleinBfunExt q = (1728 : ℂ) * q⁻¹ * Delta_cusp q

/-- Cusp-coordinate version of the `kleinBfunExt`-to-`Delta_cusp` reduction. -/
def KleinBfunExtDeltaIdentityCusp : Prop :=
  ∀ τ : ℍ,
    kleinBfunExt (q τ) = (1728 : ℂ) * (q τ)⁻¹ * Delta_cusp (q τ)

theorem kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_iff_unitDisk :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk ↔ KleinBfunExtDeltaIdentityOnUnitDisk := by
  rfl

theorem kleinDiscriminantIdentityCusp_of_unitDisk
    (hDisk : KleinDiscriminantIdentityOnUnitDisk) :
    KleinDiscriminantIdentityCusp := by
  intro τ
  exact hDisk (q τ) (norm_q_lt_one τ)

theorem kleinDiscriminantIdentityOnPuncturedUnitDisk_of_unitDisk
    (hDisk : KleinDiscriminantIdentityOnUnitDisk) :
    KleinDiscriminantIdentityOnPuncturedUnitDisk := by
  intro q hq _hq0
  exact hDisk q hq

theorem kleinDiscriminantIdentityCusp_of_puncturedUnitDisk
    (hPunct : KleinDiscriminantIdentityOnPuncturedUnitDisk) :
    KleinDiscriminantIdentityCusp := by
  intro τ
  exact hPunct (q τ) (norm_q_lt_one τ) (q_ne_zero τ)

theorem kleinDiscriminantIdentityOnPuncturedUnitDisk_of_cusp
    (hCusp : KleinDiscriminantIdentityCusp) :
    KleinDiscriminantIdentityOnPuncturedUnitDisk := by
  intro w hw hw0
  let τ : ℍ :=
    ⟨Function.Periodic.invQParam 1 w,
      Function.Periodic.im_invQParam_pos_of_norm_lt_one Real.zero_lt_one hw hw0⟩
  have hwτ : q τ = w := by
    dsimp [q, τ]
    simpa using (Function.Periodic.qParam_right_inv (h := (1 : ℝ)) one_ne_zero hw0)
  calc
    kleinDfun w = kleinDfun (q τ) := by rw [hwτ]
    _ = (1728 : ℂ) * Delta_cusp (q τ) := hCusp τ
    _ = (1728 : ℂ) * Delta_cusp w := by rw [hwτ]

theorem kleinDiscriminantIdentityCusp_iff_puncturedUnitDisk :
    KleinDiscriminantIdentityCusp ↔ KleinDiscriminantIdentityOnPuncturedUnitDisk := by
  constructor
  · exact kleinDiscriminantIdentityOnPuncturedUnitDisk_of_cusp
  · exact kleinDiscriminantIdentityCusp_of_puncturedUnitDisk

theorem kleinBfunExtDeltaIdentityCusp_of_puncturedUnitDisk
    (hPunct : KleinBfunExtDeltaIdentityOnPuncturedUnitDisk) :
    KleinBfunExtDeltaIdentityCusp := by
  intro τ
  exact hPunct (q τ) (norm_q_lt_one τ) (q_ne_zero τ)

theorem kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_of_cusp
    (hCusp : KleinBfunExtDeltaIdentityCusp) :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk := by
  intro w hw hw0
  let τ : ℍ :=
    ⟨Function.Periodic.invQParam 1 w,
      Function.Periodic.im_invQParam_pos_of_norm_lt_one Real.zero_lt_one hw hw0⟩
  have hwτ : q τ = w := by
    dsimp [q, τ]
    simpa using (Function.Periodic.qParam_right_inv (h := (1 : ℝ)) one_ne_zero hw0)
  calc
    kleinBfunExt w = kleinBfunExt (q τ) := by rw [hwτ]
    _ = (1728 : ℂ) * (q τ)⁻¹ * Delta_cusp (q τ) := hCusp τ
    _ = (1728 : ℂ) * w⁻¹ * Delta_cusp w := by rw [hwτ]

theorem kleinBfunExtDeltaIdentityCusp_iff_puncturedUnitDisk :
    KleinBfunExtDeltaIdentityCusp ↔ KleinBfunExtDeltaIdentityOnPuncturedUnitDisk := by
  constructor
  · exact kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_of_cusp
  · exact kleinBfunExtDeltaIdentityCusp_of_puncturedUnitDisk

theorem kleinDiscriminantIdentity_of_cusp
    (hCusp : KleinDiscriminantIdentityCusp) :
    KleinDiscriminantIdentity := by
  intro τ
  calc
    kleinDenom τ = kleinDfun (q τ) := kleinDenom_eq_kleinDfun (τ := τ)
    _ = (1728 : ℂ) * Delta_cusp (q τ) := hCusp τ
    _ = (1728 : ℂ) * Delta τ := by rw [Delta_eq_Delta_cusp (τ := τ)]

theorem kleinDiscriminantIdentityCusp_of_global
    (hGlobal : KleinDiscriminantIdentity) :
    KleinDiscriminantIdentityCusp := by
  intro τ
  calc
    kleinDfun (q τ) = kleinDenom τ := (kleinDenom_eq_kleinDfun (τ := τ)).symm
    _ = (1728 : ℂ) * Delta τ := hGlobal τ
    _ = (1728 : ℂ) * Delta_cusp (q τ) := by rw [Delta_eq_Delta_cusp (τ := τ)]

theorem kleinDiscriminantIdentity_iff_cusp :
    KleinDiscriminantIdentity ↔ KleinDiscriminantIdentityCusp := by
  constructor
  · exact kleinDiscriminantIdentityCusp_of_global
  · exact kleinDiscriminantIdentity_of_cusp

theorem kleinDiscriminantIdentity_of_unitDisk
    (hDisk : KleinDiscriminantIdentityOnUnitDisk) :
    KleinDiscriminantIdentity :=
  kleinDiscriminantIdentity_of_cusp (kleinDiscriminantIdentityCusp_of_unitDisk hDisk)

theorem kleinDiscriminantIdentity_of_puncturedUnitDisk
    (hPunct : KleinDiscriminantIdentityOnPuncturedUnitDisk) :
    KleinDiscriminantIdentity :=
  kleinDiscriminantIdentity_of_cusp (kleinDiscriminantIdentityCusp_of_puncturedUnitDisk hPunct)

theorem kleinDiscriminantIdentity_iff_puncturedUnitDisk :
    KleinDiscriminantIdentity ↔ KleinDiscriminantIdentityOnPuncturedUnitDisk := by
  constructor
  · intro hGlobal
    exact
      kleinDiscriminantIdentityOnPuncturedUnitDisk_of_cusp
        (kleinDiscriminantIdentityCusp_of_global hGlobal)
  · exact kleinDiscriminantIdentity_of_puncturedUnitDisk

theorem kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_of_discriminant_puncturedUnitDisk
    (hPunct : KleinDiscriminantIdentityOnPuncturedUnitDisk) :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk := by
  intro q hq hq0
  have hD : kleinDfun q = (1728 : ℂ) * Delta_cusp q := hPunct q hq hq0
  calc
    kleinBfunExt q = q⁻¹ * kleinDfun q := by
      simpa using (kleinBfunExt_eq_div (q := q) hq0)
    _ = q⁻¹ * ((1728 : ℂ) * Delta_cusp q) := by rw [hD]
    _ = (1728 : ℂ) * q⁻¹ * Delta_cusp q := by ring

theorem kleinDiscriminantIdentityOnPuncturedUnitDisk_of_kleinBfunExtDeltaIdentityOnPuncturedUnitDisk
    (hB : KleinBfunExtDeltaIdentityOnPuncturedUnitDisk) :
    KleinDiscriminantIdentityOnPuncturedUnitDisk := by
  intro q hq hq0
  have hBq : kleinBfunExt q = (1728 : ℂ) * q⁻¹ * Delta_cusp q := hB q hq hq0
  calc
    kleinDfun q = q * kleinBfunExt q := by
      simpa using (kleinDfun_eq_mul_kleinBfunExt (q := q) hq0)
    _ = q * ((1728 : ℂ) * q⁻¹ * Delta_cusp q) := by rw [hBq]
    _ = (1728 : ℂ) * (q * q⁻¹) * Delta_cusp q := by ring
    _ = (1728 : ℂ) * Delta_cusp q := by simp [hq0]

theorem kleinDiscriminantIdentityOnPuncturedUnitDisk_iff_kleinBfunExtDeltaIdentityOnPuncturedUnitDisk :
    KleinDiscriminantIdentityOnPuncturedUnitDisk ↔ KleinBfunExtDeltaIdentityOnPuncturedUnitDisk := by
  constructor
  · exact kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_of_discriminant_puncturedUnitDisk
  · exact kleinDiscriminantIdentityOnPuncturedUnitDisk_of_kleinBfunExtDeltaIdentityOnPuncturedUnitDisk

theorem kleinDiscriminantIdentityCusp_iff_kleinBfunExtDeltaIdentityCusp :
    KleinDiscriminantIdentityCusp ↔ KleinBfunExtDeltaIdentityCusp := by
  calc
    KleinDiscriminantIdentityCusp ↔ KleinDiscriminantIdentityOnPuncturedUnitDisk := by
      exact kleinDiscriminantIdentityCusp_iff_puncturedUnitDisk
    _ ↔ KleinBfunExtDeltaIdentityOnPuncturedUnitDisk := by
      exact kleinDiscriminantIdentityOnPuncturedUnitDisk_iff_kleinBfunExtDeltaIdentityOnPuncturedUnitDisk
    _ ↔ KleinBfunExtDeltaIdentityCusp := by
      exact (kleinBfunExtDeltaIdentityCusp_iff_puncturedUnitDisk).symm

theorem kleinBfunExtDeltaIdentityCusp_of_discriminant_cusp
    (hDiscCusp : KleinDiscriminantIdentityCusp) :
    KleinBfunExtDeltaIdentityCusp :=
  (kleinDiscriminantIdentityCusp_iff_kleinBfunExtDeltaIdentityCusp).1 hDiscCusp

theorem kleinDiscriminantIdentityCusp_of_kleinBfunExtDeltaIdentityCusp
    (hB : KleinBfunExtDeltaIdentityCusp) :
    KleinDiscriminantIdentityCusp :=
  (kleinDiscriminantIdentityCusp_iff_kleinBfunExtDeltaIdentityCusp).2 hB

theorem kleinDiscriminantIdentity_iff_kleinBfunExtDeltaIdentityOnPuncturedUnitDisk :
    KleinDiscriminantIdentity ↔ KleinBfunExtDeltaIdentityOnPuncturedUnitDisk := by
  constructor
  · intro hGlobal
    exact
      kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_of_discriminant_puncturedUnitDisk
        ((kleinDiscriminantIdentity_iff_puncturedUnitDisk).1 hGlobal)
  · intro hB
    exact
      (kleinDiscriminantIdentity_iff_puncturedUnitDisk).2
        (kleinDiscriminantIdentityOnPuncturedUnitDisk_of_kleinBfunExtDeltaIdentityOnPuncturedUnitDisk hB)

theorem kleinDiscriminantIdentity_iff_etaIdentity :
    KleinDiscriminantIdentity ↔
      (∀ τ : ℍ, kleinDenom τ = (1728 : ℂ) * (eta τ) ^ (24 : Nat)) := by
  constructor
  · intro hDisc τ
    simpa [Delta] using hDisc τ
  · intro hEta τ
    simpa [Delta] using hEta τ

theorem kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_iff_etaIdentity :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk ↔
      (∀ τ : ℍ, kleinDenom τ = (1728 : ℂ) * (eta τ) ^ (24 : Nat)) := by
  calc
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk ↔ KleinDiscriminantIdentity := by
      exact (kleinDiscriminantIdentity_iff_kleinBfunExtDeltaIdentityOnPuncturedUnitDisk).symm
    _ ↔ (∀ τ : ℍ, kleinDenom τ = (1728 : ℂ) * (eta τ) ^ (24 : Nat)) := by
      exact kleinDiscriminantIdentity_iff_etaIdentity

theorem kleinDiscriminantIdentity_iff_eisensteinEtaIdentity :
    KleinDiscriminantIdentity ↔
      (∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) = (1728 : ℂ) * (eta τ) ^ (24 : Nat)) := by
  constructor
  · intro hDisc τ
    simpa [kleinDenom] using (kleinDiscriminantIdentity_iff_etaIdentity.1 hDisc τ)
  · intro hEta
    refine (kleinDiscriminantIdentity_iff_etaIdentity.2 ?_)
    intro τ
    simpa [kleinDenom] using hEta τ

theorem kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_iff_eisensteinEtaIdentity :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk ↔
      (∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) = (1728 : ℂ) * (eta τ) ^ (24 : Nat)) := by
  calc
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk ↔ KleinDiscriminantIdentity := by
      exact (kleinDiscriminantIdentity_iff_kleinBfunExtDeltaIdentityOnPuncturedUnitDisk).symm
    _ ↔ (∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) = (1728 : ℂ) * (eta τ) ^ (24 : Nat)) := by
      exact kleinDiscriminantIdentity_iff_eisensteinEtaIdentity

theorem kleinDiscriminantIdentity_of_kleinBfunExtDeltaIdentityOnPuncturedUnitDisk
    (hB : KleinBfunExtDeltaIdentityOnPuncturedUnitDisk) :
    KleinDiscriminantIdentity :=
  (kleinDiscriminantIdentity_iff_kleinBfunExtDeltaIdentityOnPuncturedUnitDisk).2 hB

theorem kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_of_discriminant_identity
    (hDisc : KleinDiscriminantIdentity) :
    KleinBfunExtDeltaIdentityOnPuncturedUnitDisk :=
  (kleinDiscriminantIdentity_iff_kleinBfunExtDeltaIdentityOnPuncturedUnitDisk).1 hDisc

theorem kleinDiscriminantIdentity_of_kleinBfunExtDeltaIdentityCusp
    (hB : KleinBfunExtDeltaIdentityCusp) :
    KleinDiscriminantIdentity :=
  (kleinDiscriminantIdentity_iff_cusp).2
    ((kleinDiscriminantIdentityCusp_iff_kleinBfunExtDeltaIdentityCusp).2 hB)

theorem kleinBfunExtDeltaIdentityCusp_of_discriminant_identity
    (hDisc : KleinDiscriminantIdentity) :
    KleinBfunExtDeltaIdentityCusp :=
  (kleinDiscriminantIdentityCusp_iff_kleinBfunExtDeltaIdentityCusp).1
    ((kleinDiscriminantIdentity_iff_cusp).1 hDisc)

theorem kleinDiscriminantIdentity_iff_kleinBfunExtDeltaIdentityCusp :
    KleinDiscriminantIdentity ↔ KleinBfunExtDeltaIdentityCusp := by
  constructor
  · exact kleinBfunExtDeltaIdentityCusp_of_discriminant_identity
  · exact kleinDiscriminantIdentity_of_kleinBfunExtDeltaIdentityCusp

theorem kleinBfunExtDeltaIdentityCusp_iff_etaIdentity :
    KleinBfunExtDeltaIdentityCusp ↔
      (∀ τ : ℍ, kleinDenom τ = (1728 : ℂ) * (eta τ) ^ (24 : Nat)) := by
  calc
    KleinBfunExtDeltaIdentityCusp ↔ KleinDiscriminantIdentity := by
      exact (kleinDiscriminantIdentity_iff_kleinBfunExtDeltaIdentityCusp).symm
    _ ↔ (∀ τ : ℍ, kleinDenom τ = (1728 : ℂ) * (eta τ) ^ (24 : Nat)) := by
      exact kleinDiscriminantIdentity_iff_etaIdentity

theorem kleinBfunExtDeltaIdentityCusp_iff_eisensteinEtaIdentity :
    KleinBfunExtDeltaIdentityCusp ↔
      (∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) = (1728 : ℂ) * (eta τ) ^ (24 : Nat)) := by
  calc
    KleinBfunExtDeltaIdentityCusp ↔ KleinDiscriminantIdentity := by
      exact (kleinDiscriminantIdentity_iff_kleinBfunExtDeltaIdentityCusp).symm
    _ ↔ (∀ τ : ℍ, (E4 τ) ^ (3 : Nat) - (E6 τ) ^ (2 : Nat) = (1728 : ℂ) * (eta τ) ^ (24 : Nat)) := by
      exact kleinDiscriminantIdentity_iff_eisensteinEtaIdentity

theorem kleinBfunExtDeltaIdentityOnUnitDisk_of_discriminant_unitDisk
    (hDisk : KleinDiscriminantIdentityOnUnitDisk) :
    KleinBfunExtDeltaIdentityOnUnitDisk := by
  intro q hq hq0
  have hD : kleinDfun q = (1728 : ℂ) * Delta_cusp q := hDisk q hq
  calc
    kleinBfunExt q = q⁻¹ * kleinDfun q := by
      simpa using (kleinBfunExt_eq_div (q := q) hq0)
    _ = q⁻¹ * ((1728 : ℂ) * Delta_cusp q) := by rw [hD]
    _ = (1728 : ℂ) * q⁻¹ * Delta_cusp q := by ring

theorem kleinDenom_ne_zero_global_of_kleinBfunExtDeltaIdentityOnUnitDisk
    (hB : KleinBfunExtDeltaIdentityOnUnitDisk) :
    ∀ τ : ℍ, kleinDenom τ ≠ 0 := by
  intro τ
  have hq : ‖q τ‖ < 1 := norm_q_lt_one τ
  have hq0 : q τ ≠ 0 := q_ne_zero τ
  have hDelta : Delta_cusp (q τ) ≠ 0 :=
    Delta_cusp_ne_zero_of_norm_lt_one_of_ne_zero (q := q τ) hq hq0
  have hBnon : kleinBfunExt (q τ) ≠ 0 := by
    rw [hB (q τ) hq hq0]
    have hInv : (q τ)⁻¹ ≠ 0 := inv_ne_zero hq0
    exact mul_ne_zero (mul_ne_zero (by norm_num) hInv) hDelta
  exact (kleinDenom_ne_zero_iff_kleinBfunExt_ne_zero (τ := τ)).2 hBnon

theorem kleinDenom_ne_zero_global_of_kleinBfunExtDeltaIdentityOnPuncturedUnitDisk
    (hB : KleinBfunExtDeltaIdentityOnPuncturedUnitDisk) :
    ∀ τ : ℍ, kleinDenom τ ≠ 0 :=
  kleinDenom_ne_zero_global_of_kleinBfunExtDeltaIdentityOnUnitDisk
    ((kleinBfunExtDeltaIdentityOnPuncturedUnitDisk_iff_unitDisk).1 hB)

theorem kleinDenom_ne_zero_global_of_kleinBfunExtDeltaIdentityCusp
    (hB : KleinBfunExtDeltaIdentityCusp) :
    ∀ τ : ℍ, kleinDenom τ ≠ 0 :=
  kleinDenom_ne_zero_global_of_kleinBfunExtDeltaIdentityOnPuncturedUnitDisk
    ((kleinBfunExtDeltaIdentityCusp_iff_puncturedUnitDisk).1 hB)

theorem kleinDenom_ne_zero_global_of_discriminant_unitDisk
    (hDisk : KleinDiscriminantIdentityOnUnitDisk) :
    ∀ τ : ℍ, kleinDenom τ ≠ 0 :=
  kleinDenom_ne_zero_global_of_kleinBfunExtDeltaIdentityOnUnitDisk
    (kleinBfunExtDeltaIdentityOnUnitDisk_of_discriminant_unitDisk hDisk)

theorem kleinDenom_ne_zero_global_of_discriminant_punctured_unitDisk
    (hPunct : KleinDiscriminantIdentityOnPuncturedUnitDisk) :
    ∀ τ : ℍ, kleinDenom τ ≠ 0 := by
  intro τ
  have hq : ‖q τ‖ < 1 := norm_q_lt_one τ
  have hq0 : q τ ≠ 0 := q_ne_zero τ
  have hDisc : kleinDfun (q τ) = (1728 : ℂ) * Delta_cusp (q τ) := hPunct (q τ) hq hq0
  calc
    kleinDenom τ = kleinDfun (q τ) := kleinDenom_eq_kleinDfun (τ := τ)
    _ = (1728 : ℂ) * Delta_cusp (q τ) := hDisc
    _ ≠ 0 := by
      exact mul_ne_zero (by norm_num)
        (Delta_cusp_ne_zero_of_norm_lt_one_of_ne_zero (q := q τ) hq hq0)

theorem kleinDenom_ne_zero_global_of_discriminant_identity
    (hDisc : KleinDiscriminantIdentity) :
    ∀ τ : ℍ, kleinDenom τ ≠ 0 := by
  intro τ
  rw [hDisc τ]
  exact mul_ne_zero (by norm_num) (Delta_ne_zero τ)

theorem kleinDenom_ne_zero_on_fd_of_discriminant_identity
    (hDisc : KleinDiscriminantIdentity)
    (τ : ℍ) (_hτ : τ ∈ ModularGroup.fd) :
    kleinDenom τ ≠ 0 := by
  exact kleinDenom_ne_zero_global_of_discriminant_identity hDisc τ

theorem kleinDenom_ne_zero_global_of_cusp_discriminant_identity
    (hDiscCusp : KleinDiscriminantIdentityCusp) :
    ∀ τ : ℍ, kleinDenom τ ≠ 0 :=
  kleinDenom_ne_zero_global_of_discriminant_identity
    (kleinDiscriminantIdentity_of_cusp hDiscCusp)

theorem kleinDenom_ne_zero_on_fd_of_cusp_discriminant_identity
    (hDiscCusp : KleinDiscriminantIdentityCusp)
    (τ : ℍ) (_hτ : τ ∈ ModularGroup.fd) :
    kleinDenom τ ≠ 0 := by
  exact kleinDenom_ne_zero_global_of_cusp_discriminant_identity hDiscCusp τ

theorem kleinDenom_ne_zero_on_fd_of_kleinBfunExtDeltaIdentityCusp
    (hB : KleinBfunExtDeltaIdentityCusp)
    (τ : ℍ) (_hτ : τ ∈ ModularGroup.fd) :
    kleinDenom τ ≠ 0 := by
  exact kleinDenom_ne_zero_global_of_kleinBfunExtDeltaIdentityCusp hB τ

end HeytingLean.Moonshine.Modular
