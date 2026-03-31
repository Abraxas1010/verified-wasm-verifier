import Mathlib

set_option linter.unusedSimpArgs false

namespace HeytingLean.External.Teorth.MagmaCompat

section Base
variable {α : Type*}

theorem magma_eqn_1_base (x : α) : x = x := by
  rfl

end Base

section Sup
variable {α : Type*} [SemilatticeSup α]

theorem magma_eqn_3_sup (x : α) : x = (x ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_8_sup (x : α) : x = (x ⊔ (x ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_23_sup (x : α) : x = ((x ⊔ x) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_43_sup (x y : α) : (x ⊔ y) = (y ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_47_sup (x : α) : x = (x ⊔ (x ⊔ (x ⊔ x))) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_99_sup (x : α) : x = (x ⊔ ((x ⊔ x) ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_151_sup (x : α) : x = ((x ⊔ x) ⊔ (x ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_203_sup (x : α) : x = ((x ⊔ (x ⊔ x)) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_255_sup (x : α) : x = (((x ⊔ x) ⊔ x) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_307_sup (x : α) : (x ⊔ x) = (x ⊔ (x ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_323_sup (x y : α) : (x ⊔ y) = (x ⊔ (x ⊔ y)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_325_sup (x y : α) : (x ⊔ y) = (x ⊔ (y ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_326_sup (x y : α) : (x ⊔ y) = (x ⊔ (y ⊔ y)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_332_sup (x y : α) : (x ⊔ y) = (y ⊔ (x ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_333_sup (x y : α) : (x ⊔ y) = (y ⊔ (x ⊔ y)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_335_sup (x y : α) : (x ⊔ y) = (y ⊔ (y ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_359_sup (x : α) : (x ⊔ x) = ((x ⊔ x) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_375_sup (x y : α) : (x ⊔ y) = ((x ⊔ x) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_377_sup (x y : α) : (x ⊔ y) = ((x ⊔ y) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_378_sup (x y : α) : (x ⊔ y) = ((x ⊔ y) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_384_sup (x y : α) : (x ⊔ y) = ((y ⊔ x) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_385_sup (x y : α) : (x ⊔ y) = ((y ⊔ x) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_387_sup (x y : α) : (x ⊔ y) = ((y ⊔ y) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_411_sup (x : α) : x = (x ⊔ (x ⊔ (x ⊔ (x ⊔ x)))) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_614_sup (x : α) : x = (x ⊔ (x ⊔ ((x ⊔ x) ⊔ x))) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_817_sup (x : α) : x = (x ⊔ ((x ⊔ x) ⊔ (x ⊔ x))) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_1020_sup (x : α) : x = (x ⊔ ((x ⊔ (x ⊔ x)) ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_1223_sup (x : α) : x = (x ⊔ (((x ⊔ x) ⊔ x) ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_1426_sup (x : α) : x = ((x ⊔ x) ⊔ (x ⊔ (x ⊔ x))) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_1629_sup (x : α) : x = ((x ⊔ x) ⊔ ((x ⊔ x) ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_1832_sup (x : α) : x = ((x ⊔ (x ⊔ x)) ⊔ (x ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_2035_sup (x : α) : x = (((x ⊔ x) ⊔ x) ⊔ (x ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_2238_sup (x : α) : x = ((x ⊔ (x ⊔ (x ⊔ x))) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_2441_sup (x : α) : x = ((x ⊔ ((x ⊔ x) ⊔ x)) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_2644_sup (x : α) : x = (((x ⊔ x) ⊔ (x ⊔ x)) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_2847_sup (x : α) : x = (((x ⊔ (x ⊔ x)) ⊔ x) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3050_sup (x : α) : x = ((((x ⊔ x) ⊔ x) ⊔ x) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3253_sup (x : α) : (x ⊔ x) = (x ⊔ (x ⊔ (x ⊔ x))) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3306_sup (x y : α) : (x ⊔ y) = (x ⊔ (x ⊔ (x ⊔ y))) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3308_sup (x y : α) : (x ⊔ y) = (x ⊔ (x ⊔ (y ⊔ x))) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3309_sup (x y : α) : (x ⊔ y) = (x ⊔ (x ⊔ (y ⊔ y))) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3315_sup (x y : α) : (x ⊔ y) = (x ⊔ (y ⊔ (x ⊔ x))) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3316_sup (x y : α) : (x ⊔ y) = (x ⊔ (y ⊔ (x ⊔ y))) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3318_sup (x y : α) : (x ⊔ y) = (x ⊔ (y ⊔ (y ⊔ x))) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3319_sup (x y : α) : (x ⊔ y) = (x ⊔ (y ⊔ (y ⊔ y))) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3342_sup (x y : α) : (x ⊔ y) = (y ⊔ (x ⊔ (x ⊔ x))) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3343_sup (x y : α) : (x ⊔ y) = (y ⊔ (x ⊔ (x ⊔ y))) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3345_sup (x y : α) : (x ⊔ y) = (y ⊔ (x ⊔ (y ⊔ x))) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3346_sup (x y : α) : (x ⊔ y) = (y ⊔ (x ⊔ (y ⊔ y))) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3352_sup (x y : α) : (x ⊔ y) = (y ⊔ (y ⊔ (x ⊔ x))) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3353_sup (x y : α) : (x ⊔ y) = (y ⊔ (y ⊔ (x ⊔ y))) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3355_sup (x y : α) : (x ⊔ y) = (y ⊔ (y ⊔ (y ⊔ x))) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3456_sup (x : α) : (x ⊔ x) = (x ⊔ ((x ⊔ x) ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3509_sup (x y : α) : (x ⊔ y) = (x ⊔ ((x ⊔ x) ⊔ y)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3511_sup (x y : α) : (x ⊔ y) = (x ⊔ ((x ⊔ y) ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3512_sup (x y : α) : (x ⊔ y) = (x ⊔ ((x ⊔ y) ⊔ y)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3518_sup (x y : α) : (x ⊔ y) = (x ⊔ ((y ⊔ x) ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3519_sup (x y : α) : (x ⊔ y) = (x ⊔ ((y ⊔ x) ⊔ y)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3521_sup (x y : α) : (x ⊔ y) = (x ⊔ ((y ⊔ y) ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3522_sup (x y : α) : (x ⊔ y) = (x ⊔ ((y ⊔ y) ⊔ y)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3545_sup (x y : α) : (x ⊔ y) = (y ⊔ ((x ⊔ x) ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3546_sup (x y : α) : (x ⊔ y) = (y ⊔ ((x ⊔ x) ⊔ y)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3548_sup (x y : α) : (x ⊔ y) = (y ⊔ ((x ⊔ y) ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3549_sup (x y : α) : (x ⊔ y) = (y ⊔ ((x ⊔ y) ⊔ y)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3555_sup (x y : α) : (x ⊔ y) = (y ⊔ ((y ⊔ x) ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3556_sup (x y : α) : (x ⊔ y) = (y ⊔ ((y ⊔ x) ⊔ y)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3558_sup (x y : α) : (x ⊔ y) = (y ⊔ ((y ⊔ y) ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3659_sup (x : α) : (x ⊔ x) = ((x ⊔ x) ⊔ (x ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3712_sup (x y : α) : (x ⊔ y) = ((x ⊔ x) ⊔ (x ⊔ y)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3714_sup (x y : α) : (x ⊔ y) = ((x ⊔ x) ⊔ (y ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3715_sup (x y : α) : (x ⊔ y) = ((x ⊔ x) ⊔ (y ⊔ y)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3721_sup (x y : α) : (x ⊔ y) = ((x ⊔ y) ⊔ (x ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3722_sup (x y : α) : (x ⊔ y) = ((x ⊔ y) ⊔ (x ⊔ y)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3724_sup (x y : α) : (x ⊔ y) = ((x ⊔ y) ⊔ (y ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3725_sup (x y : α) : (x ⊔ y) = ((x ⊔ y) ⊔ (y ⊔ y)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3748_sup (x y : α) : (x ⊔ y) = ((y ⊔ x) ⊔ (x ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3749_sup (x y : α) : (x ⊔ y) = ((y ⊔ x) ⊔ (x ⊔ y)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3751_sup (x y : α) : (x ⊔ y) = ((y ⊔ x) ⊔ (y ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3752_sup (x y : α) : (x ⊔ y) = ((y ⊔ x) ⊔ (y ⊔ y)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3758_sup (x y : α) : (x ⊔ y) = ((y ⊔ y) ⊔ (x ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3759_sup (x y : α) : (x ⊔ y) = ((y ⊔ y) ⊔ (x ⊔ y)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3761_sup (x y : α) : (x ⊔ y) = ((y ⊔ y) ⊔ (y ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3862_sup (x : α) : (x ⊔ x) = ((x ⊔ (x ⊔ x)) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3915_sup (x y : α) : (x ⊔ y) = ((x ⊔ (x ⊔ x)) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3917_sup (x y : α) : (x ⊔ y) = ((x ⊔ (x ⊔ y)) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3918_sup (x y : α) : (x ⊔ y) = ((x ⊔ (x ⊔ y)) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3924_sup (x y : α) : (x ⊔ y) = ((x ⊔ (y ⊔ x)) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3925_sup (x y : α) : (x ⊔ y) = ((x ⊔ (y ⊔ x)) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3927_sup (x y : α) : (x ⊔ y) = ((x ⊔ (y ⊔ y)) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3928_sup (x y : α) : (x ⊔ y) = ((x ⊔ (y ⊔ y)) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3951_sup (x y : α) : (x ⊔ y) = ((y ⊔ (x ⊔ x)) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3952_sup (x y : α) : (x ⊔ y) = ((y ⊔ (x ⊔ x)) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3954_sup (x y : α) : (x ⊔ y) = ((y ⊔ (x ⊔ y)) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3955_sup (x y : α) : (x ⊔ y) = ((y ⊔ (x ⊔ y)) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3961_sup (x y : α) : (x ⊔ y) = ((y ⊔ (y ⊔ x)) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3962_sup (x y : α) : (x ⊔ y) = ((y ⊔ (y ⊔ x)) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_3964_sup (x y : α) : (x ⊔ y) = ((y ⊔ (y ⊔ y)) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4065_sup (x : α) : (x ⊔ x) = (((x ⊔ x) ⊔ x) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4118_sup (x y : α) : (x ⊔ y) = (((x ⊔ x) ⊔ x) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4120_sup (x y : α) : (x ⊔ y) = (((x ⊔ x) ⊔ y) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4121_sup (x y : α) : (x ⊔ y) = (((x ⊔ x) ⊔ y) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4127_sup (x y : α) : (x ⊔ y) = (((x ⊔ y) ⊔ x) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4128_sup (x y : α) : (x ⊔ y) = (((x ⊔ y) ⊔ x) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4130_sup (x y : α) : (x ⊔ y) = (((x ⊔ y) ⊔ y) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4131_sup (x y : α) : (x ⊔ y) = (((x ⊔ y) ⊔ y) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4154_sup (x y : α) : (x ⊔ y) = (((y ⊔ x) ⊔ x) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4155_sup (x y : α) : (x ⊔ y) = (((y ⊔ x) ⊔ x) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4157_sup (x y : α) : (x ⊔ y) = (((y ⊔ x) ⊔ y) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4158_sup (x y : α) : (x ⊔ y) = (((y ⊔ x) ⊔ y) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4164_sup (x y : α) : (x ⊔ y) = (((y ⊔ y) ⊔ x) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4165_sup (x y : α) : (x ⊔ y) = (((y ⊔ y) ⊔ x) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4167_sup (x y : α) : (x ⊔ y) = (((y ⊔ y) ⊔ y) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4283_sup (x y : α) : (x ⊔ (x ⊔ y)) = (x ⊔ (y ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4284_sup (x y : α) : (x ⊔ (x ⊔ y)) = (x ⊔ (y ⊔ y)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4290_sup (x y : α) : (x ⊔ (x ⊔ y)) = (y ⊔ (x ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4291_sup (x y : α) : (x ⊔ (x ⊔ y)) = (y ⊔ (x ⊔ y)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4293_sup (x y : α) : (x ⊔ (x ⊔ y)) = (y ⊔ (y ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4314_sup (x y : α) : (x ⊔ (y ⊔ x)) = (x ⊔ (y ⊔ y)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4320_sup (x y : α) : (x ⊔ (y ⊔ x)) = (y ⊔ (x ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4321_sup (x y : α) : (x ⊔ (y ⊔ x)) = (y ⊔ (x ⊔ y)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4343_sup (x y : α) : (x ⊔ (y ⊔ y)) = (y ⊔ (x ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4358_sup (x y z : α) : (x ⊔ (y ⊔ z)) = (x ⊔ (z ⊔ y)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4362_sup (x y z : α) : (x ⊔ (y ⊔ z)) = (y ⊔ (x ⊔ z)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4364_sup (x y z : α) : (x ⊔ (y ⊔ z)) = (y ⊔ (z ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4369_sup (x y z : α) : (x ⊔ (y ⊔ z)) = (z ⊔ (y ⊔ x)) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4380_sup (x : α) : (x ⊔ (x ⊔ x)) = ((x ⊔ x) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4396_sup (x y : α) : (x ⊔ (x ⊔ y)) = ((x ⊔ x) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4398_sup (x y : α) : (x ⊔ (x ⊔ y)) = ((x ⊔ y) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4399_sup (x y : α) : (x ⊔ (x ⊔ y)) = ((x ⊔ y) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4405_sup (x y : α) : (x ⊔ (x ⊔ y)) = ((y ⊔ x) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4406_sup (x y : α) : (x ⊔ (x ⊔ y)) = ((y ⊔ x) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4408_sup (x y : α) : (x ⊔ (x ⊔ y)) = ((y ⊔ y) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4433_sup (x y : α) : (x ⊔ (y ⊔ x)) = ((x ⊔ x) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4435_sup (x y : α) : (x ⊔ (y ⊔ x)) = ((x ⊔ y) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4436_sup (x y : α) : (x ⊔ (y ⊔ x)) = ((x ⊔ y) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4442_sup (x y : α) : (x ⊔ (y ⊔ x)) = ((y ⊔ x) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4443_sup (x y : α) : (x ⊔ (y ⊔ x)) = ((y ⊔ x) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4445_sup (x y : α) : (x ⊔ (y ⊔ x)) = ((y ⊔ y) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4470_sup (x y : α) : (x ⊔ (y ⊔ y)) = ((x ⊔ x) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4472_sup (x y : α) : (x ⊔ (y ⊔ y)) = ((x ⊔ y) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4473_sup (x y : α) : (x ⊔ (y ⊔ y)) = ((x ⊔ y) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4479_sup (x y : α) : (x ⊔ (y ⊔ y)) = ((y ⊔ x) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4480_sup (x y : α) : (x ⊔ (y ⊔ y)) = ((y ⊔ x) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4482_sup (x y : α) : (x ⊔ (y ⊔ y)) = ((y ⊔ y) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4512_sup (x y z : α) : (x ⊔ (y ⊔ z)) = ((x ⊔ y) ⊔ z) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4515_sup (x y z : α) : (x ⊔ (y ⊔ z)) = ((x ⊔ z) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4525_sup (x y z : α) : (x ⊔ (y ⊔ z)) = ((y ⊔ x) ⊔ z) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4531_sup (x y z : α) : (x ⊔ (y ⊔ z)) = ((y ⊔ z) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4541_sup (x y z : α) : (x ⊔ (y ⊔ z)) = ((z ⊔ x) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4544_sup (x y z : α) : (x ⊔ (y ⊔ z)) = ((z ⊔ y) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4598_sup (x y : α) : ((x ⊔ x) ⊔ y) = ((x ⊔ y) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4599_sup (x y : α) : ((x ⊔ x) ⊔ y) = ((x ⊔ y) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4605_sup (x y : α) : ((x ⊔ x) ⊔ y) = ((y ⊔ x) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4606_sup (x y : α) : ((x ⊔ x) ⊔ y) = ((y ⊔ x) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4608_sup (x y : α) : ((x ⊔ x) ⊔ y) = ((y ⊔ y) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4629_sup (x y : α) : ((x ⊔ y) ⊔ x) = ((x ⊔ y) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4635_sup (x y : α) : ((x ⊔ y) ⊔ x) = ((y ⊔ x) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4636_sup (x y : α) : ((x ⊔ y) ⊔ x) = ((y ⊔ x) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4658_sup (x y : α) : ((x ⊔ y) ⊔ y) = ((y ⊔ x) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4673_sup (x y z : α) : ((x ⊔ y) ⊔ z) = ((x ⊔ z) ⊔ y) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4677_sup (x y z : α) : ((x ⊔ y) ⊔ z) = ((y ⊔ x) ⊔ z) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4679_sup (x y z : α) : ((x ⊔ y) ⊔ z) = ((y ⊔ z) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem magma_eqn_4684_sup (x y z : α) : ((x ⊔ y) ⊔ z) = ((z ⊔ y) ⊔ x) := by
  simp [sup_assoc, sup_comm, sup_left_comm, sup_idem]

end Sup

section Inf
variable {α : Type*} [SemilatticeInf α]

theorem magma_eqn_3_inf (x : α) : x = (x ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_8_inf (x : α) : x = (x ⊓ (x ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_23_inf (x : α) : x = ((x ⊓ x) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_43_inf (x y : α) : (x ⊓ y) = (y ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_47_inf (x : α) : x = (x ⊓ (x ⊓ (x ⊓ x))) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_99_inf (x : α) : x = (x ⊓ ((x ⊓ x) ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_151_inf (x : α) : x = ((x ⊓ x) ⊓ (x ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_203_inf (x : α) : x = ((x ⊓ (x ⊓ x)) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_255_inf (x : α) : x = (((x ⊓ x) ⊓ x) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_307_inf (x : α) : (x ⊓ x) = (x ⊓ (x ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_323_inf (x y : α) : (x ⊓ y) = (x ⊓ (x ⊓ y)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_325_inf (x y : α) : (x ⊓ y) = (x ⊓ (y ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_326_inf (x y : α) : (x ⊓ y) = (x ⊓ (y ⊓ y)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_332_inf (x y : α) : (x ⊓ y) = (y ⊓ (x ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_333_inf (x y : α) : (x ⊓ y) = (y ⊓ (x ⊓ y)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_335_inf (x y : α) : (x ⊓ y) = (y ⊓ (y ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_359_inf (x : α) : (x ⊓ x) = ((x ⊓ x) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_375_inf (x y : α) : (x ⊓ y) = ((x ⊓ x) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_377_inf (x y : α) : (x ⊓ y) = ((x ⊓ y) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_378_inf (x y : α) : (x ⊓ y) = ((x ⊓ y) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_384_inf (x y : α) : (x ⊓ y) = ((y ⊓ x) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_385_inf (x y : α) : (x ⊓ y) = ((y ⊓ x) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_387_inf (x y : α) : (x ⊓ y) = ((y ⊓ y) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_411_inf (x : α) : x = (x ⊓ (x ⊓ (x ⊓ (x ⊓ x)))) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_614_inf (x : α) : x = (x ⊓ (x ⊓ ((x ⊓ x) ⊓ x))) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_817_inf (x : α) : x = (x ⊓ ((x ⊓ x) ⊓ (x ⊓ x))) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_1020_inf (x : α) : x = (x ⊓ ((x ⊓ (x ⊓ x)) ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_1223_inf (x : α) : x = (x ⊓ (((x ⊓ x) ⊓ x) ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_1426_inf (x : α) : x = ((x ⊓ x) ⊓ (x ⊓ (x ⊓ x))) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_1629_inf (x : α) : x = ((x ⊓ x) ⊓ ((x ⊓ x) ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_1832_inf (x : α) : x = ((x ⊓ (x ⊓ x)) ⊓ (x ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_2035_inf (x : α) : x = (((x ⊓ x) ⊓ x) ⊓ (x ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_2238_inf (x : α) : x = ((x ⊓ (x ⊓ (x ⊓ x))) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_2441_inf (x : α) : x = ((x ⊓ ((x ⊓ x) ⊓ x)) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_2644_inf (x : α) : x = (((x ⊓ x) ⊓ (x ⊓ x)) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_2847_inf (x : α) : x = (((x ⊓ (x ⊓ x)) ⊓ x) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3050_inf (x : α) : x = ((((x ⊓ x) ⊓ x) ⊓ x) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3253_inf (x : α) : (x ⊓ x) = (x ⊓ (x ⊓ (x ⊓ x))) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3306_inf (x y : α) : (x ⊓ y) = (x ⊓ (x ⊓ (x ⊓ y))) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3308_inf (x y : α) : (x ⊓ y) = (x ⊓ (x ⊓ (y ⊓ x))) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3309_inf (x y : α) : (x ⊓ y) = (x ⊓ (x ⊓ (y ⊓ y))) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3315_inf (x y : α) : (x ⊓ y) = (x ⊓ (y ⊓ (x ⊓ x))) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3316_inf (x y : α) : (x ⊓ y) = (x ⊓ (y ⊓ (x ⊓ y))) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3318_inf (x y : α) : (x ⊓ y) = (x ⊓ (y ⊓ (y ⊓ x))) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3319_inf (x y : α) : (x ⊓ y) = (x ⊓ (y ⊓ (y ⊓ y))) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3342_inf (x y : α) : (x ⊓ y) = (y ⊓ (x ⊓ (x ⊓ x))) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3343_inf (x y : α) : (x ⊓ y) = (y ⊓ (x ⊓ (x ⊓ y))) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3345_inf (x y : α) : (x ⊓ y) = (y ⊓ (x ⊓ (y ⊓ x))) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3346_inf (x y : α) : (x ⊓ y) = (y ⊓ (x ⊓ (y ⊓ y))) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3352_inf (x y : α) : (x ⊓ y) = (y ⊓ (y ⊓ (x ⊓ x))) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3353_inf (x y : α) : (x ⊓ y) = (y ⊓ (y ⊓ (x ⊓ y))) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3355_inf (x y : α) : (x ⊓ y) = (y ⊓ (y ⊓ (y ⊓ x))) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3456_inf (x : α) : (x ⊓ x) = (x ⊓ ((x ⊓ x) ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3509_inf (x y : α) : (x ⊓ y) = (x ⊓ ((x ⊓ x) ⊓ y)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3511_inf (x y : α) : (x ⊓ y) = (x ⊓ ((x ⊓ y) ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3512_inf (x y : α) : (x ⊓ y) = (x ⊓ ((x ⊓ y) ⊓ y)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3518_inf (x y : α) : (x ⊓ y) = (x ⊓ ((y ⊓ x) ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3519_inf (x y : α) : (x ⊓ y) = (x ⊓ ((y ⊓ x) ⊓ y)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3521_inf (x y : α) : (x ⊓ y) = (x ⊓ ((y ⊓ y) ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3522_inf (x y : α) : (x ⊓ y) = (x ⊓ ((y ⊓ y) ⊓ y)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3545_inf (x y : α) : (x ⊓ y) = (y ⊓ ((x ⊓ x) ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3546_inf (x y : α) : (x ⊓ y) = (y ⊓ ((x ⊓ x) ⊓ y)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3548_inf (x y : α) : (x ⊓ y) = (y ⊓ ((x ⊓ y) ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3549_inf (x y : α) : (x ⊓ y) = (y ⊓ ((x ⊓ y) ⊓ y)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3555_inf (x y : α) : (x ⊓ y) = (y ⊓ ((y ⊓ x) ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3556_inf (x y : α) : (x ⊓ y) = (y ⊓ ((y ⊓ x) ⊓ y)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3558_inf (x y : α) : (x ⊓ y) = (y ⊓ ((y ⊓ y) ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3659_inf (x : α) : (x ⊓ x) = ((x ⊓ x) ⊓ (x ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3712_inf (x y : α) : (x ⊓ y) = ((x ⊓ x) ⊓ (x ⊓ y)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3714_inf (x y : α) : (x ⊓ y) = ((x ⊓ x) ⊓ (y ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3715_inf (x y : α) : (x ⊓ y) = ((x ⊓ x) ⊓ (y ⊓ y)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3721_inf (x y : α) : (x ⊓ y) = ((x ⊓ y) ⊓ (x ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3722_inf (x y : α) : (x ⊓ y) = ((x ⊓ y) ⊓ (x ⊓ y)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3724_inf (x y : α) : (x ⊓ y) = ((x ⊓ y) ⊓ (y ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3725_inf (x y : α) : (x ⊓ y) = ((x ⊓ y) ⊓ (y ⊓ y)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3748_inf (x y : α) : (x ⊓ y) = ((y ⊓ x) ⊓ (x ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3749_inf (x y : α) : (x ⊓ y) = ((y ⊓ x) ⊓ (x ⊓ y)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3751_inf (x y : α) : (x ⊓ y) = ((y ⊓ x) ⊓ (y ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3752_inf (x y : α) : (x ⊓ y) = ((y ⊓ x) ⊓ (y ⊓ y)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3758_inf (x y : α) : (x ⊓ y) = ((y ⊓ y) ⊓ (x ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3759_inf (x y : α) : (x ⊓ y) = ((y ⊓ y) ⊓ (x ⊓ y)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3761_inf (x y : α) : (x ⊓ y) = ((y ⊓ y) ⊓ (y ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3862_inf (x : α) : (x ⊓ x) = ((x ⊓ (x ⊓ x)) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3915_inf (x y : α) : (x ⊓ y) = ((x ⊓ (x ⊓ x)) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3917_inf (x y : α) : (x ⊓ y) = ((x ⊓ (x ⊓ y)) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3918_inf (x y : α) : (x ⊓ y) = ((x ⊓ (x ⊓ y)) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3924_inf (x y : α) : (x ⊓ y) = ((x ⊓ (y ⊓ x)) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3925_inf (x y : α) : (x ⊓ y) = ((x ⊓ (y ⊓ x)) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3927_inf (x y : α) : (x ⊓ y) = ((x ⊓ (y ⊓ y)) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3928_inf (x y : α) : (x ⊓ y) = ((x ⊓ (y ⊓ y)) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3951_inf (x y : α) : (x ⊓ y) = ((y ⊓ (x ⊓ x)) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3952_inf (x y : α) : (x ⊓ y) = ((y ⊓ (x ⊓ x)) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3954_inf (x y : α) : (x ⊓ y) = ((y ⊓ (x ⊓ y)) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3955_inf (x y : α) : (x ⊓ y) = ((y ⊓ (x ⊓ y)) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3961_inf (x y : α) : (x ⊓ y) = ((y ⊓ (y ⊓ x)) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3962_inf (x y : α) : (x ⊓ y) = ((y ⊓ (y ⊓ x)) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_3964_inf (x y : α) : (x ⊓ y) = ((y ⊓ (y ⊓ y)) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4065_inf (x : α) : (x ⊓ x) = (((x ⊓ x) ⊓ x) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4118_inf (x y : α) : (x ⊓ y) = (((x ⊓ x) ⊓ x) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4120_inf (x y : α) : (x ⊓ y) = (((x ⊓ x) ⊓ y) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4121_inf (x y : α) : (x ⊓ y) = (((x ⊓ x) ⊓ y) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4127_inf (x y : α) : (x ⊓ y) = (((x ⊓ y) ⊓ x) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4128_inf (x y : α) : (x ⊓ y) = (((x ⊓ y) ⊓ x) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4130_inf (x y : α) : (x ⊓ y) = (((x ⊓ y) ⊓ y) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4131_inf (x y : α) : (x ⊓ y) = (((x ⊓ y) ⊓ y) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4154_inf (x y : α) : (x ⊓ y) = (((y ⊓ x) ⊓ x) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4155_inf (x y : α) : (x ⊓ y) = (((y ⊓ x) ⊓ x) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4157_inf (x y : α) : (x ⊓ y) = (((y ⊓ x) ⊓ y) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4158_inf (x y : α) : (x ⊓ y) = (((y ⊓ x) ⊓ y) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4164_inf (x y : α) : (x ⊓ y) = (((y ⊓ y) ⊓ x) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4165_inf (x y : α) : (x ⊓ y) = (((y ⊓ y) ⊓ x) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4167_inf (x y : α) : (x ⊓ y) = (((y ⊓ y) ⊓ y) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4283_inf (x y : α) : (x ⊓ (x ⊓ y)) = (x ⊓ (y ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4284_inf (x y : α) : (x ⊓ (x ⊓ y)) = (x ⊓ (y ⊓ y)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4290_inf (x y : α) : (x ⊓ (x ⊓ y)) = (y ⊓ (x ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4291_inf (x y : α) : (x ⊓ (x ⊓ y)) = (y ⊓ (x ⊓ y)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4293_inf (x y : α) : (x ⊓ (x ⊓ y)) = (y ⊓ (y ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4314_inf (x y : α) : (x ⊓ (y ⊓ x)) = (x ⊓ (y ⊓ y)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4320_inf (x y : α) : (x ⊓ (y ⊓ x)) = (y ⊓ (x ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4321_inf (x y : α) : (x ⊓ (y ⊓ x)) = (y ⊓ (x ⊓ y)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4343_inf (x y : α) : (x ⊓ (y ⊓ y)) = (y ⊓ (x ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4358_inf (x y z : α) : (x ⊓ (y ⊓ z)) = (x ⊓ (z ⊓ y)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4362_inf (x y z : α) : (x ⊓ (y ⊓ z)) = (y ⊓ (x ⊓ z)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4364_inf (x y z : α) : (x ⊓ (y ⊓ z)) = (y ⊓ (z ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4369_inf (x y z : α) : (x ⊓ (y ⊓ z)) = (z ⊓ (y ⊓ x)) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4380_inf (x : α) : (x ⊓ (x ⊓ x)) = ((x ⊓ x) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4396_inf (x y : α) : (x ⊓ (x ⊓ y)) = ((x ⊓ x) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4398_inf (x y : α) : (x ⊓ (x ⊓ y)) = ((x ⊓ y) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4399_inf (x y : α) : (x ⊓ (x ⊓ y)) = ((x ⊓ y) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4405_inf (x y : α) : (x ⊓ (x ⊓ y)) = ((y ⊓ x) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4406_inf (x y : α) : (x ⊓ (x ⊓ y)) = ((y ⊓ x) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4408_inf (x y : α) : (x ⊓ (x ⊓ y)) = ((y ⊓ y) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4433_inf (x y : α) : (x ⊓ (y ⊓ x)) = ((x ⊓ x) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4435_inf (x y : α) : (x ⊓ (y ⊓ x)) = ((x ⊓ y) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4436_inf (x y : α) : (x ⊓ (y ⊓ x)) = ((x ⊓ y) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4442_inf (x y : α) : (x ⊓ (y ⊓ x)) = ((y ⊓ x) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4443_inf (x y : α) : (x ⊓ (y ⊓ x)) = ((y ⊓ x) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4445_inf (x y : α) : (x ⊓ (y ⊓ x)) = ((y ⊓ y) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4470_inf (x y : α) : (x ⊓ (y ⊓ y)) = ((x ⊓ x) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4472_inf (x y : α) : (x ⊓ (y ⊓ y)) = ((x ⊓ y) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4473_inf (x y : α) : (x ⊓ (y ⊓ y)) = ((x ⊓ y) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4479_inf (x y : α) : (x ⊓ (y ⊓ y)) = ((y ⊓ x) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4480_inf (x y : α) : (x ⊓ (y ⊓ y)) = ((y ⊓ x) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4482_inf (x y : α) : (x ⊓ (y ⊓ y)) = ((y ⊓ y) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4512_inf (x y z : α) : (x ⊓ (y ⊓ z)) = ((x ⊓ y) ⊓ z) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4515_inf (x y z : α) : (x ⊓ (y ⊓ z)) = ((x ⊓ z) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4525_inf (x y z : α) : (x ⊓ (y ⊓ z)) = ((y ⊓ x) ⊓ z) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4531_inf (x y z : α) : (x ⊓ (y ⊓ z)) = ((y ⊓ z) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4541_inf (x y z : α) : (x ⊓ (y ⊓ z)) = ((z ⊓ x) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4544_inf (x y z : α) : (x ⊓ (y ⊓ z)) = ((z ⊓ y) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4598_inf (x y : α) : ((x ⊓ x) ⊓ y) = ((x ⊓ y) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4599_inf (x y : α) : ((x ⊓ x) ⊓ y) = ((x ⊓ y) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4605_inf (x y : α) : ((x ⊓ x) ⊓ y) = ((y ⊓ x) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4606_inf (x y : α) : ((x ⊓ x) ⊓ y) = ((y ⊓ x) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4608_inf (x y : α) : ((x ⊓ x) ⊓ y) = ((y ⊓ y) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4629_inf (x y : α) : ((x ⊓ y) ⊓ x) = ((x ⊓ y) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4635_inf (x y : α) : ((x ⊓ y) ⊓ x) = ((y ⊓ x) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4636_inf (x y : α) : ((x ⊓ y) ⊓ x) = ((y ⊓ x) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4658_inf (x y : α) : ((x ⊓ y) ⊓ y) = ((y ⊓ x) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4673_inf (x y z : α) : ((x ⊓ y) ⊓ z) = ((x ⊓ z) ⊓ y) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4677_inf (x y z : α) : ((x ⊓ y) ⊓ z) = ((y ⊓ x) ⊓ z) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4679_inf (x y z : α) : ((x ⊓ y) ⊓ z) = ((y ⊓ z) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

theorem magma_eqn_4684_inf (x y z : α) : ((x ⊓ y) ⊓ z) = ((z ⊓ y) ⊓ x) := by
  simp [inf_assoc, inf_comm, inf_left_comm, inf_idem]

end Inf

end HeytingLean.External.Teorth.MagmaCompat
