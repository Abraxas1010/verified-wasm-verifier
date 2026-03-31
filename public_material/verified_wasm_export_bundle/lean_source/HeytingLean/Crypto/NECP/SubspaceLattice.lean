import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Span.Basic

namespace HeytingLean
namespace Crypto
namespace NECP
namespace SubspaceLattice

abbrev Bit := ZMod 2
abbrev Plane := Fin 2 → Bit

def xVec : Plane := fun i => if i = 0 then 1 else 0
def yVec : Plane := fun i => if i = 1 then 1 else 0
def diagVec : Plane := fun _ => 1

def X : Submodule Bit Plane where
  carrier := {x | x 1 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change (x + y) 1 = 0
    rw [Pi.add_apply, hx, hy, add_zero]
  smul_mem' := by
    intro a x hx
    change (a • x) 1 = 0
    rw [Pi.smul_apply, hx, smul_zero]

def Y : Submodule Bit Plane where
  carrier := {x | x 0 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change (x + y) 0 = 0
    rw [Pi.add_apply, hx, hy, add_zero]
  smul_mem' := by
    intro a x hx
    change (a • x) 0 = 0
    rw [Pi.smul_apply, hx, smul_zero]

def D : Submodule Bit Plane where
  carrier := {x | x 0 = x 1}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change (x + y) 0 = (x + y) 1
    rw [Pi.add_apply, Pi.add_apply, hx, hy]
  smul_mem' := by
    intro a x hx
    change (a • x) 0 = (a • x) 1
    rw [Pi.smul_apply, Pi.smul_apply, hx]

@[simp] theorem mem_X {x : Plane} : x ∈ X ↔ x 1 = 0 :=
  Iff.rfl

@[simp] theorem mem_Y {x : Plane} : x ∈ Y ↔ x 0 = 0 :=
  Iff.rfl

@[simp] theorem mem_D {x : Plane} : x ∈ D ↔ x 0 = x 1 :=
  Iff.rfl

@[simp] theorem xVec_mem_X : xVec ∈ X := by
  simp [xVec, X]

@[simp] theorem yVec_mem_Y : yVec ∈ Y := by
  simp [yVec, Y]

@[simp] theorem diagVec_mem_D : diagVec ∈ D := by
  simp [diagVec, D]

theorem xVec_ne_zero : xVec ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [xVec] at h0

theorem yVec_ne_zero : yVec ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  simp [yVec] at h1

theorem yVec_not_mem_X : yVec ∉ X := by
  simp [yVec, X]

theorem X_ne_bot : X ≠ ⊥ := by
  intro h
  have hx : xVec ∈ (⊥ : Submodule Bit Plane) := by
    simpa [h] using xVec_mem_X
  simp [xVec_ne_zero] at hx

theorem X_ne_top : X ≠ ⊤ := by
  intro h
  have hy : yVec ∈ X := by
    rw [h]
    simp
  exact yVec_not_mem_X hy

instance : IsModularLattice (Submodule Bit Plane) := inferInstance

theorem X_inf_Y_eq_bot : X ⊓ Y = ⊥ := by
  apply le_antisymm
  · intro x hx
    have h0 : x 0 = 0 := hx.2
    have h1 : x 1 = 0 := hx.1
    have hx0 : x = 0 := by
      funext i
      fin_cases i <;> simp [h0, h1]
    simp [hx0]
  · exact bot_le

theorem X_inf_D_eq_bot : X ⊓ D = ⊥ := by
  apply le_antisymm
  · intro x hx
    have h1 : x 1 = 0 := hx.1
    have h0' : x 0 = x 1 := hx.2
    have h0 : x 0 = 0 := by simpa [h1] using h0'
    have hx0 : x = 0 := by
      funext i
      fin_cases i <;> simp [h0, h1]
    simp [hx0]
  · exact bot_le

theorem Y_inf_D_eq_bot : Y ⊓ D = ⊥ := by
  apply le_antisymm
  · intro x hx
    have h0 : x 0 = 0 := hx.1
    have h0' : x 0 = x 1 := hx.2
    have h1 : x 1 = 0 := by simpa [h0] using h0'.symm
    have hx0 : x = 0 := by
      funext i
      fin_cases i <;> simp [h0, h1]
    simp [hx0]
  · exact bot_le

theorem X_sup_Y_eq_top : X ⊔ Y = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  refine Submodule.mem_sup.2 ?_
  refine ⟨fun i => if i = 0 then x 0 else 0, ?_, fun i => if i = 1 then x 1 else 0, ?_, ?_⟩
  · simp [X]
  · simp [Y]
  · funext i
    fin_cases i <;> simp

theorem X_sup_D_eq_top : X ⊔ D = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  refine Submodule.mem_sup.2 ?_
  refine ⟨(x 0 + x 1) • xVec, ?_, x 1 • diagVec, ?_, ?_⟩
  · exact X.smul_mem (x 0 + x 1) xVec_mem_X
  · exact D.smul_mem (x 1) diagVec_mem_D
  · funext i
    fin_cases i
    · have hcancel : x 1 + x 1 = 0 := by
        calc
          x 1 + x 1 = x 1 - x 1 := by rw [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
          _ = 0 := sub_self _
      calc
        ((x 0 + x 1) • xVec + x 1 • diagVec) 0 = (x 0 + x 1) + x 1 := by
          simp [xVec, diagVec]
        _ = x 0 + (x 1 + x 1) := by rw [add_assoc]
        _ = x 0 := by rw [hcancel, add_zero]
    · simp [xVec, diagVec, add_comm]

theorem Y_sup_D_eq_top : Y ⊔ D = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  refine Submodule.mem_sup.2 ?_
  refine ⟨(x 1 + x 0) • yVec, ?_, x 0 • diagVec, ?_, ?_⟩
  · exact Y.smul_mem (x 1 + x 0) yVec_mem_Y
  · exact D.smul_mem (x 0) diagVec_mem_D
  · funext i
    fin_cases i
    · simp [yVec, diagVec, add_comm]
    · have hcancel : x 0 + x 0 = 0 := by
        calc
          x 0 + x 0 = x 0 - x 0 := by rw [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
          _ = 0 := sub_self _
      calc
        ((x 1 + x 0) • yVec + x 0 • diagVec) 1 = (x 1 + x 0) + x 0 := by
          simp [yVec, diagVec]
        _ = x 1 + (x 0 + x 0) := by rw [add_assoc]
        _ = x 1 := by rw [hcancel, add_zero]

theorem meet_sup_distrib_failure :
    X ⊓ (Y ⊔ D) ≠ (X ⊓ Y) ⊔ (X ⊓ D) := by
  simp [Y_sup_D_eq_top, X_inf_Y_eq_bot, X_inf_D_eq_bot, X_ne_bot]

def projX : Plane →ₗ[Bit] Plane where
  toFun x := fun i => if i = 0 then x 0 else 0
  map_add' x y := by
    funext i
    fin_cases i <;> simp
  map_smul' a x := by
    funext i
    fin_cases i <;> simp

@[simp] theorem projX_apply_zero (x : Plane) :
    projX x 0 = x 0 := by
  simp [projX]

@[simp] theorem projX_apply_one (x : Plane) :
    projX x 1 = 0 := by
  simp [projX]

theorem projX_range_eq_X : LinearMap.range projX = X := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    simp [X, projX]
  · intro x hx
    refine ⟨x, ?_⟩
    funext i
    fin_cases i
    · simp [projX]
    · simp [projX, mem_X.mp hx]

end SubspaceLattice
end NECP
end Crypto
end HeytingLean
