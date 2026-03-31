import HeytingLean.Crypto.NECP.DivisorLattice
import HeytingLean.Crypto.NECP.LinearClosure

namespace HeytingLean
namespace Crypto
namespace NECP

open PrimePowerDivisor

universe u

/-- Coordinate flag space used to embed the prime-power divisor chain into subspaces. -/
abbrev FlagSpace (k : Nat) (F : Type u) := Fin k → F

section

variable {F : Type u} [Field F] {k : Nat}

/-- The `m`-th coordinate flag: vectors supported on the first `m` coordinates. -/
def flagSubmodule (m : PrimePowerDivisor k) : Submodule F (FlagSpace k F) where
  carrier := {x | ∀ i : Fin k, m.1 ≤ i.1 → x i = 0}
  zero_mem' := by
    intro i hi
    simp
  add_mem' := by
    intro x y hx hy i hi
    simp [hx i hi, hy i hi]
  smul_mem' := by
    intro a x hx i hi
    simp [hx i hi]

@[simp] theorem mem_flagSubmodule {m : PrimePowerDivisor k} {x : FlagSpace k F} :
    x ∈ flagSubmodule m ↔ ∀ i : Fin k, m.1 ≤ i.1 → x i = 0 :=
  Iff.rfl

theorem flagSubmodule_mono {a b : PrimePowerDivisor k} (h : a ≤ b) :
    flagSubmodule (F := F) a ≤ flagSubmodule (F := F) b := by
  intro x hx i hi
  exact hx i (le_trans h hi)

/-- Truncation to the first `m` coordinates. -/
def truncate (m : PrimePowerDivisor k) : FlagSpace k F →ₗ[F] FlagSpace k F where
  toFun x := fun i => if i.1 < m.1 then x i else 0
  map_add' x y := by
    funext i
    by_cases hi : i.1 < m.1 <;> simp [hi]
  map_smul' a x := by
    funext i
    by_cases hi : i.1 < m.1 <;> simp [hi]

theorem truncate_eq_self_of_mem_flag {m : PrimePowerDivisor k} {x : FlagSpace k F}
    (hx : x ∈ flagSubmodule (F := F) m) :
    truncate m x = x := by
  funext i
  by_cases hi : i.1 < m.1
  · simp [truncate, hi]
  · have hm : m.1 ≤ i.1 := Nat.le_of_not_gt hi
    simp [truncate, hi, hx i hm]

theorem truncate_range_eq_flag (m : PrimePowerDivisor k) :
    LinearMap.range (truncate m) = flagSubmodule (F := F) m := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    intro i hi
    have hnot : ¬ i.1 < m.1 := Nat.not_lt.mpr hi
    simp [truncate, hnot]
  · intro x hx
    refine ⟨x, ?_⟩
    exact truncate_eq_self_of_mem_flag hx

theorem flagSup_eq_max (a b : PrimePowerDivisor k) :
    flagSubmodule (F := F) a ⊔ flagSubmodule (F := F) b = flagSubmodule (F := F) (max a b) := by
  rcases le_total a b with hab | hba
  · have hle : flagSubmodule (F := F) a ≤ flagSubmodule (F := F) b := flagSubmodule_mono hab
    rw [max_eq_right hab, sup_eq_right.mpr hle]
  · have hle : flagSubmodule (F := F) b ≤ flagSubmodule (F := F) a := flagSubmodule_mono hba
    rw [max_eq_left hba, sup_eq_left.mpr hle]

theorem ladmini_is_necp_special_case
    (threshold e : PrimePowerDivisor k) :
    linearClosure (R := F) (M := FlagSpace k F) (truncate threshold) (flagSubmodule (F := F) e) =
      flagSubmodule (F := F) (divisorClosure threshold e) := by
  calc
    linearClosure (R := F) (M := FlagSpace k F) (truncate threshold) (flagSubmodule (F := F) e)
        = flagSubmodule (F := F) e ⊔ LinearMap.range (truncate threshold) := by
            rfl
    _ = flagSubmodule (F := F) e ⊔ flagSubmodule (F := F) threshold := by
          rw [truncate_range_eq_flag]
    _ = flagSubmodule (F := F) (divisorClosure threshold e) := by
          simpa [PrimePowerDivisor.divisorClosure, max_comm] using flagSup_eq_max e threshold

end

end NECP
end Crypto
end HeytingLean
