import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic

/-!
# Electron configuration (Aufbau model)

This is a *model* electron-configuration generator suitable for bookkeeping:
- deterministic
- computable (Nat-only)
- proven to conserve electron count

It is not intended to capture all experimentally observed ground-state exceptions.
Those can be layered later as an override table (with provenance).
-/

namespace HeytingLean
namespace Chem
namespace PeriodicTable

/-- Orbital angular-momentum labels used in chemistry. -/
inductive Orbital where
  | s | p | d | f
deriving DecidableEq, Repr

namespace Orbital

def capacity : Orbital → Nat
  | .s => 2
  | .p => 6
  | .d => 10
  | .f => 14

end Orbital

/-- A subshell label `(n, l)` with principal quantum number `n` and orbital label `l`. -/
structure Subshell where
  n : Nat
  l : Orbital
deriving DecidableEq, Repr

namespace Subshell

def capacity (s : Subshell) : Nat :=
  Orbital.capacity s.l

end Subshell

abbrev Configuration : Type := List (Subshell × Nat)

def electronCount (cfg : Configuration) : Nat :=
  match cfg with
  | [] => 0
  | p :: ps => p.2 + electronCount ps

@[simp] theorem electronCount_nil : electronCount [] = 0 := by
  rfl

@[simp] theorem electronCount_cons (p : Subshell × Nat) (ps : Configuration) :
    electronCount (p :: ps) = p.2 + electronCount ps := by
  rfl

/-- The standard Madelung/Aufbau subshell order sufficient for elements up to 118 (through 7p). -/
def aufbauOrder : List Subshell :=
  [ ⟨1, .s⟩
  , ⟨2, .s⟩, ⟨2, .p⟩
  , ⟨3, .s⟩, ⟨3, .p⟩
  , ⟨4, .s⟩, ⟨3, .d⟩, ⟨4, .p⟩
  , ⟨5, .s⟩, ⟨4, .d⟩, ⟨5, .p⟩
  , ⟨6, .s⟩, ⟨4, .f⟩, ⟨5, .d⟩, ⟨6, .p⟩
  , ⟨7, .s⟩, ⟨5, .f⟩, ⟨6, .d⟩, ⟨7, .p⟩
  ]

def fill (order : List Subshell) : Nat → Configuration
  | 0 => []
  | z + 1 =>
    match order with
    | [] => []
    | s :: ss =>
      let k := Nat.min s.capacity (z + 1)
      (s, k) :: fill ss ((z + 1) - k)

def modelConfiguration (Z : Nat) : Configuration :=
  fill aufbauOrder Z

def totalCapacity (order : List Subshell) : Nat :=
  match order with
  | [] => 0
  | s :: ss => s.capacity + totalCapacity ss

theorem electronCount_fill_of_le_totalCapacity (order : List Subshell) (Z : Nat)
    (hZ : Z ≤ totalCapacity order) :
    electronCount (fill order Z) = Z := by
  induction order generalizing Z with
  | nil =>
      -- totalCapacity [] = 0, so Z must be 0.
      have hZ0 : Z = 0 := Nat.eq_zero_of_le_zero (by simpa [totalCapacity] using hZ)
      subst hZ0
      simp [fill]
  | cons s ss ih =>
      cases Z with
      | zero =>
          simp [fill]
      | succ z =>
          -- Split on whether the head subshell absorbs all remaining electrons.
          let k : Nat := Nat.min s.capacity (Nat.succ z)
          by_cases hZcap : Nat.succ z ≤ s.capacity
          · -- Then `k = Z` and the remainder is 0.
            have hk : k = Nat.succ z := by
              simp [k, Nat.min_eq_right hZcap]
            simp [fill, k, hk]
          · -- Otherwise the subshell is filled to capacity: `k = cap`, and we use the IH on the remainder.
            have hcap_leZ : s.capacity ≤ Nat.succ z := Nat.le_of_not_ge hZcap
            have hk : k = s.capacity := by
              simp [k, Nat.min_eq_left hcap_leZ]
            have hRem : Nat.succ z - s.capacity ≤ totalCapacity ss := by
              -- From `Z ≤ cap + totalCapacity ss`, conclude `Z - cap ≤ totalCapacity ss`.
              have : Nat.succ z ≤ s.capacity + totalCapacity ss := by
                simpa [totalCapacity] using hZ
              exact (Nat.sub_le_iff_le_add).2 (by simpa [Nat.add_comm] using this)
            have ih' : electronCount (fill ss (Nat.succ z - s.capacity)) = (Nat.succ z - s.capacity) :=
              ih (Z := Nat.succ z - s.capacity) hRem
            simp [fill, k, hk, ih', Nat.add_sub_of_le hcap_leZ]

theorem totalCapacity_aufbauOrder : totalCapacity aufbauOrder = 118 := by
  decide

theorem electronCount_modelConfiguration_of_le (Z : Nat) (hZ : Z ≤ 118) :
    electronCount (modelConfiguration Z) = Z := by
  have hZ' : Z ≤ totalCapacity aufbauOrder := by
    simpa [totalCapacity_aufbauOrder] using hZ
  simpa [modelConfiguration] using electronCount_fill_of_le_totalCapacity aufbauOrder Z hZ'

end PeriodicTable
end Chem
end HeytingLean
