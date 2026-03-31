import Mathlib.Data.Set.Lattice
import HeytingLean.LoF.Instances
import HeytingLean.LoF.Nucleus
import HeytingLean.Matula.Algebra.Lattice

namespace HeytingLean
namespace Matula
namespace Algebra
namespace MatulaNucleus

open HeytingLean.LoF
open Set
open scoped Classical

abbrev Carrier := Set PosNat

def onePos : PosNat := ⟨1, Nat.succ_pos 0⟩
def twoPos : PosNat := ⟨2, by decide⟩

def primordial : Carrier := {x | x = onePos}
def counter : Carrier := {x | x = twoPos}
def support : Carrier := primordial

/-- Phase II nucleus candidate: identity closure on `Set PosNat`. -/
noncomputable def nucleusCandidate : Nucleus Carrier := (⊥ : Nucleus Carrier)

@[simp] theorem nucleusCandidate_apply (S : Carrier) : nucleusCandidate S = S := rfl

/-- Matula-specific `Reentry` used to gate Phase III `RoundTrip` integration. -/
noncomputable def reentry : Reentry Carrier := by
  classical
  refine
    { nucleus := nucleusCandidate
      primordial := primordial
      counter := counter
      support := support
      primordial_mem := rfl
      counter_mem := rfl
      primordial_nonbot := ?_
      counter_nonbot := ?_
      orthogonal := ?_
      primordial_in_support := by
        intro x hx
        exact hx
      map_bot := rfl
      primordial_minimal := ?_ }
  · refine bot_lt_iff_ne_bot.mpr ?_
    intro h
    have hmem : onePos ∈ (⊥ : Carrier) := by
      have hPrim : onePos ∈ primordial := by simp [primordial]
      rw [← h]
      exact hPrim
    exact hmem.elim
  · refine bot_lt_iff_ne_bot.mpr ?_
    intro h
    have hmem : twoPos ∈ (⊥ : Carrier) := by
      have hCount : twoPos ∈ counter := by simp [counter]
      rw [← h]
      exact hCount
    exact hmem.elim
  · ext x
    constructor
    · intro hx
      rcases hx with ⟨hxP, hxC⟩
      have hxP' : x = onePos := by simpa [primordial] using hxP
      have hxC' : x = twoPos := by simpa [counter] using hxC
      have h12 : (1 : Nat) = 2 := by
        cases hxP'
        simpa [onePos, twoPos] using congrArg Subtype.val hxC'
      exact (by decide : (1 : Nat) ≠ 2) h12 |> False.elim
    · intro hx
      exact (False.elim hx)
  · intro x _hxFix hxPos hxSupport
    have hx_ne : x ≠ (⊥ : Carrier) := bot_lt_iff_ne_bot.mp hxPos
    have hx_nonempty : x.Nonempty := Set.nonempty_iff_ne_empty.mpr (by simpa using hx_ne)
    obtain ⟨w, hw⟩ := hx_nonempty
    have hw_one : w = onePos := by
      have : w ∈ support := hxSupport hw
      simpa [support, primordial] using this
    have hone : onePos ∈ x := by simpa [hw_one] using hw
    intro y hy
    have hy_one : y = onePos := by simpa [primordial] using hy
    subst hy_one
    simpa using hone

@[simp] theorem reentry_apply (S : Carrier) : reentry S = S := rfl

@[simp] theorem process_carrier :
    ((reentry.process : reentry.Omega) : Carrier) = primordial := rfl

@[simp] theorem counterProcess_carrier :
    ((reentry.counterProcess : reentry.Omega) : Carrier) = counter := rfl

@[simp] theorem eulerBoundary_carrier :
    ((reentry.eulerBoundary : reentry.Omega) : Carrier) = primordial := by
  simpa [Reentry.eulerBoundary_eq_process] using
    (process_carrier : ((reentry.process : reentry.Omega) : Carrier) = primordial)

end MatulaNucleus
end Algebra
end Matula
end HeytingLean
