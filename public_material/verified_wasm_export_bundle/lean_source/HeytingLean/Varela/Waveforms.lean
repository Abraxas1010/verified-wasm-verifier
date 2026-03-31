import HeytingLean.Varela.ECI

/-!
# Varela Waveforms

Temporal unfolding of re-entry gives alternating waveforms. The pointwise
crossing swaps the two phase-shifted oscillations, while the scoped `Diamond`
carrier records the classical four-valued “folded” view where `i` and `j` are
cross-fixed.
-/

namespace HeytingLean.Varela

open IndVal

abbrev Waveform := ℕ → IndVal

def waveI : Waveform := fun n =>
  if n % 2 = 0 then .marked else .unmarked

def waveJ : Waveform := fun n =>
  if n % 2 = 0 then .unmarked else .marked

def crossWave (w : Waveform) : Waveform := fun n => cross (w n)

theorem cross_waveI_eq_waveJ : crossWave waveI = waveJ := by
  ext n
  by_cases h : n % 2 = 0
  · simp [crossWave, waveI, waveJ, h, cross]
  · simp [crossWave, waveI, waveJ, h, cross]

theorem cross_waveJ_eq_waveI : crossWave waveJ = waveI := by
  ext n
  by_cases h : n % 2 = 0
  · simp [crossWave, waveI, waveJ, h, cross]
  · simp [crossWave, waveI, waveJ, h, cross]

/-- Folded four-valued layer used for the phase-shifted oscillations. -/
inductive Diamond : Type
  | m
  | n
  | i
  | j
  deriving DecidableEq, Repr

instance : Fintype Diamond where
  elems := {.m, .n, .i, .j}
  complete x := by
    cases x <;> simp

namespace Diamond

def cross : Diamond → Diamond
  | .m => .n
  | .n => .m
  | .i => .i
  | .j => .j

def prod : Diamond → Diamond → Diamond
  | .m, x => x
  | x, .m => x
  | .n, _ => .n
  | _, .n => .n
  | .i, .j => .m
  | .j, .i => .m
  | .i, .i => .i
  | .j, .j => .j

@[simp] theorem cross_m : cross .m = .n := rfl
@[simp] theorem cross_n : cross .n = .m := rfl
@[simp] theorem cross_i : cross .i = .i := rfl
@[simp] theorem cross_j : cross .j = .j := rfl

theorem diamond_cross_fixed_iff (x : Diamond) :
    cross x = x ↔ x = .i ∨ x = .j := by
  cases x <;> simp [cross]

@[simp] theorem prod_i_j : prod .i .j = .m := rfl
@[simp] theorem prod_j_i : prod .j .i = .m := rfl

end Diamond

end HeytingLean.Varela
