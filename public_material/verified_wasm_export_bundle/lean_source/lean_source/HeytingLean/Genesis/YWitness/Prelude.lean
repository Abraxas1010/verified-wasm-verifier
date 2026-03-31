import HeytingLean.Core.Nucleus
import HeytingLean.LoF.IntReentry
import HeytingLean.LoF.MRSystems.YBridge
import HeytingLean.Genesis.Stabilization
import HeytingLean.Genesis.WitnessInterior

namespace HeytingLean.Genesis.YWitness

open HeytingLean.Genesis

/-- A step-indexed witness process. -/
abbrev Stepwise (L : Type _) := Nat -> L

/-- The process starts at a specified seed. -/
def StartsAt {L : Type _} (seq : Stepwise L) (seed : L) : Prop :=
  seq 0 = seed

/-- The process genuinely changes at some adjacent step. -/
def AdjacentNonconstant {L : Type _} (seq : Stepwise L) : Prop :=
  Exists fun n => seq (n + 1) ≠ seq n

/-- Pointwise equality of witness processes. -/
def Follows {L : Type _} (lhs rhs : Stepwise L) : Prop :=
  forall n, lhs n = rhs n

@[simp] theorem follows_refl {L : Type _} (seq : Stepwise L) : Follows seq seq := by
  intro n
  rfl

theorem follows_symm {L : Type _} {lhs rhs : Stepwise L} (h : Follows lhs rhs) :
    Follows rhs lhs := by
  intro n
  exact (h n).symm

theorem follows_trans {L : Type _} {lhs mid rhs : Stepwise L}
    (h1 : Follows lhs mid) (h2 : Follows mid rhs) : Follows lhs rhs := by
  intro n
  exact (h1 n).trans (h2 n)

/-- The support-profile process extracted from an existing witness interior. -/
def witnessInteriorOscillation (W : WitnessInterior) : Stepwise Support :=
  fun n => supportProfile n W.source

@[simp] theorem witnessInteriorOscillation_zero (W : WitnessInterior) :
    witnessInteriorOscillation W 0 = supportProfile 0 W.source := rfl

theorem witnessInteriorOscillation_startsAt (W : WitnessInterior) :
    StartsAt (witnessInteriorOscillation W) (supportProfile 0 W.source) := by
  rfl

end HeytingLean.Genesis.YWitness
