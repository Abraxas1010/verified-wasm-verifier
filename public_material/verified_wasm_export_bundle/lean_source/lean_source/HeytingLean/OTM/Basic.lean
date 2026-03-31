import HeytingLean.Core.Nucleus
import HeytingLean.LoF.Nucleus
import HeytingLean.PerspectivalPlenum.DirectConnection
import HeytingLean.Topos.JRatchet

namespace HeytingLean
namespace OTM

universe u

/-- OTM-facing alias for the core nucleus interface. -/
abbrev RNucleus (α : Type u) [SemilatticeInf α] [OrderBot α] :=
  Core.Nucleus α

/-- OTM-facing alias for the LoF re-entry bundle. -/
abbrev ReentryCore (α : Type u) [LoF.PrimaryAlgebra α] :=
  LoF.Reentry α

/-- OTM-facing alias for the ratchet-step interface. -/
abbrev RatchetStepCore (α : Type u) [Order.Frame α] :=
  PerspectivalPlenum.RatchetStep α

/-- Abstract head movement token used by OTM transitions. -/
inductive HeadMove where
  | left
  | stay
  | right
  deriving DecidableEq, Repr

/-- Bundle a nucleus for direct OTM assembly use. -/
structure NucleusInterface (α : Type u) [SemilatticeInf α] [OrderBot α] where
  core : RNucleus α

namespace NucleusInterface

variable {α : Type u} [SemilatticeInf α] [OrderBot α]

/-- `x` is fixed by the nucleus. -/
def IsFixed (N : NucleusInterface α) (x : α) : Prop :=
  N.core.R x = x

@[simp] theorem isFixed_iff (N : NucleusInterface α) (x : α) :
    N.IsFixed x ↔ N.core.R x = x :=
  Iff.rfl

end NucleusInterface

/-- Bundle a re-entry object for OTM assembly use. -/
structure ReentryInterface (α : Type u) [LoF.PrimaryAlgebra α] where
  core : ReentryCore α

/-- Bundle a ratchet step together with a monotone level trajectory. -/
structure RatchetInterface (α : Type u) [Order.Frame α] where
  core : RatchetStepCore α
  level : Nat → Nat
  trajectory : Topos.JRatchet.RatchetTrajectory level

namespace RatchetInterface

variable {α : Type u} [Order.Frame α]

theorem level_monotone (R : RatchetInterface α) :
    ∀ fuel₁ fuel₂, fuel₁ ≤ fuel₂ → R.level fuel₁ ≤ R.level fuel₂ :=
  R.trajectory

/-- Convenience constructor from an existing ratchet step and level function. -/
def ofStep (step : RatchetStepCore α) (level : Nat → Nat)
    (htraj : Topos.JRatchet.RatchetTrajectory level) : RatchetInterface α :=
  { core := step, level := level, trajectory := htraj }

end RatchetInterface

end OTM
end HeytingLean
