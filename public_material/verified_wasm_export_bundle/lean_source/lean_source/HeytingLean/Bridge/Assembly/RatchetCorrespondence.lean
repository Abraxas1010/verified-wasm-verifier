import HeytingLean.ATheory.AssemblyCore
import HeytingLean.Topos.JRatchet

/-!
# Bridge.Assembly.RatchetCorrespondence

Constructive bridge exposing assembly birth index as a ratchet-compatible
trajectory in the `JRatchet` interface.
-/

namespace HeytingLean.Bridge.Assembly

open HeytingLean

/-- Assembly-index level interpreted as a trajectory over fuel. -/
def assemblyRatchetLevel
    {α : Type _}
    [DecidableEq α]
    (R : ATheory.Rules α)
    (o : ATheory.Obj α) : Nat → Nat :=
  fun _fuel => ATheory.birthAT R o

/-- The assembly-index trajectory is monotone (constant trajectory). -/
theorem assemblyRatchetTrajectory
    {α : Type _}
    [DecidableEq α]
    (R : ATheory.Rules α)
    (o : ATheory.Obj α) :
    Topos.JRatchet.RatchetTrajectory (assemblyRatchetLevel R o) := by
  intro fuel₁ fuel₂ _hle
  simp [assemblyRatchetLevel]

/-- Fuel-zero anchor for the assembly/J-ratchet bridge. -/
@[simp] theorem assemblyRatchetLevel_zero
    {α : Type _}
    [DecidableEq α]
    (R : ATheory.Rules α)
    (o : ATheory.Obj α) :
    assemblyRatchetLevel R o 0 = ATheory.birthAT R o := rfl

end HeytingLean.Bridge.Assembly
