import HeytingLean.Numbers.Surreal.Experimental.NoneistAttentionCore

namespace HeytingLean
namespace Numbers
namespace Surreal
namespace Experimental

/-- Velocity-indexed worlds for experimental kinematic forcing. -/
structure KinematicWorld where
  stage : Nat
  velocity : Nat
  deriving Repr, DecidableEq

/-- Reachability relation for staged kinematic worlds. -/
def reaches (w v : KinematicWorld) : Prop :=
  w.stage ≤ v.stage ∧ w.velocity ≤ v.velocity

instance : LE KinematicWorld where
  le := reaches

instance : Preorder KinematicWorld where
  le := (· ≤ ·)
  le_refl w := ⟨Nat.le_refl _, Nat.le_refl _⟩
  le_trans a b c hab hbc := ⟨Nat.le_trans hab.1 hbc.1, Nat.le_trans hab.2 hbc.2⟩

/-- Unobtainability under a velocity budget. -/
def unobtainable (budget : Nat) (_w v : KinematicWorld) : Prop :=
  budget < v.velocity

/-- Horizon predicate: world speed exceeds budget. -/
def horizon (budget : Nat) (w : KinematicWorld) : Prop :=
  budget < w.velocity

instance instDecidableHorizon (budget : Nat) (w : KinematicWorld) :
    Decidable (horizon budget w) := by
  unfold horizon
  infer_instance

theorem horizon_implies_unobtainable_self {budget : Nat} {w : KinematicWorld}
    (h : horizon budget w) :
    unobtainable budget w w := h

theorem horizon_implies_unobtainable_of_reaches
    {budget : Nat} {w v : KinematicWorld}
    (hH : horizon budget w) (hR : reaches w v) :
    unobtainable budget w v := by
  exact Nat.lt_of_lt_of_le hH hR.2

/-- Explicit witness that a transition hits a horizon barrier. -/
def horizonCertificate (budget : Nat) (w v : KinematicWorld) : Prop :=
  horizon budget w ∧ reaches w v

@[simp] theorem horizonCertificate_implies_unobtainable
    {budget : Nat} {w v : KinematicWorld}
    (h : horizonCertificate budget w v) :
    unobtainable budget w v :=
  horizon_implies_unobtainable_of_reaches h.1 h.2

/-- Relational forcing over kinematic worlds. -/
def relForcing (P : KinematicWorld → Prop) (w : KinematicWorld) : Prop :=
  ∀ ⦃v : KinematicWorld⦄, reaches w v → P v

theorem relForcing_mono
    {P Q : KinematicWorld → Prop}
    (hPQ : ∀ w, P w → Q w)
    {w : KinematicWorld} :
    relForcing P w → relForcing Q w := by
  intro hP v hv
  exact hPQ v (hP hv)

end Experimental
end Surreal
end Numbers
end HeytingLean
