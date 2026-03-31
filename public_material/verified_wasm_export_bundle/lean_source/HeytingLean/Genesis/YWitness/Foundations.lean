import HeytingLean.Genesis.YWitness.Prelude
import HeytingLean.LoF.Bauer.LawvereFixedPoint
import Mathlib.Order.Nucleus

namespace HeytingLean.Genesis.YWitness

open Order

/-- Continuous-side data: a bounded process together with a witnessed nontrivial step. -/
structure ContinuousWitness (L : Type _) [Preorder L] [OrderBot L] [OrderTop L] where
  oscillation : Stepwise L
  bounded : forall n, ⊥ <= oscillation n /\ oscillation n <= ⊤
  nonconstant : AdjacentNonconstant oscillation

/-- Discrete-side data: a point fixed by a chosen nucleus. -/
structure DiscreteWitness (L : Type _) [CompleteLattice L] (R : Nucleus L) where
  point : L
  is_fixed : R point = point

/-- Iterating a nucleus from bottom gives a canonical bounded approximation chain. -/
def nucleusApprox {L : Type _} [CompleteLattice L] (R : Nucleus L) : Stepwise L
  | 0 => ⊥
  | n + 1 => R (nucleusApprox R n)

@[simp] theorem nucleusApprox_zero {L : Type _} [CompleteLattice L] (R : Nucleus L) :
    nucleusApprox R 0 = ⊥ := rfl

@[simp] theorem nucleusApprox_succ {L : Type _} [CompleteLattice L] (R : Nucleus L) (n : Nat) :
    nucleusApprox R (n + 1) = R (nucleusApprox R n) := rfl

theorem nucleusApprox_bounded {L : Type _} [CompleteLattice L] (R : Nucleus L) (n : Nat) :
    ⊥ <= nucleusApprox R n /\ nucleusApprox R n <= ⊤ := by
  exact ⟨bot_le, le_top⟩

theorem nucleusApprox_step_fixed_if_stable {L : Type _} [CompleteLattice L]
    (R : Nucleus L) {n : Nat}
    (hstable : nucleusApprox R (n + 1) = nucleusApprox R n) :
    R (nucleusApprox R n) = nucleusApprox R n := by
  simp [nucleusApprox] at hstable
  exact hstable

/-- The bounded approximants are summarized by the nucleus-closing of their supremum. -/
def crystallizationPoint {L : Type _} [CompleteLattice L] (R : Nucleus L) : L :=
  R (sSup (Set.range (nucleusApprox R)))

theorem crystallizationPoint_fixed {L : Type _} [CompleteLattice L] (R : Nucleus L) :
    R (crystallizationPoint R) = crystallizationPoint R := by
  simp [crystallizationPoint]

/-- A continuous witness follows the canonical approximation chain. -/
def FollowsApprox {L : Type _} [CompleteLattice L] (R : Nucleus L)
    (cw : ContinuousWitness L) : Prop :=
  Follows cw.oscillation (nucleusApprox R)

/-- The continuous process crystallizes when it follows the approximation chain and lands at the
canonical crystallization point. -/
def CrystallizesTo {L : Type _} [CompleteLattice L] (R : Nucleus L)
    (cw : ContinuousWitness L) (x : L) : Prop :=
  FollowsApprox R cw /\ x = crystallizationPoint R

/-- Regeneration data: a seed sequence starts at the given point and has at least one nontrivial
adjacent step. -/
structure ReentrySeed (L : Type _) where
  seq : Stepwise L
  nonconstant : AdjacentNonconstant seq

/-- The discrete point regenerates a genuinely moving sequence. -/
def Regenerates {L : Type _} (x : L) (seed : ReentrySeed L) : Prop :=
  StartsAt seed.seq x /\ AdjacentNonconstant seed.seq

/-- The canonical discrete witness associated to a nucleus. -/
def crystallizedWitness {L : Type _} [CompleteLattice L] (R : Nucleus L) :
    DiscreteWitness L R where
  point := crystallizationPoint R
  is_fixed := crystallizationPoint_fixed R

/-- Lawvere's theorem remains available as a negative guard against overclaiming unrestricted
fixed-point operators. -/
theorem lawvere_no_pointSurjective_bool (A : Type _) :
    Not (Exists fun e : A -> A -> Bool => HeytingLean.LoF.Bauer.Lawvere.PointSurjective e) := by
  exact HeytingLean.LoF.Bauer.Lawvere.no_pointSurjective_bool A

end HeytingLean.Genesis.YWitness
