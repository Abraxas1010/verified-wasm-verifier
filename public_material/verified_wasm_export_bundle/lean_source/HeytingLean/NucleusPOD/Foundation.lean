import Mathlib.Order.Closure

namespace HeytingLean
namespace NucleusPOD

abbrev AgentId := Nat
abbrev RoleId := Nat
abbrev GrantId := Nat
abbrev KeyHash := Nat
abbrev Tick := Nat

structure Agent where
  agentId : AgentId
  deriving DecidableEq, Repr

structure Channel (src tgt : Agent) where
  grant : GrantId
  deriving DecidableEq, Repr

namespace Channel

def reflexive (A : Agent) : Channel A A :=
  ⟨0⟩

def compose {A B C : Agent} (f : Channel A B) (g : Channel B C) : Channel A C :=
  ⟨f.grant + g.grant⟩

@[simp] theorem compose_reflexive_left {A B : Agent} (f : Channel A B) :
    compose (reflexive A) f = f := by
  cases f
  simp [compose, reflexive]

@[simp] theorem compose_reflexive_right {A B : Agent} (f : Channel A B) :
    compose f (reflexive B) = f := by
  cases f
  simp [compose, reflexive, Nat.add_zero]

@[simp] theorem compose_assoc {A B C D : Agent}
    (f : Channel A B) (g : Channel B C) (h : Channel C D) :
    compose (compose f g) h = compose f (compose g h) := by
  cases f; cases g; cases h
  simp [compose, Nat.add_assoc]

end Channel

structure NucleusState where
  payload : Nat
  closed : Bool
  deriving DecidableEq, Repr

structure Venue where
  carrier : Agent
  budget : Nat
  deriving DecidableEq, Repr

@[simp] def closureFloor : Nat := 1

/-- A nontrivial nucleus-like closure on `Nat`: push every payload above a floor. -/
@[simp] def closure (x : Nat) : Nat := Nat.max x closureFloor

/-- Predicate for payloads fixed by the nucleus closure. -/
@[simp] def IsClosed (x : Nat) : Prop := closure x = x

structure AgentTransport (A B : Agent) where
  forward : Nat → Nat
  backward : Nat → Nat
  /-- Transport preserves closed payloads under forward/backward round-trip. -/
  roundTripClosed : ∀ x : Nat, backward (forward (closure x)) = closure x
  epsilonForward : Nat
  epsilonBackward : Nat

structure GluingData where
  leftSection : Nat
  rightSection : Nat
  overlapWitness : Nat

theorem closure_extensive (x : Nat) : x ≤ closure x := by
  simp [closure]

theorem closure_floor_le (x : Nat) : closureFloor ≤ closure x := by
  simp [closure]

theorem closure_monotone {a b : Nat} (h : a ≤ b) : closure a ≤ closure b := by
  unfold closure
  exact Nat.max_le.2 ⟨
    Nat.le_trans h (Nat.le_max_left b closureFloor),
    Nat.le_max_right b closureFloor
  ⟩

theorem closure_idempotent (x : Nat) : closure (closure x) = closure x := by
  unfold closure
  simp

theorem closure_fixpoint_of_ge_floor (x : Nat) (h : closureFloor ≤ x) : closure x = x := by
  have h1 : 1 ≤ x := by
    simpa [closureFloor] using h
  simpa [closure] using Nat.max_eq_left h1

theorem isClosed_iff_ge_floor (x : Nat) : IsClosed x ↔ closureFloor ≤ x := by
  constructor
  · intro hx
    have hfloor : closureFloor ≤ closure x := closure_floor_le x
    exact hx ▸ hfloor
  · intro h
    exact closure_fixpoint_of_ge_floor x h

theorem closure_le_iff_le_of_closed {x y : Nat} (hy : IsClosed y) :
    closure x ≤ y ↔ x ≤ y := by
  constructor
  · intro hxy
    exact Nat.le_trans (closure_extensive x) hxy
  · intro hxy
    have hmon : closure x ≤ closure y := closure_monotone hxy
    exact hy ▸ hmon

/-- The nucleus closure as a bundled Mathlib closure operator. -/
def closureOperatorNat : ClosureOperator Nat where
  toOrderHom :=
    { toFun := closure
      monotone' := by
        intro a b h
        exact closure_monotone h }
  le_closure' := closure_extensive
  idempotent' := closure_idempotent

@[simp] theorem closureOperatorNat_apply (x : Nat) :
    closureOperatorNat x = closure x := rfl

/-- Closed payloads form a Galois insertion into the base lattice. -/
def closureGaloisInsertion : GaloisInsertion closureOperatorNat.toCloseds (↑) :=
  closureOperatorNat.gi

theorem closureOperatorNat_reconstructs_from_gi :
    closureGaloisInsertion.gc.closureOperator = closureOperatorNat := by
  unfold closureGaloisInsertion
  exact closureOperator_gi_self closureOperatorNat

abbrev Reward := Rat

@[simp] def subgoalReward (solved total : Nat) : Reward :=
  if total = 0 then 0 else solved / total

@[simp] theorem subgoalReward_zero_total (solved : Nat) : subgoalReward solved 0 = 0 := by
  simp [subgoalReward]

@[simp] theorem subgoalReward_self (n : Nat) :
    subgoalReward n n = (if n = 0 then 0 else (n : Rat) / (n : Rat)) := by
  by_cases h : n = 0
  · simp [h, subgoalReward]
  · simp [subgoalReward, h]

end NucleusPOD
end HeytingLean
