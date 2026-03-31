import HeytingLean.Numbers.Surreal.NoneistFoundation
import HeytingLean.Noneism.Semantics.KripkeProp

/-!
# Surreal.NoneistKripke

SN-012 baseline: a Surreal-facing Kripke layer with explicit world classification
and constant/varying domain policy.
-/

namespace HeytingLean
namespace Numbers
namespace Surreal
namespace NoneistKripke

open HeytingLean.Noneism
open HeytingLean.Noneism.KripkeProp

/-- World classification used by the Surreal noneist lane. -/
inductive WorldMode where
  | possible
  | impossible
  deriving Repr, DecidableEq

/-- Kripke worlds with stage and explicit classification. -/
structure World where
  stage : Nat
  mode : WorldMode
  deriving Repr, DecidableEq

instance : LE World where
  le w v := w.stage ≤ v.stage ∧ w.mode = v.mode

instance : Preorder World where
  le := (· ≤ ·)
  le_refl w := ⟨Nat.le_refl _, rfl⟩
  le_trans a b c hab hbc := by
    exact ⟨Nat.le_trans hab.1 hbc.1, hab.2.trans hbc.2⟩

/-- Atomic symbols used for Surreal noneist forcing. -/
inductive Atom where
  | markedGenesis
  | unmarkedGenesis
  | modePossible
  | modeImpossible
  deriving Repr, DecidableEq

/-- Domain policy for existence forcing. -/
inductive DomainPolicy where
  | constant
  | varying
  deriving Repr, DecidableEq

/-- Existence valuation induced by domain policy. -/
def valEx (policy : DomainPolicy) (w : World) : Term → Prop
  | .var x =>
      match policy with
      | .constant => True
      | .varying => x ≤ w.stage

/-- Atomic valuation for Surreal noneist predicates. -/
def valPred (w : World) : Atom → List Term → Prop
  | .markedGenesis, _ => genesis.polarity = .mark
  | .unmarkedGenesis, _ => counterGenesis.polarity = .unmark
  | .modePossible, _ => w.mode = .possible
  | .modeImpossible, _ => w.mode = .impossible

/-- Kripke model for Surreal noneist formulas under selected domain policy. -/
def model (policy : DomainPolicy) : Model World Atom where
  valPred := valPred
  monoPred := by
    intro w v hw p args hp
    rcases hw with ⟨_hstage, hmode⟩
    cases p with
    | markedGenesis =>
        exact hp
    | unmarkedGenesis =>
        exact hp
    | modePossible =>
        simpa [valPred, hmode] using hp
    | modeImpossible =>
        simpa [valPred, hmode] using hp
  valEx := valEx policy
  monoEx := by
    intro w v hw t ht
    rcases hw with ⟨hstage, _hmode⟩
    cases policy with
    | constant =>
        simp [valEx] at ht ⊢
    | varying =>
        cases t with
        | var x =>
            simp [valEx] at ht ⊢
            exact Nat.le_trans ht hstage

@[simp] theorem forces_mode_possible_iff (policy : DomainPolicy) (w : World) :
    Forces (model policy) w (.pred .modePossible []) ↔ w.mode = .possible := by
  rfl

@[simp] theorem forces_mode_impossible_iff (policy : DomainPolicy) (w : World) :
    Forces (model policy) w (.pred .modeImpossible []) ↔ w.mode = .impossible := by
  rfl

theorem mode_possible_or_impossible (w : World) :
    w.mode = .possible ∨ w.mode = .impossible := by
  cases w.mode <;> simp

theorem mode_not_both (w : World) :
    ¬ (w.mode = .possible ∧ w.mode = .impossible) := by
  intro h
  rcases h with ⟨hpos, himp⟩
  have hcontra : (WorldMode.possible : WorldMode) = .impossible := hpos.symm.trans himp
  cases hcontra

theorem forces_mode_not_both (policy : DomainPolicy) (w : World) :
    ¬ (Forces (model policy) w (.pred .modePossible []) ∧
        Forces (model policy) w (.pred .modeImpossible [])) := by
  intro hBoth
  have hMode : w.mode = .possible ∧ w.mode = .impossible := by
    exact ⟨(forces_mode_possible_iff policy w).1 hBoth.1,
      (forces_mode_impossible_iff policy w).1 hBoth.2⟩
  exact mode_not_both w hMode

theorem forces_mode_possible_or_impossible (policy : DomainPolicy) (w : World) :
    Forces (model policy) w (.pred .modePossible []) ∨
      Forces (model policy) w (.pred .modeImpossible []) := by
  rcases mode_possible_or_impossible w with hpos | himp
  · exact Or.inl ((forces_mode_possible_iff policy w).2 hpos)
  · exact Or.inr ((forces_mode_impossible_iff policy w).2 himp)

theorem not_le_of_mode_mismatch {w v : World} (h : w.mode ≠ v.mode) :
    ¬ w ≤ v := by
  intro hle
  exact h hle.2

@[simp] theorem forces_marked_genesis (policy : DomainPolicy) (w : World) :
    Forces (model policy) w (.pred .markedGenesis []) := by
  change genesis.polarity = .mark
  exact genesis_polarity

@[simp] theorem forces_unmarked_genesis (policy : DomainPolicy) (w : World) :
    Forces (model policy) w (.pred .unmarkedGenesis []) := by
  change counterGenesis.polarity = .unmark
  exact counterGenesis_polarity

@[simp] theorem forces_exists_constant (w : World) (x : Nat) :
    Forces (model .constant) w (.eExists (.var x)) := by
  trivial

@[simp] theorem forces_exists_varying_iff (w : World) (x : Nat) :
    Forces (model .varying) w (.eExists (.var x)) ↔ x ≤ w.stage := by
  rfl

theorem forces_exists_varying_monotone {w v : World} (h : w ≤ v) (x : Nat) :
    Forces (model .varying) w (.eExists (.var x)) →
      Forces (model .varying) v (.eExists (.var x)) := by
  exact (model .varying).monoEx h (.var x)

end NoneistKripke
end Surreal
end Numbers
end HeytingLean
