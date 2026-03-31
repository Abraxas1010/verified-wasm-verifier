import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic

/-!
# Crypto.Commit.PedersenAssumptions

Named assumption surfaces for computational hiding of Pedersen-style vector
commitments.

This module is intentionally lighter than the executable `PMF`-based IND-CCA game
used for KEMs. The current vector-commitment interface has no oracle/adversary
language yet, so we record the remaining cryptographic content as quantitative
assumption bundles rather than pretending to have a proved game reduction.

The core idea is:

* `DLogHardness P` packages an explicit bound for DLOG-style adversaries against
  a specific Pedersen parameter instance `P`;
* `ComputationalHiding P n` packages an explicit bound for hiding adversaries at
  vector length `n`; and
* `DLogReductionStatement P n` records the classical Pedersen reduction from a
  hiding distinguisher to a DLOG adversary with explicit additive loss.

No theorem here claims that a concrete parameter instance satisfies these
assumptions automatically. They are the honest bridge surface for future
cryptographic reductions.
-/

namespace HeytingLean
namespace Crypto
namespace Commit
namespace PedersenAssumptions

/-- Abstract DLOG-style adversary against a concrete Pedersen instance `P`. The
only quantitative datum tracked here is the adversary's distinguishing
advantage, constrained to the probability range `[0, 1]`. -/
structure DLogAdversary {Inst : Type} (P : Inst) where
  advantage : ℝ
  advantage_nonneg : 0 ≤ advantage
  advantage_le_one : advantage ≤ 1

/-- Extract the quantitative advantage of a DLOG adversary. -/
def DLogAdvantage {Inst : Type} {P : Inst} (A : DLogAdversary P) : ℝ :=
  A.advantage

/-- A concrete hardness witness for a Pedersen instance `P`: every DLOG
adversary has advantage bounded by the explicit constant `ε`. -/
structure DLogHardnessWitness {Inst : Type} (P : Inst) where
  ε : ℝ
  ε_nonneg : 0 ≤ ε
  sound : ∀ A : DLogAdversary P, DLogAdvantage A ≤ ε

/-- Named hardness surface for the discrete-log assumption attached to `P`. -/
def DLogHardness {Inst : Type} (P : Inst) : Prop :=
  Nonempty (DLogHardnessWitness P)

/-- Abstract hiding adversary for a Pedersen-style vector commitment. The
adversary chooses two challenge vectors that agree at the designated opened
position and is assigned an advantage in `[0, 1]`. -/
structure HidingAdversary {Inst : Type} (P : Inst) (n : Nat) where
  left : Fin n → Int
  right : Fin n → Int
  openedIndex : Fin n
  agreeAtOpened : left openedIndex = right openedIndex
  advantage : ℝ
  advantage_nonneg : 0 ≤ advantage
  advantage_le_one : advantage ≤ 1

/-- Extract the quantitative hiding advantage of a Pedersen adversary. -/
def HidingAdvantage {Inst : Type} {P : Inst} {n : Nat}
    (A : HidingAdversary P n) : ℝ :=
  A.advantage

/-- A concrete computational-hiding witness for a Pedersen instance `P` at
vector length `n`: every hiding adversary has advantage bounded by `ε`. -/
structure ComputationalHidingWitness {Inst : Type} (P : Inst) (n : Nat) where
  ε : ℝ
  ε_nonneg : 0 ≤ ε
  sound : ∀ A : HidingAdversary P n, HidingAdvantage A ≤ ε

/-- Named computational-hiding surface for a Pedersen instance `P`. -/
def ComputationalHiding {Inst : Type} (P : Inst) (n : Nat) : Prop :=
  Nonempty (ComputationalHidingWitness P n)

/-- Classical Pedersen reduction statement: every hiding adversary against `P`
at vector length `n` can be transported to a DLOG adversary against `P`, up to
an explicit additive loss term. -/
structure DLogReductionStatement {Inst : Type} (P : Inst) (n : Nat) where
  loss : ℝ
  loss_nonneg : 0 ≤ loss
  transport :
    ∀ A : HidingAdversary P n,
      ∃ B : DLogAdversary P,
        HidingAdvantage A ≤ DLogAdvantage B + loss

/-- A DLOG hardness witness together with a reduction statement yields a
computational-hiding witness. -/
theorem computationalHiding_of_dlog
    {Inst : Type} {P : Inst} {n : Nat}
    (hHard : DLogHardness P)
    (hRed : DLogReductionStatement P n) :
    ComputationalHiding P n := by
  rcases hHard with ⟨hard⟩
  refine ⟨{
    ε := hard.ε + hRed.loss
    ε_nonneg := add_nonneg hard.ε_nonneg hRed.loss_nonneg
    sound := ?_
  }⟩
  intro A
  rcases hRed.transport A with ⟨B, hAB⟩
  exact le_trans hAB (add_le_add (hard.sound B) le_rfl)

end PedersenAssumptions
end Commit
end Crypto
end HeytingLean
