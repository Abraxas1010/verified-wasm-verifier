import HeytingLean.PerspectivalPlenum.StrictRatchet.Gates

namespace HeytingLean
namespace PerspectivalPlenum
namespace StrictRatchet
namespace Spectral

/--
Finite spectral pages used by the strict ratchet filtration.

This is an executable surrogate for the first part of the spectral-sequence
program: we track the concrete pages that matter for the current three-level
ratchet (`L0 -> L1 -> L2`) and expose machine-checkable witnesses.
-/
inductive Page where
  | E0
  | E1
  | E2
  | Einfty
  deriving DecidableEq, Repr

namespace Page

def index : Page → Nat
  | .E0 => 0
  | .E1 => 1
  | .E2 => 2
  | .Einfty => 3

@[simp] theorem index_E0 : index .E0 = 0 := rfl
@[simp] theorem index_E1 : index .E1 = 1 := rfl
@[simp] theorem index_E2 : index .E2 = 2 := rfl
@[simp] theorem index_Einfty : index .Einfty = 3 := rfl

end Page

/-- Birthday-style filtration index induced by strict ratchet levels. -/
def birthdayFiltration : StrictLevel → Nat := StrictLevel.rank

theorem birthdayFiltration_monotone {a b : StrictLevel} (h : a ≤ b) :
    birthdayFiltration a ≤ birthdayFiltration b := h

/--
Page witness at each strict level.

`E1` is where nontrivial ratchet information appears:
the plenum-level separation witness enters and persists to `E∞`.
-/
def pageWitness : Page → StrictLevel → Prop
  | .E0, _ => True
  | .E1, .L0 => False
  | .E1, .L1 => False
  | .E1, .L2 => separationWitness .L2
  | .E2, .L0 => False
  | .E2, .L1 => False
  | .E2, .L2 => separationWitness .L2
  | .Einfty, .L0 => False
  | .Einfty, .L1 => False
  | .Einfty, .L2 => separationWitness .L2

@[simp] theorem pageWitness_E0 (ℓ : StrictLevel) :
    pageWitness .E0 ℓ := by
  cases ℓ <;> simp [pageWitness]

@[simp] theorem pageWitness_E1_L2 :
    pageWitness .E1 .L2 := by
  simpa [pageWitness] using separationWitness_L2

@[simp] theorem pageWitness_E1_L1 :
    ¬ pageWitness .E1 .L1 := by
  simp [pageWitness]

@[simp] theorem pageWitness_E2_L2 :
    pageWitness .E2 .L2 := by
  simpa [pageWitness] using separationWitness_L2

@[simp] theorem pageWitness_Einfty_L2 :
    pageWitness .Einfty .L2 := by
  simpa [pageWitness] using separationWitness_L2

@[simp] theorem pageWitness_Einfty_L1 :
    ¬ pageWitness .Einfty .L1 := by
  simp [pageWitness]

/--
`d1` differential class for the strict-ratchet lane.

`L0 -> L1` and `L1 -> L2` are marked nontrivial and witnessed by the existing
strict-edge theorems.
-/
def d1Nontrivial : StrictLevel → StrictLevel → Prop
  | .L0, .L1 =>
      ∀ {α : Type} [Order.Frame α] (S : RatchetStep α) (J : Nucleus α),
        StrictStage.strictlyPrecedes (StrictStage.base J) (StrictStage.witness S J)
  | .L1, .L2 =>
      ∀ {α : Type} [Order.Frame α] (S : RatchetStep α)
        (steps : List (RatchetStep α)) (J : Nucleus α),
        StrictStage.strictlyPrecedes (StrictStage.witness S J) (StrictStage.plenum steps J)
  | _, _ => False

theorem d1_base_to_witness_nontrivial :
    d1Nontrivial .L0 .L1 := by
  intro α _ S J
  exact strict_edge_base_to_witness S J

theorem d1_witness_to_plenum_nontrivial :
    d1Nontrivial .L1 .L2 := by
  intro α _ S steps J
  exact strict_edge_witness_to_plenum S steps J

/-- Convergence witness used by the strict-ratchet spectral lane. -/
def convergenceWitness : Prop :=
  pageWitness .Einfty .L2 ∧ ¬ pageWitness .Einfty .L1

theorem convergenceWitness_holds : convergenceWitness := by
  exact ⟨pageWitness_Einfty_L2, pageWitness_Einfty_L1⟩

/--
Machine-checkable strict spectral theorem:

1. both `d1` strict edges are nontrivial;
2. the plenum separation witness survives to `E∞`.
-/
def strictSpectralTheorem : Prop :=
  d1Nontrivial .L0 .L1 ∧ d1Nontrivial .L1 .L2 ∧ convergenceWitness

theorem strictSpectralTheorem_holds : strictSpectralTheorem := by
  exact ⟨d1_base_to_witness_nontrivial, d1_witness_to_plenum_nontrivial, convergenceWitness_holds⟩

/-- Birthdays and strict-level ranks are definitionally aligned in this lane. -/
theorem birthday_alignment (ℓ : StrictLevel) :
    birthdayFiltration ℓ = StrictLevel.rank ℓ := rfl

end Spectral
end StrictRatchet
end PerspectivalPlenum
end HeytingLean
