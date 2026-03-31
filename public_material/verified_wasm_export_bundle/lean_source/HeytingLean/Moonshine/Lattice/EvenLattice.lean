import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Int.Basic

set_option autoImplicit false

namespace HeytingLean.Moonshine.Lattice

universe u

/--
Minimal kernel-pure interface for an even integral lattice.

This keeps the algebra lightweight: a `ℤ`-module with a symmetric bilinear-like pairing and
an explicit `rank` field for downstream Moonshine planning.
-/
structure EvenLattice where
  Λ : Type u
  instAddCommGroup : AddCommGroup Λ
  instModule : Module ℤ Λ
  pairing : Λ → Λ → ℤ
  pairing_add_left : ∀ x y z : Λ, pairing (x + y) z = pairing x z + pairing y z
  pairing_add_right : ∀ x y z : Λ, pairing x (y + z) = pairing x y + pairing x z
  pairing_zsmul_left : ∀ n : ℤ, ∀ x y : Λ, pairing (n • x) y = n * pairing x y
  pairing_zsmul_right : ∀ n : ℤ, ∀ x y : Λ, pairing x (n • y) = n * pairing x y
  pairing_symm : ∀ x y : Λ, pairing x y = pairing y x
  even : ∀ x : Λ, ∃ k : ℤ, pairing x x = 2 * k
  rank : ℕ

attribute [instance] EvenLattice.instAddCommGroup EvenLattice.instModule

namespace EvenLattice

variable (L : EvenLattice)

/-- Squared norm associated to the lattice pairing. -/
def normSq (x : L.Λ) : ℤ :=
  L.pairing x x

end EvenLattice

/-- Rootless condition: there is no vector of squared norm `2`. -/
def Rootless (L : EvenLattice) : Prop :=
  ∀ x : L.Λ, L.normSq x ≠ 2

/--
A simple executable even-lattice model on `ℤ` with zero pairing.

This is not the Leech lattice; it is a compile-time toy object used to validate interfaces.
-/
def zeroPairingEvenLattice : EvenLattice where
  Λ := ℤ
  instAddCommGroup := inferInstance
  instModule := inferInstance
  pairing := fun _ _ => 0
  pairing_add_left := by intro x y z; simp
  pairing_add_right := by intro x y z; simp
  pairing_zsmul_left := by intro n x y; simp
  pairing_zsmul_right := by intro n x y; simp
  pairing_symm := by intro x y; simp
  even := by
    intro x
    refine ⟨0, by simp⟩
  rank := 1

@[simp] lemma zeroPairingEvenLattice_normSq (x : zeroPairingEvenLattice.Λ) :
    zeroPairingEvenLattice.normSq x = 0 := by
  rfl

lemma rootless_zeroPairingEvenLattice : Rootless zeroPairingEvenLattice := by
  intro x
  change (0 : ℤ) ≠ 2
  decide

end HeytingLean.Moonshine.Lattice
