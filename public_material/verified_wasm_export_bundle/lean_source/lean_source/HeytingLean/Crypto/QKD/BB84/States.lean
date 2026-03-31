import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Set.Lattice

/-!
# BB84 Quantum States

Defines the four BB84 states as a finite type:
- `|0⟩, |1⟩` (Z-basis / computational)
- `|+⟩, |−⟩` (X-basis / diagonal / Hadamard)

This file is intentionally *interface-first*: we model the four states as a
finite type rather than a full Hilbert-space semantics.
-/

namespace HeytingLean
namespace Crypto
namespace QKD
namespace BB84

/-- The two bases used in BB84. -/
inductive Basis : Type
  | Z  -- Rectilinear (computational): {|0⟩, |1⟩}
  | X  -- Diagonal (Hadamard): {|+⟩, |−⟩}
  deriving DecidableEq, Repr

namespace Basis

def equivBool : Bool ≃ Basis where
  toFun
    | false => Z
    | true => X
  invFun
    | Z => false
    | X => true
  left_inv b := by cases b <;> rfl
  right_inv b := by cases b <;> rfl

instance : Fintype Basis :=
  Fintype.ofEquiv Bool equivBool

end Basis

/-- A classical bit. -/
abbrev Bit : Type := Bool

/-- A BB84 state, parameterized by (basis, bit). -/
structure BB84State where
  basis : Basis
  bit : Bit
  deriving DecidableEq, Repr

namespace BB84State

/-- Equivalence to a product (used to derive `Fintype`). -/
def equivProd : (Basis × Bit) ≃ BB84State where
  toFun p := ⟨p.1, p.2⟩
  invFun s := (s.basis, s.bit)
  left_inv p := by cases p; rfl
  right_inv s := by cases s; rfl

instance : Fintype BB84State :=
  Fintype.ofEquiv (Basis × Bit) equivProd

/-- `|0⟩`. -/
def ket0 : BB84State := ⟨Basis.Z, false⟩
/-- `|1⟩`. -/
def ket1 : BB84State := ⟨Basis.Z, true⟩
/-- `|+⟩`. -/
def ketPlus : BB84State := ⟨Basis.X, false⟩
/-- `|−⟩`. -/
def ketMinus : BB84State := ⟨Basis.X, true⟩

/-- Z-basis states (computational basis). -/
def zBasisStates : Set BB84State :=
  {s | s.basis = Basis.Z}

/-- X-basis states (Hadamard/diagonal basis). -/
def xBasisStates : Set BB84State :=
  {s | s.basis = Basis.X}

/-- All BB84 states. -/
def allStates : Set BB84State :=
  Set.univ

lemma ket0_in_zBasis : ket0 ∈ zBasisStates := by
  simp [ket0, zBasisStates]

lemma ket1_in_zBasis : ket1 ∈ zBasisStates := by
  simp [ket1, zBasisStates]

lemma ketPlus_in_xBasis : ketPlus ∈ xBasisStates := by
  simp [ketPlus, xBasisStates]

lemma ketMinus_in_xBasis : ketMinus ∈ xBasisStates := by
  simp [ketMinus, xBasisStates]

lemma zBasisStates_eq : zBasisStates = ({ket0, ket1} : Set BB84State) := by
  ext s
  cases s with
  | mk b bit =>
      cases b <;> cases bit <;>
        simp [zBasisStates, ket0, ket1]

lemma xBasisStates_eq : xBasisStates = ({ketPlus, ketMinus} : Set BB84State) := by
  ext s
  cases s with
  | mk b bit =>
      cases b <;> cases bit <;>
        simp [xBasisStates, ketPlus, ketMinus]

lemma union_is_all : zBasisStates ∪ xBasisStates = allStates := by
  ext s
  cases s with
  | mk b bit =>
      cases b <;> simp [zBasisStates, xBasisStates, allStates]

lemma bases_disjoint : Disjoint zBasisStates xBasisStates := by
  refine Set.disjoint_left.2 ?_
  intro s hz hx
  have hz' : s.basis = Basis.Z := by
    simpa [zBasisStates] using hz
  have hx' : s.basis = Basis.X := by
    simpa [xBasisStates] using hx
  exact Basis.noConfusion (hz'.symm.trans hx')

end BB84State

end BB84
end QKD
end Crypto
end HeytingLean
