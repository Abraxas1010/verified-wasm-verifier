import HeytingLean.Chem.Materials.Crystal
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Symmetry: affine operations as a group

`AffineOpG d` represents an affine transformation on fractional coordinates:

  x ↦ A * x + b

where `A` is an invertible `d×d` matrix over `ℚ` (an element of `GL (Fin d) ℚ`)
and `b` is a translation vector (`FracCoord d`).

This gives a genuine group under composition, and a `MulAction` on `FracCoord d`.

We keep this separate from `Chem/Materials/Symmetry/Affine.lean`, which uses an integer
matrix representation as a lightweight, computable scaffold.
-/

namespace HeytingLean.Chem.Materials.Symmetry

open BigOperators
open HeytingLean.Chem.Materials

abbrev GLQ (d : Nat) : Type := Matrix.GeneralLinearGroup (Fin d) ℚ

structure AffineOpG (d : Nat) where
  A : GLQ d
  b : FracCoord d

namespace AffineOpG

@[ext] theorem ext {d : Nat} {op1 op2 : AffineOpG d} (hA : op1.A = op2.A) (hb : op1.b = op2.b) :
    op1 = op2 := by
  cases op1
  cases op2
  cases hA
  cases hb
  rfl

def apply {d : Nat} (op : AffineOpG d) (x : FracCoord d) : FracCoord d :=
  op.A.1.mulVec x + op.b

def mul {d : Nat} (op1 op2 : AffineOpG d) : AffineOpG d :=
  { A := op1.A * op2.A
    b := op1.A.1.mulVec op2.b + op1.b }

def one {d : Nat} : AffineOpG d :=
  { A := 1
    b := fun _ => 0 }

def inv {d : Nat} (op : AffineOpG d) : AffineOpG d :=
  { A := op.A⁻¹
    b := -((op.A⁻¹).1.mulVec op.b) }

instance {d : Nat} : Mul (AffineOpG d) := ⟨mul⟩
instance {d : Nat} : One (AffineOpG d) := ⟨one⟩
instance {d : Nat} : Inv (AffineOpG d) := ⟨inv⟩

@[simp] theorem one_A {d : Nat} : (1 : AffineOpG d).A = 1 := rfl
@[simp] theorem one_b {d : Nat} : (1 : AffineOpG d).b = (fun _ => 0) := rfl

@[simp] theorem mul_A {d : Nat} (op1 op2 : AffineOpG d) : (op1 * op2).A = op1.A * op2.A := rfl
@[simp] theorem mul_b {d : Nat} (op1 op2 : AffineOpG d) :
    (op1 * op2).b = op1.A.1.mulVec op2.b + op1.b := rfl

@[simp] theorem inv_A {d : Nat} (op : AffineOpG d) : (op⁻¹).A = op.A⁻¹ := rfl
@[simp] theorem inv_b {d : Nat} (op : AffineOpG d) :
    (op⁻¹).b = -((op.A⁻¹).1.mulVec op.b) := rfl

theorem apply_mul {d : Nat} (op1 op2 : AffineOpG d) (x : FracCoord d) :
    apply (op1 * op2) x = apply op1 (apply op2 x) := by
  funext i
  -- Expand `apply`/`mul` and use linearity/associativity of `mulVec`.
  simp [apply, Matrix.mulVec_add, Matrix.mulVec_mulVec, add_assoc]

theorem apply_one {d : Nat} (x : FracCoord d) : apply (1 : AffineOpG d) x = x := by
  funext i
  simp [apply, Matrix.one_mulVec]

instance {d : Nat} : Group (AffineOpG d) where
  mul := (· * ·)
  mul_assoc := by
    intro a b c
    cases a; cases b; cases c
    apply AffineOpG.ext
    · simp [mul_assoc]
    · funext i
      simp [Matrix.mulVec_add, Matrix.mulVec_mulVec, add_assoc]
  one := 1
  one_mul := by
    intro a
    cases a
    apply AffineOpG.ext
    · simp
    · funext i
      simp [Matrix.one_mulVec]
  mul_one := by
    intro a
    cases a
    apply AffineOpG.ext
    · simp
    · funext i
      simp [Matrix.mulVec]
  inv := Inv.inv
  inv_mul_cancel := by
    intro a
    cases a
    apply AffineOpG.ext
    · simp
    · funext i
      simp

-- Action of affine ops on fractional coordinates.
instance {d : Nat} : SMul (AffineOpG d) (FracCoord d) := ⟨apply⟩

@[simp] theorem smul_def {d : Nat} (op : AffineOpG d) (x : FracCoord d) : op • x = apply op x := rfl

instance {d : Nat} : MulAction (AffineOpG d) (FracCoord d) where
  smul := (· • ·)
  one_smul := by intro x; simpa [smul_def] using apply_one x
  mul_smul := by intro a b x; simpa [smul_def] using apply_mul a b x

end AffineOpG

end HeytingLean.Chem.Materials.Symmetry
