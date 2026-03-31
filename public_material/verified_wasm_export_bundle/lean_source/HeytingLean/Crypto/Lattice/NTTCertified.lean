import HeytingLean.Crypto.Lattice.NTTBridge
import HeytingLean.Crypto.Lattice.NTTIterative
import Mathlib.Data.Matrix.Basic

/-!
# Certified NTT interface (matrix-level)

This module turns the ML-KEM NTT situation into a **fully checkable** artifact without introducing
any new axioms:

- `NTTBridge.quadSpecMatrix` is an explicit, computable matrix for the quadratic-factor NTT
  specification (the “algebraic target” ordering).
- `inttMatrix` is extracted from the executable inverse routine `NTTIterative.inttIterative` by
  applying it to the standard basis vectors.
- We then prove (by finite computation) that `inttMatrix * quadSpecMatrix = 1`, and use `inttMatrix`
  as a certified inverse for the spec transform.

This does **not** yet prove that `NTTIterative.nttIterative` equals `quadSpecMatrix.mulVec` on all
inputs; that refinement is still tracked in `conjectures/mlkem_ntt_correctness.json`. However, it
does provide a fully verified “bridge-complete” NTT/INTT pair suitable for downstream correctness
statements (e.g. multiplying in the quadratic-factor domain and mapping back).
-/

namespace HeytingLean
namespace Crypto
namespace Lattice
namespace NTTCertified

open scoped BigOperators

open NTTIterative
open NTTBridge

abbrev q : Nat := NTT.q
abbrev F : Type := ZMod q
abbrev Idx : Type := Fin 256

instance : Fact (Nat.Prime q) := by
  dsimp [q, NTT.q]
  exact ⟨by native_decide⟩

def normalize256 (a : Array F) : Array F :=
  Array.ofFn (fun i : Idx => a.getD i.val 0)

def basisArray (j : Idx) : Array F :=
  Array.ofFn (fun i : Idx => if i = j then (1 : F) else 0)

def vecOfArray (a : Array F) : Idx → F :=
  fun i => a.getD i.val 0

def arrayOfVec (v : Idx → F) : Array F :=
  Array.ofFn v

def inttMatrix : Matrix Idx Idx F :=
  fun row col =>
    (inttIterative (basisArray col) (by simp [basisArray])).getD row.val 0

def nttSpec (a : Array F) : Array F :=
  quadraticSpec a

def inttSpec (a : Array F) : Array F :=
  arrayOfVec (inttMatrix.mulVec (vecOfArray a))

theorem inttMatrix_mul_quadSpecMatrix :
    inttMatrix * quadSpecMatrix = 1 := by
  native_decide

theorem inttSpec_nttSpec (a : Array F) :
    inttSpec (nttSpec a) = normalize256 a := by
  -- Reduce to a matrix computation using `inttMatrix_mul_quadSpecMatrix`.
  classical
  apply Array.ext (by simp [inttSpec, nttSpec, normalize256, arrayOfVec])
  intro i hi
  -- Convert `GetElem` to `getD` on the `Idx` function view.
  have hi' : (i : Nat) < 256 := by simpa using hi
  have hmul :
      (inttMatrix.mulVec (quadSpecMatrix.mulVec (vecOfArray a))) ⟨i, hi'⟩ =
        (vecOfArray a) ⟨i, hi'⟩ := by
    -- `inttMatrix * quadSpecMatrix = 1` implies the corresponding `mulVec` identity.
    simpa [Matrix.mulVec_mulVec, inttMatrix_mul_quadSpecMatrix]
  have hquad : vecOfArray (quadraticSpec a) = quadSpecMatrix.mulVec (vecOfArray a) := by
    funext j
    simp [quadraticSpec, vecOfArray, arrayToFn, quadSpecMatrix]
  -- Rewrite through the `quadraticSpec` definition.
  simpa [inttSpec, nttSpec, normalize256, vecOfArray, arrayOfVec, hquad] using hmul

end NTTCertified
end Lattice
end Crypto
end HeytingLean
