import Mathlib.LinearAlgebra.Finsupp.Defs
import HeytingLean.LoF.Combinators.Differential.VectorSpace

/-!
# Differential combinators: a lightweight exponential `!V`

Differential linear logic interprets the exponential `!` as a cofree cocommutative coalgebra.
For this codebase we use a deliberately lightweight model:

`!V := (ℕ →₀ V)`  (a graded direct sum of copies of `V`).

This is sufficient to express `codereliction : V → !V` (embed into degree 1) and
`dereliction : !V → V` (project degree 1), and to state the “linear increment” lemma that
mirrors the DiLL intuition for codereliction.
-/

noncomputable section

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Differential

open scoped BigOperators

abbrev Exp (V : Type*) [Zero V] : Type _ :=
  ℕ →₀ V

namespace Exp

variable {K : Type*} [CommSemiring K]
variable {V : Type*} [AddCommMonoid V] [Module K V]

noncomputable def dereliction : Exp V →ₗ[K] V :=
  Finsupp.lapply 1

noncomputable def codereliction : V →ₗ[K] Exp V :=
  Finsupp.lsingle 1

theorem codereliction_linear_increment
    {W : Type*} [AddCommMonoid W] [Module K W]
    (f : Exp V →ₗ[K] W) (v dv : V) :
    f (codereliction (K := K) (V := V) (v + dv)) =
      f (codereliction (K := K) (V := V) v) + (f.comp (codereliction (K := K) (V := V))) dv := by
  simp [codereliction]

end Exp

end Differential
end Combinators
end LoF
end HeytingLean

