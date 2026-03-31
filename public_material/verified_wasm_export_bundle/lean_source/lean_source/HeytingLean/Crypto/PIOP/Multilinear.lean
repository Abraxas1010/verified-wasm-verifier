import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Crypto.PIOP.Multilinear

Minimal spec-level representation of multilinear polynomials used by PIOP/IOP protocols
(e.g. Sumcheck).

At this stage, a multilinear polynomial is modelled by its evaluation function
`(Fin n → F) → F`. This is intentionally lightweight: later refinements can replace
it with structured polynomial representations or mathlib abstractions.
-/

namespace HeytingLean
namespace Crypto
namespace PIOP

variable {F : Type} [Field F]

open scoped BigOperators

/-- Multilinear polynomial in `n` Boolean variables, represented by evaluation. -/
structure MultilinearPoly (n : Nat) where
  eval : (Fin n → F) → F

namespace MultilinearPoly

/-- Sum of a multilinear polynomial over the Boolean hypercube `{0,1}^n`. -/
noncomputable def hypercubeSum {n : Nat} (p : MultilinearPoly (F := F) n) : F :=
  ∑ b : Fin n → Bool,
    p.eval (fun i => if b i then (1 : F) else 0)

end MultilinearPoly

end PIOP
end Crypto
end HeytingLean
