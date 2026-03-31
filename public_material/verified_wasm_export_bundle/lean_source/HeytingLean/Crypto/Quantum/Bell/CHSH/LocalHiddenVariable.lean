import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import HeytingLean.Crypto.Quantum.Bell.CHSH.Correlations

/-!
# Local hidden variable (LHV) models

We model an LHV strategy as:
- a finite hidden variable type `Λ`,
- a probability mass function `pmf : Λ → ℝ` (nonnegative, sums to 1),
- deterministic response functions for Alice and Bob.

From this we derive correlators `E(x,y)` by averaging ±1 products.
-/

namespace HeytingLean
namespace Crypto
namespace Quantum
namespace Bell
namespace CHSH

open scoped BigOperators

/-- Binary measurement outcomes. We interpret `false ↦ +1` and `true ↦ -1`. -/
abbrev Outcome : Type := Bool

namespace Outcome

def sign : Outcome → ℝ
  | false => 1
  | true => -1

@[simp] theorem sign_false : sign false = (1 : ℝ) := rfl
@[simp] theorem sign_true : sign true = (-1 : ℝ) := rfl

@[simp] theorem sign_sq (o : Outcome) : (sign o) ^ 2 = (1 : ℝ) := by
  cases o <;> norm_num [sign]

@[simp] theorem abs_sign (o : Outcome) : |sign o| = (1 : ℝ) := by
  cases o <;> norm_num [sign]

end Outcome

/-- A finite LHV model with deterministic local response functions. -/
structure LocalHiddenVariableModel where
  Λ : Type
  instFintype : Fintype Λ
  pmf : Λ → ℝ
  pmf_nonneg : ∀ l, 0 ≤ pmf l
  pmf_sum_one : (Finset.univ.sum pmf) = 1
  alice : Λ → Setting → Outcome
  bob : Λ → Setting → Outcome

attribute [instance] LocalHiddenVariableModel.instFintype

namespace LocalHiddenVariableModel

/-- Deterministic product value for a hidden variable at settings `(x,y)`. -/
def value (M : LocalHiddenVariableModel) (x y : Setting) (l : M.Λ) : ℝ :=
  Outcome.sign (M.alice l x) * Outcome.sign (M.bob l y)

@[simp] theorem abs_value (M : LocalHiddenVariableModel) (x y : Setting) (l : M.Λ) :
    |M.value x y l| = (1 : ℝ) := by
  simp [LocalHiddenVariableModel.value, abs_mul, Outcome.abs_sign]

/-- Correlator induced by an LHV model. -/
def toCorrelator (M : LocalHiddenVariableModel) : Correlator where
  E := fun x y => Finset.univ.sum fun l => M.pmf l * M.value x y l
  bounded := by
    intro x y
    classical
    let f : M.Λ → ℝ := fun l => M.pmf l * M.value x y l
    have hsum :
        (Finset.univ.sum fun l => |M.pmf l * M.value x y l|) = (Finset.univ.sum fun l => M.pmf l) := by
      simp [abs_mul, M.abs_value, abs_of_nonneg, M.pmf_nonneg]
    have habs :
        |Finset.univ.sum f| ≤ (Finset.univ.sum fun l => |f l|) := by
      simpa [f] using
        (Finset.abs_sum_le_sum_abs (f := f) (s := (Finset.univ : Finset M.Λ)))
    have hEabs :
        |Finset.univ.sum f| ≤ (1 : ℝ) := by
      have habsSum : (Finset.univ.sum fun l => |f l|) = (1 : ℝ) := by
        calc
          (Finset.univ.sum fun l => |f l|) =
              (Finset.univ.sum fun l => |M.pmf l * M.value x y l|) := by
                simp [f]
          _ = (Finset.univ.sum fun l => M.pmf l) := hsum
          _ = (1 : ℝ) := by simpa using M.pmf_sum_one
      calc
        |Finset.univ.sum f| ≤ (Finset.univ.sum fun l => |f l|) := habs
        _ = (1 : ℝ) := habsSum
    exact abs_le.mp hEabs

end LocalHiddenVariableModel

end CHSH
end Bell
end Quantum
end Crypto
end HeytingLean

