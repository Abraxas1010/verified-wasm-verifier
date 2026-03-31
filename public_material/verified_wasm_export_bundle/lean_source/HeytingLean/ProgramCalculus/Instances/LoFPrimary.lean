import HeytingLean.ProgramCalculus.Futamura
import HeytingLean.LoF.Correspondence.LoFPrimarySKYBoolNary

/-!
# ProgramCalculus.Instances.LoFPrimary

Concrete instantiation of the `ProgramCalculus` interfaces for the LoFPrimary Boolean fragment.

This is the first “running mix equation” already proved in the repo:

* `specialize0` specializes the first Boolean variable (static input),
* `eval_specialize0` is the corresponding specialization correctness theorem.
-/

namespace HeytingLean
namespace ProgramCalculus
namespace Instances

/-- LoFPrimary programs with `(n+1)` Boolean variables, evaluated under a Boolean environment. -/
def loFPrimaryLanguage (n : Nat) : Language where
  Program := HeytingLean.LoF.LoFPrimary.Expr (n + 1)
  Input := Fin (n + 1) → Bool
  Output := Bool
  eval := fun program input => HeytingLean.LoF.LoFPrimary.eval (n := n + 1) program input

/-- Split the `(n+1)`-variable environment into head (`Bool`) and tail (`Fin n → Bool`). -/
def loFPrimarySplit (n : Nat) : SplitInput (Fin (n + 1) → Bool) where
  Static := Bool
  Dynamic := Fin n → Bool
  pack := fun head tail =>
    HeytingLean.LoF.Correspondence.LoFPrimary.Expr.extendEnv (n := n) head tail

/-- The LoFPrimary `Mix`: `specialize0` together with its correctness theorem. -/
def loFPrimaryMix (n : Nat) :
    Mix (loFPrimaryLanguage n) (loFPrimarySplit n) where
  Residual := HeytingLean.LoF.LoFPrimary.Expr n
  evalResidual := fun program input => HeytingLean.LoF.LoFPrimary.eval (n := n) program input
  apply := fun program head =>
    HeytingLean.LoF.Correspondence.LoFPrimary.Expr.specialize0 (n := n) head program
  correct := by
    intro program head tail
    simpa [loFPrimaryLanguage, loFPrimarySplit] using
      (HeytingLean.LoF.Correspondence.LoFPrimary.Expr.eval_specialize0
        (n := n) (A := program) (b := head) (ρ := tail))

end Instances
end ProgramCalculus
end HeytingLean
