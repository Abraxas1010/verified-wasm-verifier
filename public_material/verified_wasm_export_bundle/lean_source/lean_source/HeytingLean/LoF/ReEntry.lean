import HeytingLean.LoF.LoFSecond.Rewrite

/-!
# Re-entry and eigenforms (bundle slice)

The existing LoF development in this repo models “re-entry” as a *distinguished
constant* in `LoFSecond.Expr` together with a rewrite rule

`mark reentry ↦ reentry`.

For the standalone bundle we package this as an “eigenform” interface: an
expression is an eigenform if marking it rewrites back to itself.
-/

namespace HeytingLean
namespace LoF

open LoFSecond

/-- An eigenform is a fixed point of `mark`, up to `LoFSecond.Steps`. -/
structure Eigenform (n : Nat) where
  val : LoFSecond.Expr n
  is_eigenform : LoFSecond.Steps (LoFSecond.Expr.mark val) val

/-- A typeclass packaging the existence of a distinguished eigenform. -/
class HasImaginary (n : Nat) where
  imaginary : LoFSecond.Expr n
  imaginary_eigenform : LoFSecond.Steps (LoFSecond.Expr.mark imaginary) imaginary

/-- The built-in re-entry constant. -/
def reentry {n : Nat} : LoFSecond.Expr n :=
  LoFSecond.Expr.reentry

/-- `reentry` is an eigenform (by the re-entry rewrite rule). -/
theorem reentry_is_eigenform {n : Nat} :
    LoFSecond.Steps (LoFSecond.Expr.mark (reentry (n := n))) (reentry (n := n)) := by
  exact LoFSecond.Steps.trans LoFSecond.Step.reentry (LoFSecond.Steps.refl _)

instance (n : Nat) : HasImaginary n where
  imaginary := reentry (n := n)
  imaginary_eigenform := reentry_is_eigenform (n := n)

/-- Iterated marking. -/
def iterate_mark {n : Nat} (a : LoFSecond.Expr n) : Nat → LoFSecond.Expr n
  | 0 => a
  | Nat.succ k => LoFSecond.Expr.mark (iterate_mark a k)

/-- Second re-entry: “the system seeing itself seeing itself”. -/
def second_reentry {n : Nat} [HasImaginary n] : LoFSecond.Expr n :=
  LoFSecond.Expr.mark (LoFSecond.Expr.mark (HasImaginary.imaginary (n := n)))

end LoF
end HeytingLean

