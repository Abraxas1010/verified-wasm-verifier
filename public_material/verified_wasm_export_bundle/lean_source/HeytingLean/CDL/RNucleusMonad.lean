import HeytingLean.CDL.StrongMonad

/-!
# CDL: `R`-nuclei as strong monads (interface)

In the Closure/HeytingLean narrative, a *nucleus* `R` is an idempotent, inflationary operator
on a lattice/locale/Heyting algebra.  To use the same symbol `R` as the “monadic driver” for
Categorical Deep Learning (CDL) constraints on computational carriers, we need an `R` that acts
as a (strong) monad on `Type`.

This file provides a lightweight interface `RNucleusMonad` used by the CDL layer.  At this stage
it is intentionally minimal: CDL only needs the *strong monad* structure (so we can form `Para(R)`
and transport parametric maps).

Concrete instances tying this interface to HeytingLean’s logical nucleus are handled by lenses
(`ProofTerm`/carrier choices) elsewhere; this file just standardizes the name.
-/

namespace HeytingLean
namespace CDL

universe u

/-- A computational `R`-nucleus for the CDL layer: a strong monad on `Type`. -/
class RNucleusMonad (R : Type u → Type u) : Type (u + 1) extends StrongMonad R

-- Any strong monad can be viewed as an `RNucleusMonad`.
instance (priority := 100) (R : Type u → Type u) [StrongMonad R] : RNucleusMonad R where
  toStrongMonad := inferInstance

-- Sanity checks.
example : RNucleusMonad Id := by infer_instance
example : RNucleusMonad Option := by infer_instance

end CDL
end HeytingLean

