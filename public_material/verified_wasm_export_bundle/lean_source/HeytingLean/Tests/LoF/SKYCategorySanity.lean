import HeytingLean.LoF.Combinators.Category.MultiwayCategory
import HeytingLean.LoF.Combinators.Category.BranchialSpan
import HeytingLean.LoF.Combinators.Category.HigherCells

/-!
Compile-only sanity checks for the SKY multiway *path* category scaffolding.

This is intentionally lightweight: the topos layer uses the *thin* preorder category
on `Comb`, while these files introduce a separate wrapper `MWObj` with explicit
labeled paths as morphisms.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.Combinators.Category

-- Category instance exists on the wrapper type.
#check (inferInstance : CategoryTheory.Category MWObj)

-- Reflexive branchial-at-depth-0 witness exists.
example (t : Comb) : BranchialAt 0 t t :=
  BranchialAt.refl0 t

-- 2-cell interface is inhabited by reflexivity.
example (t : Comb) : PathHomotopy t t (.refl t) (.refl t) :=
  PathHomotopy.refl (.refl t)

end LoF
end Tests
end HeytingLean
