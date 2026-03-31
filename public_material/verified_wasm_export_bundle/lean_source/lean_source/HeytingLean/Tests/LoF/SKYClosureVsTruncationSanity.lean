import HeytingLean.LoF.Combinators.Topos.ClosureVsTruncation
import HeytingLean.LoF.Combinators.Topos.MWObjSite
import HeytingLean.LoF.Combinators.Topos.SievePresheaf
import HeytingLean.LoF.Combinators.Topos.StepsSite

/-!
Compile-only sanity checks for Phase C (closure vs truncation).

We check:
* the `Trunc (LSteps t u)` ↔ thin `t ⟶ u` boundary equivalence,
* closed sieves for the dense topology are nontrivial,
* Grothendieck closure is a natural transformation of the sieve presheaf,
* the dense-topology infrastructure exists on the non-thin multiway category.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open CategoryTheory
open HeytingLean.LoF.Combinators.Category
open HeytingLean.LoF.Combinators.Topos

variable {t u : StepsCat}

#check TruncationBoundary.truncLStepsEquivStepsHom (t := t) (u := u)

variable {X : StepsCat}

#check DenseTopology.not_subsingleton_closedSieve_dense (C := StepsCat) (X := X)

section

universe v u
variable {C : Type u} [Category.{v} C]

#check sievePresheaf (C := C)
#check closeNatTrans (C := C) (J := (GrothendieckTopology.dense : GrothendieckTopology C))

end

variable {XMW : MWObj}

#check mwDenseTopology
#check ClosedSieve (C := MWObj) mwDenseTopology XMW
#check closedSieve_instHeyting (C := MWObj) mwDenseTopology XMW

end LoF
end Tests
end HeytingLean

