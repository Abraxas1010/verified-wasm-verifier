import HeytingLean.LoF.Correspondence.LoFSKY
import HeytingLean.LoF.Combinators.Topos.Truncation
import HeytingLean.LoF.MRSystems.Truncation

/-!
# Synthesis (scoped): kernel quotients + LoF⇄SKY renaming

This module collects the **provable core** of the SKY–Heyting–∞-groupoid program inside this
repository.  In particular:

1. `LoFTerm.toSKY` is a bijective renaming between a minimal LoF-combinator syntax and SKY terms,
   and it preserves the corresponding (renamed) rewrite relation.
2. Both Grothendieck closure on sieves (`J.close`) and selector closure in the Tier-1 (M,R) scaffold
   (`closeSelector`) induce the same *kernel-quotient pattern*:
   quotient by `x ~ y :↔ close x = close y` is equivalent to the range/fixed points of `close`.

Anything beyond this (e.g. higher-cell / ∞-groupoid limits, HoTT truncation, or a full LoF calculus)
is treated as *research agenda*, not as a proved statement here.
-/

namespace HeytingLean
namespace LoF
namespace Synthesis

/-! ## Generic kernel-quotient lemma for idempotent endomorphisms -/

namespace KernelQuotient

open Classical

universe u

variable {α : Type u} (close : α → α)

/-- The kernel setoid induced by an endomorphism `close`. -/
def closeSetoid : Setoid α where
  r := fun x y => close x = close y
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      rfl
    · intro x y h
      exact h.symm
    · intro x y z hxy hyz
      exact hxy.trans hyz

abbrev CloseQuot : Type _ :=
  Quot (closeSetoid close)

/-- The range of `close`, packaged as a type. -/
abbrev ClosedRange : Type _ :=
  {x : α // ∃ y : α, close y = x}

noncomputable def quotToRange : CloseQuot close → ClosedRange close :=
  Quot.lift (fun x => ⟨close x, ⟨x, rfl⟩⟩) (by
    intro x y h
    apply Subtype.ext
    simpa using h)

noncomputable def rangeToQuot : ClosedRange close → CloseQuot close :=
  fun T => Quot.mk _ T.1

noncomputable def closeQuotEquivRange (idem : ∀ x : α, close (close x) = close x) :
    CloseQuot close ≃ ClosedRange close := by
  classical
  refine
    { toFun := quotToRange close
      invFun := rangeToQuot close
      left_inv := ?_
      right_inv := ?_ }
  · intro q
    refine Quot.inductionOn q ?_
    intro x
    apply Quot.sound
    exact idem x
  · intro T
    apply Subtype.ext
    rcases T.2 with ⟨y, hy⟩
    calc
      close T.1 = close (close y) := by simp [hy.symm]
      _ = close y := by simp [idem y]
      _ = T.1 := hy

end KernelQuotient

/-! ## Instantiations present in this repo -/

namespace Instances

open Classical
open CategoryTheory

universe v u

section LoFSKY

open HeytingLean.LoF.Correspondence

theorem lofSteps_sound {t u : LoFTerm} :
    LoFStep.Steps t u → HeytingLean.LoF.Comb.Steps (LoFTerm.toSKY t) (LoFTerm.toSKY u) :=
  LoFStep.steps_toSKY

end LoFSKY

section Grothendieck

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (X : C)

/-- The sieve-closure kernel quotient is equivalent to `J`-closed sieves. -/
noncomputable def toposCloseQuotEquivClosed :
    HeytingLean.LoF.Combinators.Topos.CloseQuot (J := J) X ≃
      HeytingLean.LoF.Combinators.Topos.ClosedSieve (C := C) J X :=
  HeytingLean.LoF.Combinators.Topos.closeQuotEquivClosed (C := C) (J := J) X

end Grothendieck

section MR

universe u' v'

variable {S : HeytingLean.ClosingTheLoop.MR.MRSystem.{u', v'}} {b : S.B}
  (RI : HeytingLean.ClosingTheLoop.MR.RightInverseAt S b)

/-- The `closeSelector` kernel quotient is equivalent to the range of `closeSelector`. -/
noncomputable def mrCloseQuotEquivClosed :
    HeytingLean.LoF.MRSystems.CloseQuot (S := S) (b := b) RI ≃
      HeytingLean.LoF.MRSystems.ClosedSelector (S := S) (b := b) RI :=
  HeytingLean.LoF.MRSystems.closeQuotEquivClosed (S := S) (b := b) RI

end MR

end Instances

end Synthesis
end LoF
end HeytingLean
