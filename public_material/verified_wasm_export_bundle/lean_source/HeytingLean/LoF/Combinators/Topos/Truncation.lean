import HeytingLean.LoF.Combinators.Topos.Localization

/-!
# Truncation — quotienting sieves by `J.close`

This is a *poset-level* “truncation-like” construction:

* define an equivalence relation `S ~ T` iff `J.close S = J.close T`;
* show the quotient is equivalent to the type of closed sieves (the range of `J.close`).

This is not HoTT truncation; it is the standard kernel-quotient of an idempotent reflector.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Topos

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

section

variable (J : GrothendieckTopology C) (X : C)

def closeSetoid : Setoid (Sieve X) where
  r := fun S T => J.close S = J.close T
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro S
      rfl
    · intro S T h
      exact h.symm
    · intro S T U hST hTU
      exact hST.trans hTU

abbrev CloseQuot : Type _ :=
  Quot (closeSetoid (J := J) X)

noncomputable def quotToClosed : CloseQuot (J := J) X → ClosedSieve (C := C) J X :=
  Quot.lift (fun S => ⟨J.close S, ⟨S, rfl⟩⟩) (by
    intro S T h
    apply Subtype.ext
    simpa using h)

noncomputable def closedToQuot : ClosedSieve (C := C) J X → CloseQuot (J := J) X :=
  fun T => Quot.mk _ T.1

noncomputable def closeQuotEquivClosed : CloseQuot (J := J) X ≃ ClosedSieve (C := C) J X := by
  classical
  refine
    { toFun := quotToClosed (C := C) (J := J) X
      invFun := closedToQuot (C := C) (J := J) X
      left_inv := ?_
      right_inv := ?_ }
  · intro q
    refine Quot.inductionOn q ?_
    intro S
    -- `S` and `J.close S` are equivalent in the quotient by idempotence of closure.
    apply Quot.sound
    change J.close (J.close S) = J.close S
    exact J.close_close S
  · intro T
    apply Subtype.ext
    change J.close T.1 = T.1
    rcases T.2 with ⟨S, hS⟩
    have hS' : J.close S = T.1 := by
      simpa using hS
    calc
      J.close T.1 = J.close (J.close S) := by simp [hS'.symm]
      _ = J.close S := by simp
      _ = T.1 := hS'

end

end Topos
end Combinators
end LoF
end HeytingLean
