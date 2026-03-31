import Mathlib.CategoryTheory.Types.Basic
import HeytingLean.ClosingTheLoop.MR.ClosureOperator
import HeytingLean.ClosingTheLoop.Cat.Concreteness

/-!
# ClosingTheLoop.MR.YonedaBridge

Bridge the MR selector-closure endomorphism to the categorical Yoneda-idempotence
reflection theorem.
-/

namespace HeytingLean
namespace ClosingTheLoop
namespace MR

open CategoryTheory

universe u v

variable {S : MRSystem.{u, v}} {b : S.B}

/-- The selector-loop closure operator as an endomorphism in `Type`. -/
def selectorEndomorphism (RI : RightInverseAt S b) :
    Selector S ⟶ Selector S :=
  closeSelector S b RI

theorem selectorEndomorphism_idem (RI : RightInverseAt S b) :
    selectorEndomorphism (S := S) (b := b) RI ≫
      selectorEndomorphism (S := S) (b := b) RI =
    selectorEndomorphism (S := S) (b := b) RI := by
  funext Φ
  simpa [selectorEndomorphism] using
    (closeSelector.idem (S := S) (b := b) (RI := RI) Φ)

/-- If the Yoneda image of selector closure is idempotent, closure is idempotent. -/
theorem selector_closure_is_yoneda_idempotent (RI : RightInverseAt S b)
    (hYoneda :
      (CategoryTheory.yoneda.map (selectorEndomorphism (S := S) (b := b) RI)) ≫
          (CategoryTheory.yoneda.map (selectorEndomorphism (S := S) (b := b) RI)) =
        CategoryTheory.yoneda.map (selectorEndomorphism (S := S) (b := b) RI)) :
    selectorEndomorphism (S := S) (b := b) RI ≫
      selectorEndomorphism (S := S) (b := b) RI =
    selectorEndomorphism (S := S) (b := b) RI :=
  Cat.idem_of_yoneda_map_idem
    (C := Type (max u v))
    (X := Selector S)
    (f := selectorEndomorphism (S := S) (b := b) RI)
    hYoneda

end MR
end ClosingTheLoop
end HeytingLean
