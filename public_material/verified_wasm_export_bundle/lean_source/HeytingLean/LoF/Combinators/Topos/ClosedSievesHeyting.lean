import HeytingLean.LoF.Combinators.Topos.SieveFrame
import HeytingLean.LoF.Combinators.Topos.SieveNucleus

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Topos

open CategoryTheory
open Order

universe v u

variable {C : Type u} [Category.{v} C]

/-!
# Closed sieves as stable truth values

For any Grothendieck topology `J`, the closure operation `J.close` is a nucleus on `Sieve X`.
Since `Sieve X` is a frame, the fixed points (equivalently, the range) form a frame as well.

This packages the standard “closed sieves form a complete Heyting algebra” fact in the same
`Order.Nucleus` convention used elsewhere.
-/

/-- The type of `J`-closed sieves on `X`, presented as the range of the sieve nucleus. -/
abbrev ClosedSieve (J : GrothendieckTopology C) (X : C) : Type _ :=
  Set.range (sieveNucleus (C := C) J X)

noncomputable def closedSieve_instFrame (J : GrothendieckTopology C) (X : C) :
    Order.Frame (ClosedSieve (C := C) J X) := by
  infer_instance

noncomputable def closedSieve_instHeyting (J : GrothendieckTopology C) (X : C) :
    HeytingAlgebra (ClosedSieve (C := C) J X) := by
  infer_instance

/-- Alternate presentation: the subtype of sieves satisfying `J.IsClosed`. -/
abbrev IsClosedSieve (J : GrothendieckTopology C) (X : C) : Type _ :=
  {S : Sieve X // J.IsClosed S}

/-- The two presentations of `J`-closed sieves (`range J.close` vs `J.IsClosed`) are equivalent. -/
noncomputable def closedSieveEquivIsClosed (J : GrothendieckTopology C) (X : C) :
    ClosedSieve (C := C) J X ≃ IsClosedSieve (C := C) J X := by
  classical
  refine
    { toFun := fun S => ?_
      invFun := fun S => ?_
      left_inv := ?_
      right_inv := ?_ }
  · let T : Sieve X := Classical.choose S.2
    have hT : (sieveNucleus (C := C) J X) T = S.1 := Classical.choose_spec S.2
    refine ⟨S.1, ?_⟩
    have hT' := hT
    simp [sieveNucleus] at hT'
    -- `S.1` is (noncomputably) presented as `J.close T`, hence is closed.
    simpa [hT'] using (J.close_isClosed T)
  · refine ⟨S.1, ?_⟩
    refine ⟨S.1, ?_⟩
    change J.close S.1 = S.1
    exact J.close_eq_self_of_isClosed S.2
  · intro S
    ext
    rfl
  · intro S
    ext
    rfl

end Topos
end Combinators
end LoF
end HeytingLean

