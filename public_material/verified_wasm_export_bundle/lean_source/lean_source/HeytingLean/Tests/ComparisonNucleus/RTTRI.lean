import HeytingLean.LoF.ComparisonNucleus

/-!
# Comparison nucleus RTTRI smoke (compile-only)

Construct a trivial `CompSpec` on `Set Nat` and check `RT1` compiles.
-/

namespace HeytingLean
namespace Tests
namespace ComparisonNucleus

open HeytingLean.LoF.Comparison

def compId : CompSpec (Set Nat) (Set Nat) where
  f := id
  g := id
  mon_f := by intro _ _ h; exact h
  mon_g := by intro _ _ h; exact h
  gc := by
    intro a b; constructor <;> intro h <;> simpa using h

-- compile-only check that RT1 is available on the trivial pack
#check (RT1 (S := compId))

end ComparisonNucleus
end Tests
end HeytingLean
