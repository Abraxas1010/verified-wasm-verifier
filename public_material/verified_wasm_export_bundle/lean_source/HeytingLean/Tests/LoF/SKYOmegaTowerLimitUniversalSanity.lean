import HeytingLean.LoF.Combinators.Category.OmegaTowerLimitUniversal

/-!
# Smoke test: strict ω-limit universal property for the Arrow tower
-/

namespace HeytingLean
namespace Tests
namespace LoF

open CategoryTheory
open HeytingLean.LoF.Combinators.Category

#check TowerCone
#check TowerCone.lift
#check TowerCone.lift_fac
#check TowerCone.lift_uniq

end LoF
end Tests
end HeytingLean

