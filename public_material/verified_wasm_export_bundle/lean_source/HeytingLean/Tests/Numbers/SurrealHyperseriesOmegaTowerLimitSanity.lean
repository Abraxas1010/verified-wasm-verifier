import HeytingLean.Hyperseries.Category.OmegaTowerLimit

namespace HeytingLean
namespace Tests
namespace Numbers

open CategoryTheory
open HeytingLean.Hyperseries.Category
open HeytingLean.LoF.Combinators.Category (TowerLimit)

#check HLeftTower
#check HRightTower
#check TowerLimit

example : Category (TowerLimit HLeftTower) := by
  infer_instance

example : Category (TowerLimit HRightTower) := by
  infer_instance

end Numbers
end Tests
end HeytingLean
