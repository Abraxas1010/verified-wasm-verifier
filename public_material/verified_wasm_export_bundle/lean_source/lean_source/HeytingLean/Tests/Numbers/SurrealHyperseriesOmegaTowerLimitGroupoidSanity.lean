import HeytingLean.Hyperseries.Category.OmegaTowerLimitGroupoid

namespace HeytingLean
namespace Tests
namespace Numbers

open CategoryTheory
open HeytingLean.Hyperseries.Category

noncomputable section

example : Groupoid HGOmegaLeft := by
  infer_instance

example : Groupoid HGOmegaRight := by
  infer_instance

end
end Numbers
end Tests
end HeytingLean
