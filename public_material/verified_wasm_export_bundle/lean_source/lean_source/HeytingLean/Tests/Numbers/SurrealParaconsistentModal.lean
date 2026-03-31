import HeytingLean.Numbers.Surreal.ParaconsistentModal

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Numbers.Surreal.ParaconsistentModal
open HeytingLean.Noneism.RM

#check non_explosion_witness
#check explosion_implication_fails

example :
    sat model ρ .w0 (.and φp (.not φp)) ∧ ¬ sat model ρ .w0 φq := by
  simpa using non_explosion_witness

example :
    ¬ sat model ρ .w0 (.imp (.and φp (.not φp)) φq) := by
  simpa using explosion_implication_fails

end Numbers
end Tests
end HeytingLean
