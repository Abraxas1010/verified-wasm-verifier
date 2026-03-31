import HeytingLean.Numbers.Surreal.Experimental.HaltingSync

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Numbers.Surreal
open HeytingLean.Numbers.Surreal.Experimental

example : classify 3 (toyProcess 0 5) = .halt :=
  toyProcess_halts_classification 3 5

example : classify 0 (toyProcess 2 3) = .horizon := by
  apply toyProcess_horizon_classification
  · decide
  · decide

example :
    classify 5 (toyProcess 2 1) = .running := by
  apply classify_running_of_not_halt_not_horizon
  · simp [halts, toyProcess]
  · simp [horizonBlocked, horizon, toyProcess]

end Numbers
end Tests
end HeytingLean
