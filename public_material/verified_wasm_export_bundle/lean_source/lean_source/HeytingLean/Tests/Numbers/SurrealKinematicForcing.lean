import HeytingLean.Numbers.Surreal.Experimental.KinematicForcing

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Numbers.Surreal
open HeytingLean.Numbers.Surreal.Experimental

private def w0 : KinematicWorld := { stage := 0, velocity := 1 }
private def w1 : KinematicWorld := { stage := 2, velocity := 3 }

example : reaches w0 w1 := by
  simp [reaches, w0, w1]

example : horizon 0 w0 := by
  simp [horizon, w0]

example : unobtainable 0 w0 w1 := by
  exact horizon_implies_unobtainable_of_reaches (by simp [horizon, w0]) (by simp [reaches, w0, w1])

example : horizonCertificate 0 w0 w1 := by
  refine ⟨?_, ?_⟩
  · simp [horizon, w0]
  · simp [reaches, w0, w1]

example : unobtainable 0 w0 w1 := by
  exact horizonCertificate_implies_unobtainable (by
    refine ⟨?_, ?_⟩
    · simp [horizon, w0]
    · simp [reaches, w0, w1])

end Numbers
end Tests
end HeytingLean
