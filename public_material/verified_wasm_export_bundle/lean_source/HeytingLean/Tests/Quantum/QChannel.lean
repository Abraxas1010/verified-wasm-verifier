import HeytingLean.Quantum.QChannel

namespace HeytingLean.Tests.Quantum

open HeytingLean Quantum

noncomputable section

open KrausChannel

def trivialKraus : KrausChannel 1 1 :=
  KrausChannel.id 1

example : KrausChannel.map trivialKraus (0 : Mat 1) = 0 := by
  classical
  simp

end

end HeytingLean.Tests.Quantum
