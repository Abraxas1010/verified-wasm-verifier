import HeytingLean.ATP.Ensemble.ConstructivityCheck

namespace HeytingLean.PTS.BaseExtension.Demo

open HeytingLean.ATP.Ensemble
open HeytingLean.PTS.BaseExtension

def constructiveCertificate : ConstructivityReport :=
  checkSkeleton 7 [] (extractPeirce ⟨0⟩ ⟨1⟩)

end HeytingLean.PTS.BaseExtension.Demo
