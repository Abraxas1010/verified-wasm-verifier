import HeytingLean.Crypto.VerifiedPQC.ExportParity

namespace HeytingLean.Tests.Crypto.VerifiedPQCExportParity

open HeytingLean
open HeytingLean.Crypto
open HeytingLean.Crypto.VerifiedPQC

example : parityCorpus.length = 5 := by
  native_decide

example : ∀ c ∈ parityCorpus, parityCaseHolds c := by
  exact parityCorpus_complete

example : acceptAllChecksFn 4 = 1 := by
  native_decide

example : acceptAllChecksFn 3 = 0 := by
  native_decide

end HeytingLean.Tests.Crypto.VerifiedPQCExportParity
