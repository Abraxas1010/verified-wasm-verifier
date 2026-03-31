import HeytingLean.Crypto.KEM.MLKEMFailureAxiomExport

namespace HeytingLean.Tests.Crypto.PQCLatticeFailureAxiomExportSanity

open HeytingLean.Crypto.KEM.FIPS203
open HeytingLean.Crypto.KEM.FIPS203.FailureAxiomExport

example :
    failureProbability mlkem768 < reportedFailureBoundQ mlkem768 :=
  mlkem768_failure_bound_assumed

end HeytingLean.Tests.Crypto.PQCLatticeFailureAxiomExportSanity
