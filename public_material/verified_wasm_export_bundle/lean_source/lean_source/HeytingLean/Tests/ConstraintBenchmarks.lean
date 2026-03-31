import HeytingLean.Payments.CLI.PMTests

namespace HeytingLean.Tests.ConstraintBenchmarks

/-- Reuse the existing payment-policy checks and R1CS compilation smoke tests. -/
def main (args : List String) : IO UInt32 :=
  HeytingLean.Payments.CLI.PMTests.main args

end HeytingLean.Tests.ConstraintBenchmarks
