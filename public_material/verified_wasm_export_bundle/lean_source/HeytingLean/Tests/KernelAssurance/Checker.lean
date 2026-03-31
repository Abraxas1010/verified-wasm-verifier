import HeytingLean.Tests.KernelAssurance.Fixture

namespace HeytingLean.Tests.KernelAssurance.Checker

open HeytingLean.KernelAssurance
open HeytingLean.Tests.KernelAssurance

example : (CheckerReport.ofBundle supportedBundle).failed = 0 := by native_decide
example : (CheckerReport.ofBundle tamperedBundle).tamperFailures > 0 := by native_decide

end HeytingLean.Tests.KernelAssurance.Checker
