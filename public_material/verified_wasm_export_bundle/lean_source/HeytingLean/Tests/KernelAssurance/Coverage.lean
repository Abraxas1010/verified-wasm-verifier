import HeytingLean.Tests.KernelAssurance.Fixture

namespace HeytingLean.Tests.KernelAssurance.Coverage

open HeytingLean.KernelAssurance
open HeytingLean.Tests.KernelAssurance

example : (CoverageReport.ofBundle supportedBundle).blockedDecls = 0 := by native_decide
example : (CoverageReport.ofBundle mixedBundle).blockedDecls = 1 := by native_decide
example : (CoverageReport.ofBundle supportedBundle).blockedFamilyCount = 0 := by native_decide

end HeytingLean.Tests.KernelAssurance.Coverage
