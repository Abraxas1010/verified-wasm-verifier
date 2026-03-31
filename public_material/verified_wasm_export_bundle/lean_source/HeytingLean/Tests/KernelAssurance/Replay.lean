import HeytingLean.Tests.KernelAssurance.Fixture

namespace HeytingLean.Tests.KernelAssurance.Replay

open HeytingLean.KernelAssurance
open HeytingLean.Tests.KernelAssurance

example : (ReplayReport.ofBundle supportedBundle).failed = 0 := by native_decide
example : (ReplayReport.ofBundle mixedBundle).skippedBlocked = 1 := by native_decide

end HeytingLean.Tests.KernelAssurance.Replay
