import HeytingLean.Process.Syntax
import HeytingLean.Process.Typing
import HeytingLean.Process.Semantics
import HeytingLean.Process.Nucleus
import HeytingLean.Process.Examples.Payment

/-! Compile-only sanity checks for the Process lens. -/

namespace HeytingLean
namespace Tests
namespace Process

open HeytingLean.Process

-- Ensure basic symbols are available and types check by instantiating the
-- kernel and a trivial process.
def _kernelDemo : Process.ProcessKernel := Process.kernel

example : HeytingLean.Process.Proc := HeytingLean.Process.Proc.nil

end Process
end Tests
end HeytingLean
