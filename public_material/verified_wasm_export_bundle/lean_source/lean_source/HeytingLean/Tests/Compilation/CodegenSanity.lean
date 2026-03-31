import HeytingLean.Compilation.Codegen.Unified
import HeytingLean.Examples.MatMul.Verified

/-!
# Compilation/codegen sanity checks

These are compile-time checks ensuring the extension modules are wired into the build.
-/

namespace HeytingLean
namespace Tests
namespace Compilation

open HeytingLean.Examples

def matmul_codegen_smoke : IO HeytingLean.Compilation.Codegen.GeneratedCode :=
  MatMul.generateMatMulCode (M := (1 : ℕ+)) (K := (1 : ℕ+)) (N := (1 : ℕ+))

example : True := by
  trivial

end Compilation
end Tests
end HeytingLean

