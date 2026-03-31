import HeytingLean.Math.ProbVec

/-
Compile-only sanity for ProbVec (Real-valued probability vectors).
-/

namespace HeytingLean
namespace Tests
namespace Math

open HeytingLean.Math

def xs : Array ℝ := #[1.0, 1.0]
def p  : ProbVec := ProbVec.normalizeR xs
def n  : Nat := p.length
def x0 : ℝ := p.get! 0

end Math
end Tests
end HeytingLean

