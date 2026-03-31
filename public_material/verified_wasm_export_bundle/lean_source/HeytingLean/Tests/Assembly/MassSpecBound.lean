import HeytingLean.ATheory.AssemblyCore
import HeytingLean.Bridges.Assembly.MassSpec

/-
# MassSpecBound tests

A small compile-only check relating the assembly index on a trivial object
to the MA upper bound derived from a synthetic fragmentation graph.
-/

namespace HeytingLean
namespace Tests
namespace Assembly

open HeytingLean.ATheory
open HeytingLean.Bridges.Assembly

/-- Trivial rule set on natural parts, used to relate assembly index to the
fragmentation-based MA upper bound. -/
def natRules : Rules Nat where
  compose _ _ := {}

/-- For any spectrum, the syntactic index of the base object `0` is bounded
above by the MA upper bound computed from the linear-chain fragmentation
graph derived from the spectrum. -/
example (δ : ℝ) (S : Spectrum) :
    syntacticIndex natRules (Obj.base (0 : Nat))
      ≤ maUpperBound (fragGraph δ S) := by
  -- The index of a base object is zero by definition of `canonicalPath`.
  have hidx : syntacticIndex natRules (Obj.base (0 : Nat)) = 0 := rfl
  -- The MA upper bound is a list length, hence a natural number ≥ 0.
  have hle : 0 ≤ maUpperBound (fragGraph δ S) :=
    Nat.zero_le _
  rw [hidx]
  exact hle

end Assembly
end Tests
end HeytingLean
