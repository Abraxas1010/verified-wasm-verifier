import Mathlib.Data.Set.Lattice
import HeytingLean.LoF.ClosureCore
import HeytingLean.Numbers.Surreal.Nucleus

/-!
# Surreal J-closure as a ClosureCore

Wraps `Surreal.Core.J : Set PreGame → Set PreGame` as a `ClosureCore`.
This does NOT require meet preservation; hence no Heyting instance is
derived here. Use the nucleus-based Option A (`ClosureReentry`) to obtain
`HeytingAlgebra` on fixed points.
-/

namespace HeytingLean
namespace Numbers
namespace Surreal

open Set
open HeytingLean.LoF
open HeytingLean.Numbers.SurrealCore

def JClosureCore : LoF.ClosureCore (Set PreGame) where
  act := Core.J
  monotone := by
    intro S T hST; exact Core.mono_J hST
  le_apply := by
    intro S; exact Core.subset_J S
  idempotent := by
    intro S; exact Core.idem_J S

abbrev Ω_J : Type _ := (JClosureCore).Omega

end Surreal
end Numbers
end HeytingLean

