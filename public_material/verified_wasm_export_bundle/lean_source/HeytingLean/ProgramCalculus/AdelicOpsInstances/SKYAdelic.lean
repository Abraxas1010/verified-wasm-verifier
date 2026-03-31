import HeytingLean.ProgramCalculus.AdelicOps
import HeytingLean.LoF.Combinators.SKY
import HeytingLean.LoF.Combinators.SKYExec

/-!
# ProgramCalculus.AdelicOpsInstances.SKYAdelic

A non-trivial `AdelicProgramOps` instance for the SKY combinator language.

This is a *law-abiding* instance for the current interface:
- `mul` is syntactic application,
- `depth` is chosen so that `depth_mul` holds **exactly** (valuation additivity),
- `add`/`normalize`/`renormDiv` are deliberately simple but still satisfy the interface laws.

The intent is to provide a concrete target for executable QA (compile+run) without overcommitting
to a specific “adelic arithmetic = program transformation” semantics yet.
-/

namespace HeytingLean
namespace ProgramCalculus
namespace AdelicOpsInstances

open HeytingLean.Embeddings
open HeytingLean.LoF
open HeytingLean.LoF.Combinators

/-! ## A concrete SKY language -/

def skyLanguage (fuel : Nat := 100) : Language where
  Program := Comb
  Input := Comb
  Output := Comb
  eval := fun p i => SKYExec.reduceFuel fuel (Comb.app p i)

/-! ## Depth measures -/

def skyNodeCount : Comb → Nat
  | .K => 0
  | .S => 0
  | .Y => 0
  | .app f x => skyNodeCount f + skyNodeCount x + 1

def skyLeaves : Comb → Nat
  | .K => 1
  | .S => 1
  | .Y => 1
  | .app f x => skyLeaves f + skyLeaves x

/-- A lens-indexed “depth/valuation” for SKY terms.

Choices:
- `.omega`, `.graph`, and `.tensor` use `nodeCount+1`, so application becomes exactly additive.
- `.region`, `.clifford`, and `.topology` use `leaves`, which is already additive under application.
-/
def skyDepth (t : Comb) : Depth := fun lens =>
  match lens with
  | .omega    => ((skyNodeCount t + 1 : Nat) : Int)
  | .region   => ((skyLeaves t : Nat) : Int)
  | .graph    => ((skyNodeCount t + 1 : Nat) : Int)
  | .clifford => ((skyLeaves t : Nat) : Int)
  | .tensor   => ((skyNodeCount t + 1 : Nat) : Int)
  | .topology => ((skyLeaves t : Nat) : Int)
  | .matula   => ((skyNodeCount t + 1 : Nat) : Int)

/-! ## `AdelicProgramOps` instance -/

def skyAdelicProgramOps (fuel : Nat := 100) : AdelicProgramOps (skyLanguage fuel) where
  depth := skyDepth
  mul := Comb.app
  add := fun _a b => b
  normalize := id
  renormDiv := fun a _e => (Comb.K, a)

  depth_mul := by
    intro a b lens
    cases lens <;>
      simp [skyDepth, skyNodeCount, skyLeaves, Int.natCast_add, add_assoc, add_left_comm, add_comm]

  depth_add := by
    intro a b lens
    -- `add` returns `b`, so the required inequality is `min(da, db) ≤ db`.
    exact min_le_right (skyDepth a lens) (skyDepth b lens)

  depth_norm := by
    intro a lens
    simp [skyDepth]

  div_reconstruct := by
    intro a e
    -- `add` returns the residual `r = a`, so reconstruction is definitional.
    simp [ObsEq, skyLanguage]

end AdelicOpsInstances
end ProgramCalculus
end HeytingLean
