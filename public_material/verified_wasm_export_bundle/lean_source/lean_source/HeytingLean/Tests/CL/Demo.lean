import HeytingLean.Logic.StageSemantics
import HeytingLean.Logic.Computability.ChoiceParallel
import HeytingLean.Logic.Computability.Bang

/-!
Compile-only demo instances for CL skeletons on `Nat`, plus an identity
bridge to exercise staged transports without adding any runtime CLIs.
-/

namespace HeytingLean
namespace Tests
namespace CL

open HeytingLean.Logic
open HeytingLean.Logic.Stage
open HeytingLean.Logic.Computability

-- Parallel/Choice/Bang instances on Nat (simple but fully specified semantics)
instance : ParallelCore Nat where
  pand := Nat.max
  por  := Nat.min

instance : ChoiceCore Nat where
  uchoice a _ := a   -- environment picks left
  tchoice _ b := b   -- machine picks right

instance : BangCore Nat where
  bang := id         -- trivial, idempotent “reuse”

-- Identity bridge Nat ↔ Nat (needs `LE Nat` which is in the prelude)
def idBridgeNat : Bridge Nat Nat where
  shadow := id
  lift   := id
  rt₁    := by intro u; rfl
  rt₂    := by intro x; exact le_rfl

-- Staged operations compile and produce Nat values.
def demoPand : Nat := (idBridgeNat).stagePand 3 5   -- = 5 (max)
def demoPor  : Nat := (idBridgeNat).stagePor 3 5    -- = 3 (min)
def demoU    : Nat := (idBridgeNat).stageU 3 5      -- = 3 (left)
def demoT    : Nat := (idBridgeNat).stageT 3 5      -- = 5 (right)
def demoBang : Nat := (idBridgeNat).stageBang 7     -- = 7 (id)

-- Bundle to ensure everything is referenced
def demoPack : Nat × Nat × Nat × Nat × Nat :=
  (demoPand, demoPor, demoU, demoT, demoBang)

end CL
end Tests
end HeytingLean
