import HeytingLean.Logic.StageSemantics
import HeytingLean.Logic.StageOML

namespace HeytingLean
namespace CLI

open HeytingLean.Logic
open HeytingLean.Logic.Stage

-- Provide an OML instance on Bool for demo purposes.
instance : Stage.OmlCore Bool where
  meet := fun a b => (a && b)
  join := fun a b => (a || b)
  compl := fun a => !a
  bot := false
  top := true

def QuantumDemo.run : IO Unit := do
  -- Identity bridge Bool ↔ Bool
  let B : Bridge Bool Bool :=
    { shadow := id, lift := id, rt₁ := by intro u; rfl, rt₂ := by intro x; exact le_rfl }
  let x := true; let y := false
  let sMeet := B.stageOmlMeet x y
  let sJoin := B.stageOmlJoin x y
  let sCompl := B.stageOmlCompl x
  IO.println s!"Quantum demo (Bool): meet={sMeet} join={sJoin} compl={sCompl}"

end CLI
end HeytingLean

def main : IO Unit :=
  HeytingLean.CLI.QuantumDemo.run
