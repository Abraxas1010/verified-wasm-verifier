import HeytingLean.Physics.String.CFT
import HeytingLean.Physics.String.Modular
import HeytingLean.Physics.String.ModNucleus

namespace HeytingLean
namespace CLI

open HeytingLean.Physics.String

def StringDemo.run : IO Unit := do
  let cft : WorldsheetCFT :=
    { name := "FreeBosonDemo", centralCharge := 1.0, partitionZ := #[1.0, 24.0, 324.0, 3200.0] }
  let Z0 := cft.partitionZ
  let N : ModNucleus := { steps := 4, closure := fun Z => closure Z 4 }
  let orb := N.closure Z0
  IO.println s!"String demo — partition Z0: {Z0}"
  IO.println s!"orbit (S,T) up to {N.steps} steps: {orb}"
  IO.println s!"fixed? {N.fixed Z0}"

end CLI
end HeytingLean

def main : IO Unit :=
  HeytingLean.CLI.StringDemo.run
