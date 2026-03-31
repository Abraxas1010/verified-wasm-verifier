import Lean
import HeytingLean.CLI.EnvBootstrap
import HeytingLean.Tests.KernelAssurance.Fixture
import HeytingLean.Util.ModuleOwner

namespace HeytingLean.Tests.KernelAssurance.ModuleOwner

open Lean

#eval show IO Unit from do
  HeytingLean.CLI.EnvBootstrap.bootstrapSearchPath
  let env ←
    Lean.importModules
      #[{ module := `HeytingLean.Tests.KernelAssurance.Fixture }]
      {}
  let theoremOwner := HeytingLean.Util.moduleOwnerOf env ``HeytingLean.Tests.KernelAssurance.fixtureTruth
  let defOwner := HeytingLean.Util.moduleOwnerOf env ``HeytingLean.Tests.KernelAssurance.fixtureNat
  let expected := `HeytingLean.Tests.KernelAssurance.Fixture
  unless theoremOwner == expected do
    throw <| IO.userError s!"fixtureTruth owner mismatch: expected {expected}, got {theoremOwner}"
  unless defOwner == expected do
    throw <| IO.userError s!"fixtureNat owner mismatch: expected {expected}, got {defOwner}"

end HeytingLean.Tests.KernelAssurance.ModuleOwner
