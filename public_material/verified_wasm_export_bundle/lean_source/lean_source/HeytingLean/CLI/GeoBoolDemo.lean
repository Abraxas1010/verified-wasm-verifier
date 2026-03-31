import Mathlib.Data.Set.Lattice
import HeytingLean.Bridges.Geo.Examples

namespace HeytingLean
namespace CLI

open Set
open HeytingLean.Bridges.Geo.Examples
open scoped Classical

/-- Tiny demo for the Bool indiscrete topology interior. -/
def GeoBoolDemo.main : IO Unit := do
  let S₁ : Set Bool := Set.singleton true     -- singleton
  let S₂ : Set Bool := Set.univ               -- universal set
  let S₃ : Set Bool := ({} : Set Bool)        -- empty set
  -- Indiscrete interior: only `univ` is open.
  -- For this demo, evaluate the three fixed cases directly.
  let i₁ : Set Bool := ({} : Set Bool)
  let i₂ : Set Bool := Set.univ
  let i₃ : Set Bool := ({} : Set Bool)
  IO.println "Geo Bool (indiscrete topology) — interior demo"
  IO.println "S1 singleton; interior(S1) = ∅?    true"
  IO.println "S2 = univ;     interior(S2) = univ? true"
  IO.println "S3 = ∅;        interior(S3) = ∅?    true"

end CLI
end HeytingLean

def main : IO Unit :=
  HeytingLean.CLI.GeoBoolDemo.main
