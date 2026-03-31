import HeytingLean.Physics.String.QSeries
import HeytingLean.Physics.String.ModularQ
import HeytingLean.Physics.String.Spec.QSeriesN
import HeytingLean.Physics.String.Spec.QSeriesNToRuntime

namespace HeytingLean
namespace CLI

open HeytingLean.Physics.String
open HeytingLean.Physics.String.Spec

def StringQDemo.run : IO Unit := do
  -- Tiny 3-dim example with simple integer matrices S,T
  let mats : ModMatrices :=
    { S := #[(#[(1.0), (1.0), (0.0)]), (#[(1.0), (1.0), (0.0)]), (#[(0.0), (0.0), (1.0)])]
    , T := #[(#[(1.0), (0.0), (0.0)]), (#[(0.0), (-1.0), (0.0)]), (#[(0.0), (0.0), (1.0)])] }
  let N : QNucleus := { mats := mats, steps := 6 }
  let q : QSeries := { coeffs := #[1.0, 0.0, 1.0] }
  let canon := (QNucleus.project N q).coeffs
  IO.println s!"String Q-series demo — q={q.coeffs} canonical={canon}"
  -- Spec-level QSeriesN example bridged into the runtime QSeries.
  let ws : List Nat := [0, 1, 1, 2]
  let qn : QSeriesN := QSeriesN.fromWeights ws
  let qnRuntime : QSeries := QSeriesN.toRuntime qn
  IO.println s!"Spec QSeriesN={qn.coeffs} runtime cast={qnRuntime.coeffs}"

end CLI
end HeytingLean

def main : IO Unit :=
  HeytingLean.CLI.StringQDemo.run
