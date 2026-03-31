import HeytingLean.Physics.String.QSeries
import HeytingLean.Physics.String.Spec.QSeriesN

/-
Bridge from the proof-friendly `QSeriesN` (with `Nat` coefficients)
to the runtime `QSeries` (with `Float` coefficients).

The intent is to keep specification lemmas in `QSeriesN` while
providing a concrete executable view for demos and CLI examples.
-/

namespace HeytingLean
namespace Physics
namespace String
namespace Spec

open HeytingLean.Physics.String
open QSeriesN

namespace QSeriesN

/-- View a `QSeriesN` as a runtime `QSeries` by casting coefficients to `Float`. -/
@[simp] def toRuntime (q : QSeriesN) : HeytingLean.Physics.String.QSeries :=
  { coeffs :=
      Array.mk (q.coeffs.map (fun (n : Nat) => Float.ofInt (Int.ofNat n))) }

/-- The runtime view preserves the truncated length. -/
@[simp] theorem toRuntime_length (q : QSeriesN) :
    (QSeriesN.toRuntime q).length = q.length := by
  simp [QSeriesN.toRuntime, QSeriesN.length, QSeries.length]

end QSeriesN

end Spec
end String
end Physics
end HeytingLean
