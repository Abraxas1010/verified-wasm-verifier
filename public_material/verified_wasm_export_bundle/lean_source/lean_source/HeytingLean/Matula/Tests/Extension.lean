import HeytingLean.Matula.Extension.Hopf
import HeytingLean.Matula.Extension.Hyperseries

namespace HeytingLean
namespace Matula

open HeytingLean.Matula.Extension

example : Hopf.hopfMulCode 6 10 = 60 := by
  native_decide

example : Hopf.hopfMulCode Hopf.hopfUnitCode 17 = 17 := by
  native_decide

example : Hopf.hopfCounit Hopf.hopfUnit = 1 := by
  rfl

example : Hopf.hopfAntipode (.node []) = .leaf := by
  native_decide

example : Hopf.hopfMul .leaf (.node [.leaf]) = .node [.leaf] := by
  native_decide

example : Hopf.hopfMul (.node [.leaf]) (.node [.leaf]) = .node [.leaf, .leaf] := by
  native_decide

example : Hopf.hopfComul .leaf = [([], .leaf)] := by
  native_decide

example : (Hopf.hopfComul (.node [.leaf])).length = 2 := by
  native_decide

example : (Hopf.hopfComul (.node [.leaf])).contains ([.leaf], .leaf) = true := by
  native_decide

example : (Hopf.hopfComul (.node [.leaf])).contains ([], .node [.leaf]) = true := by
  native_decide

example : (Hopf.hopfComul (.node [.leaf, .leaf])).length = 4 := by
  native_decide

example :
    Hyperseries.fromCodeExpr (Hyperseries.toCodeExpr (.node [.leaf])) = some 2 := by
  native_decide

example :
    Hyperseries.decodeCodeExpr (Hyperseries.toCodeExpr (.node [.leaf])) = some (.node [.leaf]) := by
  native_decide

example :
    Hyperseries.decodeCodeExpr (Hyperseries.toCodeExpr (.node [])) = some .leaf := by
  native_decide

example :
    Hyperseries.fromCodeExpr (HeytingLean.Hyperseries.HExpr.X) = none := by
  rfl

example :
    Hyperseries.decodeCodeExpr (HeytingLean.Hyperseries.HExpr.C (-3)) = none := by
  native_decide

example :
    Hyperseries.toHExpr (.node [.leaf]) =
      HeytingLean.Hyperseries.HExpr.mul
        (HeytingLean.Hyperseries.HExpr.exp HeytingLean.Hyperseries.HExpr.X)
        (HeytingLean.Hyperseries.HExpr.C 1) := by
  simp

example :
    Hyperseries.toHExpr (.node [.leaf, .leaf]) =
      HeytingLean.Hyperseries.HExpr.mul
        (HeytingLean.Hyperseries.HExpr.exp HeytingLean.Hyperseries.HExpr.X)
        (HeytingLean.Hyperseries.HExpr.mul
          (HeytingLean.Hyperseries.HExpr.exp HeytingLean.Hyperseries.HExpr.X)
          (HeytingLean.Hyperseries.HExpr.C 1)) := by
  simp [Hyperseries.toHExpr]

example : Hyperseries.fromHExpr (Hyperseries.toHExpr (.node [.leaf])) = some (.node [.leaf]) := by
  native_decide

example : Hyperseries.fromHExpr (Hyperseries.toHExpr (.node [])) = some (.node []) := by
  native_decide

example : Hyperseries.fromHExpr (Hyperseries.toHExpr .leaf) = some .leaf := by
  native_decide

example : Hyperseries.toHExpr (.node [.leaf]) ≠ Hyperseries.toHExpr (.node []) := by
  intro h
  have hTree := Hyperseries.toHExpr_injective h
  cases hTree

example :
    HeytingLean.Hyperseries.HExpr.eval HeytingLean.Hyperseries.surrealModel
      (Hyperseries.toHExpr .leaf) = HeytingLean.Hyperseries.omegaSurreal := by
  simp

end Matula
end HeytingLean
