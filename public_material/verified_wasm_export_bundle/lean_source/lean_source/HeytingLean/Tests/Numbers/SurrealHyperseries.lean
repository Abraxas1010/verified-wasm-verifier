import HeytingLean.Numbers.Surreal.Hyperseries

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Numbers.Ordinal
open HeytingLean.Numbers.Surreal
open HeytingLean.Numbers.Surreal.Hyperseries

private def sNat : Series := monomial 3 (OrdinalCNF.ofNat 2)
private def sOmega : Series := monomial (-1) (OrdinalCNF.omega + OrdinalCNF.ofNat 1)

example : (add sNat sOmega).length = 2 := by
  native_decide

example :
    mul sNat sOmega =
      monomial (-3) (OrdinalCNF.ofNat 2 + (OrdinalCNF.omega + OrdinalCNF.ofNat 1)) := by
  simp [sNat, sOmega]

example : order sNat ≤ order (add sNat sOmega) := by
  native_decide

example : order sOmega ≤ order (add sNat sOmega) := by
  native_decide

example :
    truncate (OrdinalCNF.omega + OrdinalCNF.ofNat 1)
      (truncate (OrdinalCNF.omega + OrdinalCNF.ofNat 1) (add sNat sOmega)) =
    truncate (OrdinalCNF.omega + OrdinalCNF.ofNat 1) (add sNat sOmega) := by
  simp

example : normalize (normalize (sNat ++ [{ coeff := 0, exp := OrdinalCNF.ofNat 9 }])) =
    normalize (sNat ++ [{ coeff := 0, exp := OrdinalCNF.ofNat 9 }]) := by
  simp

private def idx : OmnificIndex :=
  { integerPart := 7
    transfinitePart := OrdinalCNF.omega + OrdinalCNF.ofNat 3 }

example : indexSeries idx = monomial 7 (OrdinalCNF.omega + OrdinalCNF.ofNat 3) := by
  rfl

example :
    order (fromBirth TransfinitePreGame.PreGame.omega) = OrdinalCNF.omega := by
  native_decide

example :
    order (fromBirth (TransfinitePreGame.PreGame.omegaPlusNat 1)) =
      OrdinalCNF.omega + OrdinalCNF.ofNat 1 := by
  native_decide

private def ts0 : TransseriesState :=
  { principal := sNat
    correction := sOmega }

example :
    (transseriesStep ts0).principal = add sNat sOmega := by
  rfl

end Numbers
end Tests
end HeytingLean
