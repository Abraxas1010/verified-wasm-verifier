import HeytingLean.Matula.Algebra.HeytingCore

namespace HeytingLean
namespace Matula
namespace Tests

open Algebra
open Algebra.PosNat

def p1 : PosNat := ⟨1, by decide⟩
def p2 : PosNat := ⟨2, by decide⟩
def p6 : PosNat := ⟨6, by decide⟩

example : p1 * p2 = p2 := by
  apply Subtype.ext
  simp [p1, p2]

example : (PosNat.fromTree .leaf).1 = 1 := by
  native_decide

example : (PosNat.fromTree (.node [.leaf])).1 = 2 := by
  native_decide

example : (PosNat.combineEncoded .leaf (.node [.leaf])).1 = 2 := by
  native_decide

example : (PosNat.combineEncoded (.node [.leaf]) (.node [.node [.leaf]])).1 = 6 := by
  native_decide

example : p2 ⪯ p6 := by
  change (2 : Nat) ∣ 6
  decide

example : PosNat.meet p2 p6 ⪯ p2 := by
  exact PosNat.meet_le_left _ _

example : p2 ⪯ PosNat.join p2 p6 := by
  exact PosNat.le_join_left _ _

example :
    Algebra.HeytingCore.R.eulerBoundary = Algebra.HeytingCore.R.process := by
  simp

example :
    Algebra.HeytingCore.decode
      (Algebra.HeytingCore.encode Algebra.HeytingCore.R.process) =
    Algebra.HeytingCore.R.process := by
  simp

example :
    (((Algebra.HeytingCore.R.process ⇨ Algebra.HeytingCore.R.counterProcess :
      Algebra.HeytingCore.Omega) : Algebra.HeytingCore.Carrier))
      =
    (((Algebra.HeytingCore.R.process : Algebra.HeytingCore.Omega) :
      Algebra.HeytingCore.Carrier) ⇨
      ((Algebra.HeytingCore.R.counterProcess : Algebra.HeytingCore.Omega) :
        Algebra.HeytingCore.Carrier)) := by
  rfl

end Tests
end Matula
end HeytingLean
