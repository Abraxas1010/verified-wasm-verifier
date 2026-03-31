import HeytingLean.Crypto.ZK.AirIR
import HeytingLean.Crypto.ZK.R1CS

namespace HeytingLean
namespace Crypto
namespace Tests

open ZK
open ZK.AIR

/-- TransitionSet.ofSystemAuto covers const-one equalities and multiplicative triples
    arising from boolean ops like OR/IMP/NOT (with helper product wires). -/
theorem air_bool_ops_auto_imply_r1cs :
    -- vars: x=0, y=0, t=0 (product), zOr=0, zImp=1-x+ t = 1, zNot=1
    let x := 0; let y := 1; let t := 2; let zOr := 3; let zImp := 4; let zNot := 5
    let a : ZK.Var → ℚ := fun _ => 0
    -- R1CS constraints: t = x*y (mul), zOr = x + y - t (eq), zImp = 1 - x + t (eq), zNot = 1 - x (eq)
    let cMul : ZK.Constraint := { A := ZK.LinComb.single x 1, B := ZK.LinComb.single y 1, C := ZK.LinComb.single t 1 }
    let lcOr : ZK.LinComb := { const := 0, terms := [(x, 1), (y, 1), (t, -1)] }
    let cOr : ZK.Constraint := { A := ZK.LinComb.single zOr 1, B := ZK.LinComb.ofConst 1, C := lcOr }
    let lcImp : ZK.LinComb := { const := 1, terms := [(x, -1), (t, 1)] }
    let cImp : ZK.Constraint := { A := ZK.LinComb.single zImp 1, B := ZK.LinComb.ofConst 1, C := lcImp }
    let lcNot : ZK.LinComb := { const := 1, terms := [(x, -1)] }
    let cNot : ZK.Constraint := { A := ZK.LinComb.single zNot 1, B := ZK.LinComb.ofConst 1, C := lcNot }
    let cs := [cMul, cOr, cImp, cNot]
    let tset := TransitionSet.ofSystemAuto cs
    TransitionSet.satisfied a tset ∧ ZK.System.satisfied a { constraints := cs } := by
  classical
  intros x y t zOr zImp zNot a cMul lcOr cOr lcImp cImp lcNot cNot cs tset
  -- Show transitions are satisfied under zero assignment
  have hSatEq : EqTransition.satisfied a ⟨tset.eqs⟩ := by
    intro eqp hIn
    rcases hIn with _ | hTail
    · simp
    · rcases hTail with _ | hTail2
      · simp
      · simp at hTail2
  have hSatMul : MulTransition.satisfied a ⟨tset.muls⟩ := by
    intro tr hIn
    rcases hIn with _ | hNil
    · simp
    · cases hNil
  have hSat : TransitionSet.satisfied a tset := And.intro hSatEq hSatMul
  -- Apply auto implication to R1CS
  have hR1 : ZK.System.satisfied a { constraints := cs } :=
    AIR.ofSystemAuto_imply_r1cs (a := a) (cs := cs) hSat
  exact And.intro hSat hR1

end Tests
end Crypto
end HeytingLean

