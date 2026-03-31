import HeytingLean.Crypto.ZK.AirIR
import HeytingLean.Crypto.ZK.R1CS

namespace HeytingLean
namespace Crypto
namespace Tests

open ZK
open ZK.AIR

/-- A composite transition set with one const-one equality and one multiplicative constraint
    implies R1CS satisfaction of both constraints. -/
theorem air_union_transitions_imply_r1cs_example :
    let cEq : ZK.Constraint :=
      { A := ZK.LinComb.single 3 1
      , B := ZK.LinComb.ofConst 1
      , C := ZK.LinComb.single 3 1 }
    let cMul : ZK.Constraint :=
      { A := ZK.LinComb.single 0 1
      , B := ZK.LinComb.single 1 1
      , C := ZK.LinComb.single 2 1 }
    let t : TransitionSet := { eqs := [(cEq.A, cEq.C)], muls := [(cMul.A, cMul.B, cMul.C)] }
    let a : ZK.Var → ℚ := fun _ => 0
    ZK.System.satisfied a { constraints := [cEq, cMul] } := by
  classical
  intros cEq cMul t a
  have hEnc : ∀ c ∈ [cEq, cMul],
      (isConstOne c ∧ ∃ eqp ∈ t.eqs, eqp.1 = c.A ∧ eqp.2 = c.C)
      ∨ (∃ tr ∈ t.muls, tr.1 = c.A ∧ tr.2.1 = c.B ∧ tr.2.2 = c.C) := by
    intro c hc
    have hcCases := List.mem_cons.mp hc
    cases hcCases with
    | inl h =>
        subst h
        left
        exact ⟨by simp [isConstOne], ⟨(cEq.A, cEq.C), by simp, rfl, rfl⟩⟩
    | inr hTail =>
        have hc' : c = cMul := by simpa using List.mem_singleton.mp hTail
        subst hc'
        right
        exact ⟨(cMul.A, cMul.B, cMul.C), by simp, rfl, rfl, rfl⟩
  have hSat : TransitionSet.satisfied a t := by
    constructor
    · intro eqp hIn; rcases hIn with _ | hNil; simp_all
    · intro tr  hIn; rcases hIn with _ | hNil; simp_all
  exact AIR.transitions_union_imply_r1cs (t := t) (a := a) (cs := [cEq, cMul]) hEnc hSat

end Tests
end Crypto
end HeytingLean

