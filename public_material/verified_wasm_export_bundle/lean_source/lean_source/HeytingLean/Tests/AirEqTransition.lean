import HeytingLean.Crypto.ZK.AirIR
import HeytingLean.Crypto.ZK.R1CS

namespace HeytingLean
namespace Crypto
namespace Tests

open ZK
open ZK.AIR

/-- AIR equality-transitions imply R1CS satisfaction for const-one constraints. -/
theorem air_eq_transitions_imply_r1cs_example :
    let c : ZK.Constraint :=
      { A := ZK.LinComb.single 2 1
      , B := ZK.LinComb.ofConst 1
      , C := ZK.LinComb.single 2 1 }
    let enc : EqTransition := { eqs := [(c.A, c.C)] }
    let a : ZK.Var → ℚ := fun _ => 0
    ZK.System.satisfied a { constraints := [c] } := by
  classical
  intros c enc a
  have hEnc : ∀ c' ∈ [c], isConstOne c' ∧ ∃ eqp ∈ enc.eqs, eqp.1 = c'.A ∧ eqp.2 = c'.C := by
    intro c' hc'
    have hc'Eq : c' = c := by simpa using List.mem_singleton.mp hc'
    subst hc'
    refine And.intro ?hOne ?hPair
    · simp [isConstOne]
    · refine ⟨(c.A, c.C), by simp, rfl, rfl⟩
  have hSat : EqTransition.satisfied a enc := by
    intro eqp hIn; rcases hIn with _ | hNil
    · simp
    · cases hNil
  exact AIR.eqs_imply_r1cs_constOne (t := enc) (a := a) (cs := [c]) hEnc hSat

end Tests
end Crypto
end HeytingLean
