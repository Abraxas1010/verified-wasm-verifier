import HeytingLean.Crypto.ZK.AirIR
import HeytingLean.Crypto.ZK.R1CS

namespace HeytingLean
namespace Crypto
namespace Tests

open ZK
open ZK.AIR

/-- A simple multiplicative transition implies the corresponding R1CS gate. -/
theorem air_mul_transitions_imply_r1cs_example :
    let c : ZK.Constraint :=
      { A := ZK.LinComb.single 0 1
      , B := ZK.LinComb.single 1 1
      , C := ZK.LinComb.single 2 1 }
    let t : MulTransition := { triples := [(c.A, c.B, c.C)] }
    let a : ZK.Var → ℚ := fun _ => 0
    ZK.System.satisfied a { constraints := [c] } := by
  classical
  intros c t a
  have hEnc : ∀ c' ∈ [c], ∃ tr ∈ t.triples, tr.1 = c'.A ∧ tr.2.1 = c'.B ∧ tr.2.2 = c'.C := by
    intro c' hc'
    have hc'Eq : c' = c := by simpa using List.mem_singleton.mp hc'
    subst hc'
    exact ⟨(c.A, c.B, c.C), by simp, rfl, rfl, rfl⟩
  have hSat : MulTransition.satisfied a t := by
    intro tr htr; rcases htr with _ | hnil
    · simp
    · cases hnil
  exact AIR.muls_imply_r1cs (t := t) (a := a) (cs := [c]) hEnc hSat

end Tests
end Crypto
end HeytingLean

