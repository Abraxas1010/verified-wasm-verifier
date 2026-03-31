import HeytingLean.Crypto.ZK.R1CS
import HeytingLean.Crypto.ZK.Rename

namespace HeytingLean
namespace Crypto
namespace Tests

open ZK

/-- Sanity: renaming a simple equality constraint via a swap preserves satisfaction. -/
theorem rename_swap_eq_satisfied :
    let c : Constraint := { A := LinComb.single 0 1, B := LinComb.ofConst 1, C := LinComb.single 1 1 }
    let σ : Var → Var := fun v => if v = 0 then 1 else if v = 1 then 0 else v
    let a : Var → ℚ := fun v => if v = 0 then 3 else if v = 1 then 3 else 0
    Constraint.satisfied a (Rename.constraint σ c) ↔ Constraint.satisfied (fun v => a (σ v)) c := by
  classical
  intros; simpa using (ZK.Rename.satisfied_constraint σ a c)

end Tests
end Crypto
end HeytingLean

