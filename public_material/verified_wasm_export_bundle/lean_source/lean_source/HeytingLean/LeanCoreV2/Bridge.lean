import HeytingLean.LeanCoreV2.Syntax
import HeytingLean.LeanCoreV2.Semantics

namespace HeytingLean
namespace LeanCoreV2
namespace Bridge

open HeytingLean.Core

/-- Lean (meta-level) add-one function. -/
def leanAdd1 (n : Nat) : Nat := n + 1

/-- LeanCore v2 term encoding `leanAdd1`. -/
def termAdd1 : Term [] (Ty.arrow Ty.nat Ty.nat) :=
  Term.lam (Term.app (Term.app Term.primAddNat (Term.var Var.vz)) (Term.constNat 1))

/-- Proof that the LeanCore term computes the same function as `leanAdd1`. -/
theorem add1_bridge_correct (n : Nat) :
    evalClosed (Term.app termAdd1 (Term.constNat n)) = leanAdd1 n := by
  unfold termAdd1 leanAdd1 evalClosed
  simp [eval, extendEnv]

/-- Lean (meta-level) doubling function. -/
def leanDouble (n : Nat) : Nat := n + n

/-- LeanCore v2 term encoding `leanDouble`. -/
def termDouble : Term [] (Ty.arrow Ty.nat Ty.nat) :=
  Term.lam
    (Term.app
      (Term.app Term.primAddNat (Term.var Var.vz))
      (Term.var Var.vz))

/-- Proof that the LeanCore term computes the same function as `leanDouble`. -/
theorem double_bridge_correct (n : Nat) :
    evalClosed (Term.app termDouble (Term.constNat n)) = leanDouble n := by
  unfold termDouble leanDouble evalClosed
  simp [eval, extendEnv]

end Bridge
end LeanCoreV2
end HeytingLean
