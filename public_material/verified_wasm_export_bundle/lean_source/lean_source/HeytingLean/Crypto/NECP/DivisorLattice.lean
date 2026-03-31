import Mathlib.Data.Fintype.Order
import HeytingLean.Crypto.NECP.PrincipalNucleus

namespace HeytingLean
namespace Crypto
namespace NECP

/-- Prime-power divisors are represented by their exponents `0, …, k`. -/
abbrev PrimePowerDivisor (k : Nat) := Fin (k + 1)

/-- Concrete divisor carrier for the prime-power lane. The prime parameter is retained so the
surface still names the divisor family it is modelling. -/
abbrev DivisorOf (_p k : Nat) := PrimePowerDivisor k

/-- Minimal protocol-side state whose secret is a divisor in the prime-power chain. -/
structure LadminiState (p k : Nat) where
  secret : DivisorOf p k

namespace PrimePowerDivisor

variable {k : Nat}

/-- Numeric divisor represented by exponent `e`, namely `p^e`. -/
def value (p : Nat) (e : PrimePowerDivisor k) : Nat :=
  p ^ (e : Nat)

/-- Closure on the divisor chain by adjoining a threshold exponent. -/
def divisorClosure (threshold : PrimePowerDivisor k) (e : PrimePowerDivisor k) :
    PrimePowerDivisor k :=
  max e threshold

theorem divisorClosure_extensive (threshold e : PrimePowerDivisor k) :
    e ≤ divisorClosure threshold e := by
  exact le_max_left _ _

theorem divisorClosure_idempotent (threshold e : PrimePowerDivisor k) :
    divisorClosure threshold (divisorClosure threshold e) = divisorClosure threshold e := by
  simp [divisorClosure]

theorem divisorClosure_meet_preserves (threshold a b : PrimePowerDivisor k) :
    divisorClosure threshold (a ⊓ b) =
      divisorClosure threshold a ⊓ divisorClosure threshold b := by
  simpa [divisorClosure, max_comm] using sup_inf_left threshold a b

noncomputable def divisorNucleus (threshold : PrimePowerDivisor k) :
    Nucleus (PrimePowerDivisor k) :=
  principalNucleus threshold

@[simp] theorem divisorNucleus_apply (threshold e : PrimePowerDivisor k) :
    divisorNucleus threshold e = divisorClosure threshold e :=
  by simp [divisorNucleus, divisorClosure, principalNucleus, max_comm]

end PrimePowerDivisor

section

variable {k : Nat}

/-- NECP-facing name for the divisor closure nucleus used in the embedding lane. -/
noncomputable def smoothPartNucleus (threshold : PrimePowerDivisor k) :
    Nucleus (PrimePowerDivisor k) :=
  PrimePowerDivisor.divisorNucleus threshold

@[simp] theorem smoothPartNucleus_apply (threshold e : PrimePowerDivisor k) :
    smoothPartNucleus threshold e = PrimePowerDivisor.divisorClosure threshold e := by
  simp [smoothPartNucleus]

end

end NECP
end Crypto
end HeytingLean
