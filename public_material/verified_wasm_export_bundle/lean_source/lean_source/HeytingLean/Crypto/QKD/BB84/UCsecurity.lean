import HeytingLean.Crypto.Composable
import HeytingLean.Crypto.QKD.BB84.Security

/-!
# BB84 UC-style security (interface-first, reduction-based)

We avoid a full UC framework proof. Instead we provide a reduction principle:
if any successful distinguishing attack against BB84 (real vs ideal) would imply the CT-forbidden
subtask `copyAll` is possible, then BB84 is UC-secure.
-/

namespace HeytingLean.Crypto.QKD.BB84

open HeytingLean.Crypto.Composable
open HeytingLean.Crypto.Composable.Instances

/-- A BB84 UC model that reduces any real/ideal distinguishing to CT-possibility of `copyAll`. -/
structure BB84UCReduction (n : Nat) where
  π : Protocol (IdealKeyExchange n)
  sim : Simulator (IdealKeyExchange n) π
  Indistinguishable :
    (Unit → (Fin n → Bool) × π.Message) → (Unit → (Fin n → Bool) × π.Message) → Prop
  /-- Reduction: if real and ideal are distinguishable, then `copyAll` is possible. -/
  reduction :
    ¬ Indistinguishable (realExecution π) (idealExecution π sim) →
      bb84TaskCT.possible copyAll

/-- UC security for BB84, assuming a reduction to the no-cloning subtask `copyAll`. -/
def bb84_uc_secure {n : Nat} (R : BB84UCReduction n) :
    UCSecure (IdealKeyExchange n) R.π := by
  refine ⟨R.sim, R.Indistinguishable, ?_⟩
  by_contra h
  exact copyAll_impossible (R.reduction h)

end HeytingLean.Crypto.QKD.BB84

