import HeytingLean.OTM.DynamicsComputation.StablePropositions
import HeytingLean.LoF.Bauer.SyntheticComputability

namespace HeytingLean
namespace OTM
namespace DynamicsComputation

universe u v w

/--
Interface layer for effective-topos/synthetic-computability style bridges.
All commitments are explicit fields; no global axioms are introduced.
-/
structure RealizabilityBridge (Ω : Type u) [Order.Frame Ω] where
  Carrier : Type v
  Program : Type w
  realizes : Program → Carrier → Ω
  J : Nucleus Ω
  closed_realizes : ∀ p x, J (realizes p x) = realizes p x

namespace RealizabilityBridge

variable {Ω : Type u} [Order.Frame Ω] (B : RealizabilityBridge Ω)

theorem realizes_mem_closed (p : B.Program) (x : B.Carrier) :
    B.realizes p x ∈ B.J.toSublocale := by
  exact ⟨B.realizes p x, B.closed_realizes p x⟩

/--
Bridge transfer lemma: realizability predicates are stable/closed in the bridge nucleus.
-/
theorem realizability_bridge_transfers_universality (p : B.Program) (x : B.Carrier) :
    B.J (B.realizes p x) = B.realizes p x :=
  B.closed_realizes p x

end RealizabilityBridge

/--
Adapter from a Bauer synthetic computability world to a realizability-style bridge.
This is intentionally lightweight and interface-only.
-/
def ofSyntheticWorld
    {Ω : Type u} [Order.Frame Ω]
    (W : LoF.Bauer.SyntheticComputability.World (Ω := Ω))
    (Carrier : Type v) (Program : Type w)
    (realizes : Program → Carrier → Ω)
    (hclosed : ∀ p x, W.J (realizes p x) = realizes p x) :
    RealizabilityBridge Ω where
  Carrier := Carrier
  Program := Program
  realizes := realizes
  J := W.J
  closed_realizes := hclosed

end DynamicsComputation
end OTM
end HeytingLean
