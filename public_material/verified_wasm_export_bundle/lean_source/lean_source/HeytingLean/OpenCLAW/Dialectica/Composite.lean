import HeytingLean.OpenCLAW.Dialectica.InfoSecurity
import HeytingLean.OpenCLAW.Dialectica.ComputeSecurity
import HeytingLean.OpenCLAW.Dialectica.DataIntegrity

namespace HeytingLean.OpenCLAW.Dialectica

/-!
# Composite P2PCLAW Protocol Security

- source_type: categorical integration (dialectica tensor product)
- attribution_status: n/a (infrastructure)
- claim_status: n/a (integration)
- proof_status: proved
-/

/-- P2PCLAW protocol object using STS-001 + PoW + RS layers. -/
def p2pclawProtocol (S O : Type) [Fintype S] [Fintype O] : ProtocolLayer.{0} :=
  (zeroLeakageLayer S O).tensor (powTimeLayer.tensor rsIntegrityLayer)

/-- Composite security theorem with explicit RS corruption-bound hypothesis.
The hypothesis `hrs` asserts that the number of corrupted symbols does not exceed
the RS code's bounded-distance decoding capacity `⌊(n-k)/2⌋`. The info-theory
and PoW components are unconditionally secure given valid witnesses. -/
theorem p2pclaw_composite_secure
    (S O : Type) [Fintype S] [Fintype O]
    (w : (p2pclawProtocol S O).Witness)
    (c : (p2pclawProtocol S O).Challenge)
    (hrs : rsIntegrityLayer.secure w.2.2 c.2.2) :
    (p2pclawProtocol S O).secure w c := by
  refine And.intro ?_ ?_
  · exact zeroLeakageLayer_secure S O w.1 c.1
  · refine And.intro ?_ ?_
    · exact powTimeLayer_secure w.2.1 c.2.1
    · exact hrs

/-- Variant protocol object using STS-002 + PoW + RS layers. -/
def p2pclawProtocolPredictability (X Y : Type)
    [Fintype X] [Fintype Y] [DecidableEq Y] [Nonempty Y] : ProtocolLayer.{0} :=
  (predictabilityLayer X Y).tensor (powTimeLayer.tensor rsIntegrityLayer)

/-- Composite security theorem for the predictability variant with explicit RS bound.
Same RS corruption-bound hypothesis as `p2pclaw_composite_secure`. -/
theorem p2pclaw_composite_secure_predictability
    (X Y : Type) [Fintype X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (w : (p2pclawProtocolPredictability X Y).Witness)
    (c : (p2pclawProtocolPredictability X Y).Challenge)
    (hrs : rsIntegrityLayer.secure w.2.2 c.2.2) :
    (p2pclawProtocolPredictability X Y).secure w c := by
  refine And.intro ?_ ?_
  · exact predictabilityLayer_secure X Y w.1 c.1
  · refine And.intro ?_ ?_
    · exact powTimeLayer_secure w.2.1 c.2.1
    · exact hrs

end HeytingLean.OpenCLAW.Dialectica
