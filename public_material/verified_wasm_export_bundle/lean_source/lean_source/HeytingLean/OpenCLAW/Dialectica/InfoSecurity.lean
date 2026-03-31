import HeytingLean.OpenCLAW.Dialectica.ProtocolLayer
import HeytingLean.OpenCLAW.Info.Defs
import HeytingLean.Silicon.Leakage
import HeytingLean.Silicon.Predictability
import HeytingLean.Silicon.Cost

namespace HeytingLean.OpenCLAW.Dialectica

noncomputable section

/-!
# Dialectica Wrappers for Information-Security Claims

All layers are instantiated at `ProtocolLayer.{0}` (`Type 0`) for compatibility
with the PoW/RS layers which use `Nat`/`Rat`. The Silicon source theorems are
universe-polymorphic but the composite protocol requires a fixed universe.

- source_paper_url: https://arxiv.org/abs/2601.12032
- attribution_status: A-conditional
- claim_status: B-pass (dialectica instantiation of existing proofs)
- proof_status: proved
-/

/-- STS-001 as a dialectica protocol layer. -/
def zeroLeakageLayer (S O : Type) [Fintype S] [Fintype O] : ProtocolLayer.{0} where
  Witness := { P : HeytingLean.Silicon.Run S O //
    HeytingLean.Silicon.Independent (S := S) (O := O) P }
  Challenge := Unit
  secure := fun ⟨P, _⟩ _ => HeytingLean.Silicon.Leakage (S := S) (O := O) P = 0

/-- STS-001 witness theorem delegated to `Silicon.leakage_eq_zero_of_independent`. -/
theorem zeroLeakageLayer_secure (S O : Type) [Fintype S] [Fintype O]
    (w : (zeroLeakageLayer S O).Witness)
    (c : (zeroLeakageLayer S O).Challenge) :
    (zeroLeakageLayer S O).secure w c := by
  rcases w with ⟨P, hind⟩
  simpa [zeroLeakageLayer] using
    (HeytingLean.Silicon.leakage_eq_zero_of_independent (S := S) (O := O) P hind)

/-- STS-002 as a dialectica protocol layer. -/
def predictabilityLayer (X Y : Type)
    [Fintype X] [Fintype Y] [DecidableEq Y] [Nonempty Y] : ProtocolLayer.{0} where
  Witness := { P : HeytingLean.Silicon.Run X Y //
    HeytingLean.Silicon.Independent (S := X) (O := Y) P }
  Challenge := X -> Y
  secure := fun ⟨P, _⟩ g =>
    HeytingLean.Silicon.Predictability.accuracy (X := X) (Y := Y) P g <=
      HeytingLean.Silicon.Predictability.baseline (X := X) (Y := Y) P

/-- STS-002 witness theorem delegated to `accuracy_le_baseline_of_independent`. -/
theorem predictabilityLayer_secure (X Y : Type)
    [Fintype X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (w : (predictabilityLayer X Y).Witness)
    (c : (predictabilityLayer X Y).Challenge) :
    (predictabilityLayer X Y).secure w c := by
  rcases w with ⟨P, hind⟩
  simpa [predictabilityLayer] using
    (HeytingLean.Silicon.Predictability.accuracy_le_baseline_of_independent
      (X := X) (Y := Y) P hind c)

/-- STS-003 as a dialectica protocol layer.
This layer is defined and proved correct independently. It is not wired into the
default composite (`p2pclawProtocol`) because STS-003 covers a distinct threat
model (early-abort energy savings) rather than the information-leakage model used
by STS-001/002. A composite variant using this layer can be constructed via
`energySavingsLayer.tensor (powTimeLayer.tensor rsIntegrityLayer)`. -/
def energySavingsLayer (Obs Y : Type) [Fintype Obs] [Fintype Y]
    (n k : Nat) (hn : 0 < n) (hk : k <= n) : ProtocolLayer.{0} where
  Witness := { Pc :
      (HeytingLean.Probability.InfoTheory.FinDist
        (HeytingLean.Silicon.EarlyAbort.Trace (Obs := Obs) n × Y)) × ((Fin k -> Obs) -> Bool) //
      HeytingLean.Silicon.Cost.EarlyAbort.continueProb (Obs := Obs) (Y := Y) hk Pc.1 Pc.2 = 0 }
  Challenge := Unit
  secure := fun ⟨⟨P, clf⟩, _⟩ _ =>
    HeytingLean.Silicon.Cost.EarlyAbort.energySavings (Obs := Obs) (Y := Y) (hn := hn) hk P clf =
      1 - (k : Real) / (n : Real)

/-- STS-003 witness theorem delegated to `energySavings_eq_of_continueProb_eq_zero`. -/
theorem energySavingsLayer_secure (Obs Y : Type) [Fintype Obs] [Fintype Y]
    (n k : Nat) (hn : 0 < n) (hk : k <= n)
    (w : (energySavingsLayer Obs Y n k hn hk).Witness)
    (c : (energySavingsLayer Obs Y n k hn hk).Challenge) :
    (energySavingsLayer Obs Y n k hn hk).secure w c := by
  rcases w with ⟨⟨P, clf⟩, h0⟩
  simpa [energySavingsLayer] using
    (HeytingLean.Silicon.Cost.EarlyAbort.energySavings_eq_of_continueProb_eq_zero
      (Obs := Obs) (Y := Y) (hn := hn) hk P clf h0)

end

end HeytingLean.OpenCLAW.Dialectica
