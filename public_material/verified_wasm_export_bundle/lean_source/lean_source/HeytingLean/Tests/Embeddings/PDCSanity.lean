import HeytingLean.Embeddings.PerspectivalDescentCarrier
import HeytingLean.Embeddings.AdelicInstances
import HeytingLean.Embeddings.GenericCrossLensTransport
import HeytingLean.ATP.DifferentiableATP.SheafTransport
import HeytingLean.PerspectivalPlenum.PDCDescentBridge

/-!
# Tests.Embeddings.PDCSanity

Compile-time sanity checks for the Perspectival Descent Carrier (PDC) integration.
-/

namespace HeytingLean.Tests.Embeddings.PDCSanity

open HeytingLean
open HeytingLean.Embeddings
open HeytingLean.Embeddings.GenericCrossLensTransport
open HeytingLean.ATP.DifferentiableATP

#check PerspectivalDescentCarrier
#check PerspectivalDescentCarrier.Approx
#check coreLensData
#check coreLensDataOnLensID
#check restrictCoreAdelicToLensID
#check sheafTransportPDC

example : PerspectivalDescentCarrier CoreLensTag coreLensData.Completion := by
  infer_instance

example : PerspectivalDescentCarrier LensID coreLensDataOnLensID.Completion := by
  infer_instance

example : PerspectivalDescentCarrier LensID SheafCarrier := by
  infer_instance

/-- Truncation from the sheaf transport PDC is the local projection round-trip. -/
example (x : HeytingLean.LoF.Combinators.Differential.Compute.FSum) :
    (PerspectivalDescentCarrier.truncate (τ := LensID) (Carrier := SheafCarrier)
      LensID.omega 5 x) = lensProjection LensID.omega x := by
  rfl

/-- Generic transport cocycle theorem remains available through the PDC bridge layer. -/
example {τ : Type} {Carrier : τ → Type} {Plato : Type}
    (T : GenericTransport τ Carrier Plato) :
    GenericTransport.ForwardCocycle T :=
  GenericTransport.forward_comp_is_cocycle T

#check PerspectivalPlenum.transport_gluing_to_pairCover_amalgamates

end HeytingLean.Tests.Embeddings.PDCSanity
