import HeytingLean.Embeddings.PDCExtensions

/-!
# Tests.Embeddings.PDCExtensionsSanity

Compile-time sanity checks for PDC hierarchy levels and Families F-J.
-/

namespace HeytingLean.Tests.Embeddings.PDCExtensionsSanity

open HeytingLean
open HeytingLean.Embeddings
open HeytingLean.Embeddings.PDCExtensions

#check PDCWithTransport
#check PDCWithDescent
#check PDCWithTransport.forward
#check PDCWithTransport.ForwardCocycle
#check PDCWithDescent.toPlato_const

example : PDCWithDescent MixedHodgePerspective (fun _ => Int) := by infer_instance
example : PDCWithDescent PerverseStratum (fun _ => Int) := by infer_instance
example : PDCWithDescent ChromaticHeight (fun _ => Int) := by infer_instance

example : PDCWithDescent MotivicPerspective (fun _ => Int) := by infer_instance
example : PDCWithDescent PrismaticPerspective (fun _ => Int) := by infer_instance
example : PDCWithDescent ArakelovPlace (fun _ => Int) := by infer_instance

example : PDCWithDescent CondensedTestObj (fun _ => Int) := by infer_instance
example : PDCWithDescent CondensedTestObj (fun _ => LiquidValue) := by infer_instance

example : PDCWithDescent CodimLevel (fun _ => Int) := by infer_instance
example : PDCWithDescent SpacetimeOpen (fun _ => Int) := by infer_instance
example : PDCWithDescent FloerFlavor (fun _ => Int) := by infer_instance

example : PDCWithDescent SimplicialDegree (fun _ => Int) := by infer_instance

example (x : Int) :
    PerspectivalDescentCarrier.truncate
      (τ := PerverseStratum) (Carrier := fun _ => Int)
      .closedStratum 0 x = 0 :=
  perverse_closed_truncates_to_zero_at_level0 x

example (x : Int) :
    PerspectivalDescentCarrier.truncate
      (τ := MotivicPerspective) (Carrier := fun _ => Int)
      .betti 0 x = 0 :=
  motivic_truncate_at_zero .betti x

example (x : Int) :
    PerspectivalDescentCarrier.truncate
      (τ := CondensedTestObj) (Carrier := fun _ => Int)
      .cantor4 0 x = 0 :=
  condensed_truncate_zero .cantor4 x

example (x : LiquidValue) :
    (PerspectivalDescentCarrier.truncate
      (τ := CondensedTestObj) (Carrier := fun _ => LiquidValue)
      .profinite8 2 x).norm ≤ 2 :=
  liquid_truncate_norm_le .profinite8 2 x

example :
    PDCWithTransport.ForwardCocycle
      (τ := FloerFlavor) (Carrier := fun _ => Int) :=
  floer_forward_cocycle

example :
    PDCWithTransport.ForwardCocycle
      (τ := SimplicialDegree) (Carrier := fun _ => Int) :=
  derived_forward_cocycle

end HeytingLean.Tests.Embeddings.PDCExtensionsSanity
