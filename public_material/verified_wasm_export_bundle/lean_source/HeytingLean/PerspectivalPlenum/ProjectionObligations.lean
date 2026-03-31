import HeytingLean.PerspectivalPlenum.ATPTargets
import HeytingLean.PerspectivalPlenum.VirtualObstructionBridge
import HeytingLean.PerspectivalPlenum.VirtualKnotTransportBridge
import HeytingLean.Embeddings.CrossLensTransportChain
import HeytingLean.Quantum.StabilizerNucleus

namespace HeytingLean
namespace PerspectivalPlenum
namespace ProjectionObligations

/--
Machine-checkable obligation keys used by cross-lens ATP routing.

Each key has a corresponding theorem hook that can be used to discharge a
projection/restriction obligation in the target lens.
-/
inductive ObligationKey where
  | triangleCechH1
  | triangleLocalGlobal
  | squareCircleLensRelative
  | euclideanSingletonGlues
  | virtualLifeObstruction
  | virtualKnotTransportR2
  | virtualKnotTransportR3Pair
  | virtualKnotTransportR3Bracket
  | virtualKnotTransportR3BracketTL3
  | virtualKnotTransportR3BracketBridge
  | crossLensRoundtrip
  deriving DecidableEq, Repr

def keyName : ObligationKey → String
  | .triangleCechH1 => "triangle_cech_h1"
  | .triangleLocalGlobal => "triangle_local_global"
  | .squareCircleLensRelative => "square_circle_lens_relative"
  | .euclideanSingletonGlues => "euclidean_singleton_glues"
  | .virtualLifeObstruction => "virtual_life_obstruction"
  | .virtualKnotTransportR2 => "virtual_knot_transport_r2"
  | .virtualKnotTransportR3Pair => "virtual_knot_transport_r3_pair"
  | .virtualKnotTransportR3Bracket => "virtual_knot_transport_r3_bracket"
  | .virtualKnotTransportR3BracketTL3 => "virtual_knot_transport_r3_bracket_tl3"
  | .virtualKnotTransportR3BracketBridge => "virtual_knot_transport_r3_bracket_bridge"
  | .crossLensRoundtrip => "cross_lens_roundtrip"

/-- Projection hook: contextuality triangle `H1` witness. -/
theorem triangle_cech_h1_hook :
    ContextualityEngine.HasCechH1
      Quantum.Contextuality.Triangle.X
      Quantum.Contextuality.Triangle.cover
      Quantum.Contextuality.Triangle.model
      (fun {C} hC => Quantum.Contextuality.Triangle.coverSubX (C := C) hC) :=
  ATP.target_triangle_cech_h1

/-- Projection hook: local admissibility with global obstruction. -/
theorem triangle_local_global_hook :
    ContextualityEngine.LocallyAdmissibleOnCover Quantum.Contextuality.Triangle.model ∧
      ContextualityEngine.GloballyObstructed
        Quantum.Contextuality.Triangle.X
        Quantum.Contextuality.Triangle.cover
        Quantum.Contextuality.Triangle.model
        (fun {C} hC => Quantum.Contextuality.Triangle.coverSubX (C := C) hC) :=
  ATP.target_triangle_local_global

/-- Projection hook: square-circle lens-relative decomposition. -/
theorem square_circle_lens_relative_hook :
    Lens.CollapseToBottom Lens.Examples.euclideanLens Lens.Examples.ShapeObject.squareCircle ∧
      Lens.LocallySatisfiable Lens.Examples.higherDimLens Lens.Examples.ShapeObject.squareCircle :=
  ATP.target_squareCircle_lens_relative

/-- Projection hook: singleton Euclidean matching-family gluing. -/
theorem euclidean_singleton_glues_hook :
    LensSheaf.Amalgamates
      LensSheaf.Examples.ShapeWitnessPresheaf
      LensSheaf.Examples.euclideanObj
      (LensSheaf.singletonCover LensSheaf.Examples.euclideanObj)
      LensSheaf.Examples.euclideanSingletonFamily :=
  ATP.target_euclideanSingleton_glues

/-- Projection hook: Life-class virtual obstruction classification. -/
theorem virtual_life_obstruction_hook :
    ∀ {G : Type} (P : VirtualObstructionBridge.VirtualProfile G),
      VirtualObstructionBridge.virtualObstructionClass P P.life =
      ContextualityEngine.CechObstructionClass.h1_overlap_incompatibility :=
  ATP.target_virtual_life_obstruction_class

/-- Projection hook: transported R2 move lands in no-obstruction class. -/
theorem virtual_knot_transport_r2_hook
    {g g' : HeytingLean.Topology.Knot.PDGraph}
    {x u : Nat}
    (hMove : HeytingLean.Topology.Knot.Reidemeister.r2Add g x u = .ok g') :
    VirtualKnotTransportBridge.virtualKnotObstructionClass g' =
      ContextualityEngine.CechObstructionClass.none :=
  VirtualKnotTransportBridge.virtual_transport_obstruction_hook_r2 hMove

/-- Projection hook: transported R3 pair lands in no-obstruction on both braid endpoints. -/
theorem virtual_knot_transport_r3_pair_hook
    {g : HeytingLean.Topology.Knot.PDGraph}
    {x u w : Nat}
    (pair : HeytingLean.Topology.Knot.R3TransportPair g x u w) :
    VirtualKnotTransportBridge.virtualKnotObstructionClass pair.left =
      ContextualityEngine.CechObstructionClass.none ∧
      VirtualKnotTransportBridge.virtualKnotObstructionClass pair.right =
      ContextualityEngine.CechObstructionClass.none :=
  ATP.target_virtual_knot_r3_pair_class pair

/--
Projection hook: conditional R3 braid-endpoint bracket invariance.
-/
theorem virtual_knot_transport_r3_bracket_hook
    {g gL gR : HeytingLean.Topology.Knot.PDGraph}
    {x u w : Nat}
    (hLeft : HeytingLean.Topology.Knot.Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : HeytingLean.Topology.Knot.Reidemeister.r3BraidRight g x u w = .ok gR)
    (hStepEq : HeytingLean.Topology.Knot.Kauffman.r3SkeinStep gL =
      HeytingLean.Topology.Knot.Kauffman.r3SkeinStep gR) :
    HeytingLean.Topology.Knot.bracketSignature gL =
    HeytingLean.Topology.Knot.bracketSignature gR :=
  ATP.target_virtual_knot_r3_bracket_signature_of_skeinStep_eq hLeft hRight hStepEq

/--
Projection hook: conditional R3 braid-endpoint bracket invariance via endpoint
TL3 bridge correspondences.
-/
theorem virtual_knot_transport_r3_bracket_tl3_hook
    {g gL gR : HeytingLean.Topology.Knot.PDGraph}
    {x u w fuel : Nat}
    (hLeft : HeytingLean.Topology.Knot.Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : HeytingLean.Topology.Knot.Reidemeister.r3BraidRight g x u w = .ok gR)
    (hLeftTL :
      HeytingLean.Topology.Knot.Kauffman.r3SkeinStep gL =
        HeytingLean.Topology.Knot.Kauffman.TL3Context.evalTL3Expr fuel g x u w
          HeytingLean.Topology.Knot.Kauffman.R3.tlWordLeft)
    (hRightTL :
      HeytingLean.Topology.Knot.Kauffman.r3SkeinStep gR =
        HeytingLean.Topology.Knot.Kauffman.TL3Context.evalTL3Expr fuel g x u w
          HeytingLean.Topology.Knot.Kauffman.R3.tlWordRight) :
    HeytingLean.Topology.Knot.bracketSignature gL =
      HeytingLean.Topology.Knot.bracketSignature gR :=
  ATP.target_virtual_knot_r3_bracket_signature_of_tl3_bridge_endpoints
    hLeft hRight hLeftTL hRightTL

/--
Projection hook: conditional R3 braid-endpoint bracket invariance via the
unified bridge witness.
-/
theorem virtual_knot_transport_r3_bracket_bridge_hook
    {g gL gR : HeytingLean.Topology.Knot.PDGraph}
    {x u w : Nat}
    (hLeft : HeytingLean.Topology.Knot.Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : HeytingLean.Topology.Knot.Reidemeister.r3BraidRight g x u w = .ok gR)
    (hBridge :
      HeytingLean.Topology.Knot.Kauffman.R3SkeinBridgeWitness g gL gR x u w) :
    HeytingLean.Topology.Knot.bracketSignature gL =
      HeytingLean.Topology.Knot.bracketSignature gR :=
  ATP.target_virtual_knot_r3_bracket_signature_of_bridge_witness
    hLeft hRight hBridge

/--
Generic round-trip hook for cross-lens transports.

This provides a kernel-level theorem object for RT-1/RT-2 style obligations.
-/
theorem cross_lens_roundtrip_hook
    {Carrier : Embeddings.LensID → Type} {Plato : Type}
    (T : Embeddings.CrossLensTransport Carrier Plato)
    (src dst : Embeddings.LensID)
    (x : Carrier src) :
    T.backward src dst (T.forward src dst x) = x :=
  Embeddings.CrossLensTransport.backward_forward T src dst x

/--
Stabilizer fixed-point obligations are invariant under a certified cross-lens
round trip: transport to another lens and back does not change membership.
-/
theorem stabilizer_roundtrip_membership_hook
    {Carrier : Embeddings.LensID → Type} {Plato : Type}
    (T : Embeddings.CrossLensTransport Carrier Plato)
    (src dst : Embeddings.LensID)
    (U : Set (Carrier src))
    (x : Carrier src) :
    (T.backward src dst (T.forward src dst x) ∈ U) ↔ (x ∈ U) := by
  simp [cross_lens_roundtrip_hook (T := T) src dst x]

/--
Stabilizer nucleus fixedness is preserved by cross-lens roundtrip reindexing of
the carrier set under a certified transport.
-/
theorem stabilizer_roundtrip_fixed_preserved_hook
    {Carrier : Embeddings.LensID → Type} {Plato : Type}
    (T : Embeddings.CrossLensTransport Carrier Plato)
    (src dst : Embeddings.LensID)
    (C : HeytingLean.Quantum.StabilizerCode (Carrier src))
    (U : Set (Carrier src))
    (hfix : HeytingLean.Quantum.StabilizerNucleus.stabilizerNucleus C U = U) :
    HeytingLean.Quantum.StabilizerNucleus.stabilizerNucleus C
      {x : Carrier src | T.backward src dst (T.forward src dst x) ∈ U}
      = {x : Carrier src | T.backward src dst (T.forward src dst x) ∈ U} := by
  have hset :
      ({x : Carrier src | T.backward src dst (T.forward src dst x) ∈ U} : Set (Carrier src)) = U := by
    ext x
    simp [cross_lens_roundtrip_hook (T := T) src dst x]
  simpa [hset] using hfix

/-- Canonical theorem-name registry used by script-level obligation discharge. -/
def dischargeHintRegistry : List (ObligationKey × String) :=
  [ (.triangleCechH1, "HeytingLean.PerspectivalPlenum.ProjectionObligations.triangle_cech_h1_hook")
  , (.triangleLocalGlobal, "HeytingLean.PerspectivalPlenum.ProjectionObligations.triangle_local_global_hook")
  , (.squareCircleLensRelative, "HeytingLean.PerspectivalPlenum.ProjectionObligations.square_circle_lens_relative_hook")
  , (.euclideanSingletonGlues, "HeytingLean.PerspectivalPlenum.ProjectionObligations.euclidean_singleton_glues_hook")
  , (.virtualLifeObstruction, "HeytingLean.PerspectivalPlenum.ProjectionObligations.virtual_life_obstruction_hook")
  , (.virtualKnotTransportR2, "HeytingLean.PerspectivalPlenum.ProjectionObligations.virtual_knot_transport_r2_hook")
  , (.virtualKnotTransportR3Pair, "HeytingLean.PerspectivalPlenum.ProjectionObligations.virtual_knot_transport_r3_pair_hook")
  , (.virtualKnotTransportR3Bracket, "HeytingLean.PerspectivalPlenum.ProjectionObligations.virtual_knot_transport_r3_bracket_hook")
  , (.virtualKnotTransportR3BracketTL3, "HeytingLean.PerspectivalPlenum.ProjectionObligations.virtual_knot_transport_r3_bracket_tl3_hook")
  , (.virtualKnotTransportR3BracketBridge, "HeytingLean.PerspectivalPlenum.ProjectionObligations.virtual_knot_transport_r3_bracket_bridge_hook")
  , (.crossLensRoundtrip, "HeytingLean.PerspectivalPlenum.ProjectionObligations.cross_lens_roundtrip_hook")
  ]

end ProjectionObligations
end PerspectivalPlenum
end HeytingLean

/--
Queue anchor theorem for `ontology_stabilizer_plenum_projection_20260219`:
stabilizer fixed points are preserved by certified round-trip transports.
-/
theorem ontology_stabilizer_plenum_projection_20260219
    {Carrier : HeytingLean.Embeddings.LensID → Type} {Plato : Type}
    (T : HeytingLean.Embeddings.CrossLensTransport Carrier Plato)
    (src dst : HeytingLean.Embeddings.LensID)
    (C : HeytingLean.Quantum.StabilizerCode (Carrier src))
    (U : Set (Carrier src))
    (hfix : HeytingLean.Quantum.StabilizerNucleus.stabilizerNucleus C U = U) :
    HeytingLean.Quantum.StabilizerNucleus.stabilizerNucleus C
      {x : Carrier src | T.backward src dst (T.forward src dst x) ∈ U}
      = {x : Carrier src | T.backward src dst (T.forward src dst x) ∈ U} :=
  HeytingLean.PerspectivalPlenum.ProjectionObligations.stabilizer_roundtrip_fixed_preserved_hook
    (T := T) src dst C U hfix
