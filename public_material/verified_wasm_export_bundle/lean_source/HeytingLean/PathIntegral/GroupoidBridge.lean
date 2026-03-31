import HeytingLean.PathIntegral.Topology

/-!
# PathIntegral.GroupoidBridge

Quotient-level bridge from the discrete `ProofGroupoid` to a HoTT-flavoured
path-space presentation and the existing Cech obstruction witnesses.

The key restriction is that `ProofPath.homotopic` preserves only
`start`, `finish`, and `transportSupport`. The legacy
`PathIntegral.obstructionClass` depends on `usesMultipleLenses`, which is not a
homotopy invariant. This module therefore defines a transport-support based
classifier that does factor through the quotient, packages quotient elimination
in a J-style form, and connects the resulting obstruction classes to the
triangle `H¹` witness already formalized in
`PerspectivalPlenum.CechCohomology`.
-/

namespace HeytingLean
namespace PathIntegral

open HeytingLean.PerspectivalPlenum

/-- The fiber of proof paths belonging to a fixed quotient class. -/
def pathFiber (cls : ProofGroupoid) : Type :=
  { p : ProofPath // Quotient.mk ProofPath.homotopicSetoid p = cls }

/-- Every groupoid class has at least one representative. -/
theorem pathFiber_nonempty (cls : ProofGroupoid) : Nonempty (pathFiber cls) := by
  refine Quotient.inductionOn cls ?_
  intro p
  exact ⟨⟨p, rfl⟩⟩

/-- Any two representatives of the same quotient class are homotopic. -/
theorem pathFiber_members_homotopic {cls : ProofGroupoid}
    (x y : pathFiber cls) : ProofPath.homotopic x.val y.val := by
  have hxy :
      Quotient.mk ProofPath.homotopicSetoid x.val =
        Quotient.mk ProofPath.homotopicSetoid y.val := by
    calc
      Quotient.mk ProofPath.homotopicSetoid x.val = cls := x.property
      _ = Quotient.mk ProofPath.homotopicSetoid y.val := y.property.symm
  exact Quotient.exact hxy

/-- The quotient class of the stationary path contains only homotopic members. -/
theorem pathFiber_id_all_homotopic (s : ProofState)
    (x : pathFiber (Quotient.mk ProofPath.homotopicSetoid (ProofPath.id s))) :
    ProofPath.homotopic x.val (ProofPath.id s) := by
  exact pathFiber_members_homotopic x ⟨ProofPath.id s, rfl⟩

/--
Dependent elimination for `ProofGroupoid`, mirroring HoTT path induction.
`Quotient.hrecOn` is the kernel primitive; `hcompat` is the transport law.
-/
noncomputable def groupoidJ
    (C : ProofGroupoid → Sort*)
    (d : (p : ProofPath) → C (Quotient.mk ProofPath.homotopicSetoid p))
    (hcompat : ∀ p q : ProofPath, ProofPath.homotopic p q → HEq (d p) (d q))
    (cls : ProofGroupoid) : C cls :=
  Quotient.hrecOn cls d (fun p q h => hcompat p q h)

/-- Beta rule for `groupoidJ` on representatives. -/
@[simp] theorem groupoidJ_beta
    (C : ProofGroupoid → Sort*)
    (d : (p : ProofPath) → C (Quotient.mk ProofPath.homotopicSetoid p))
    (hcompat : ∀ p q : ProofPath, ProofPath.homotopic p q → HEq (d p) (d q))
    (p : ProofPath) :
    groupoidJ C d hcompat (Quotient.mk ProofPath.homotopicSetoid p) = d p := by
  rfl

/-- Homotopy preserves the loop-likeness predicate. -/
theorem loopLike_eq_of_homotopic {p q : ProofPath}
    (h : ProofPath.homotopic p q) :
    p.loopLike = q.loopLike := by
  rcases h with ⟨hstart, hfinish, _⟩
  by_cases hp : p.start = p.finish
  · have hq : q.start = q.finish := by
      calc
        q.start = p.start := hstart.symm
        _ = p.finish := hp
        _ = q.finish := hfinish
    simp [ProofPath.loopLike, hp, hq]
  · have hq : ¬ q.start = q.finish := by
      intro hq
      apply hp
      calc
        p.start = q.start := hstart
        _ = q.finish := hq
        _ = p.finish := hfinish.symm
    simp [ProofPath.loopLike, hp, hq]

/--
Transport-support based obstruction classifier.
Unlike `Topology.obstructionClass`, this depends only on homotopy-invariant data.
-/
def obstructionClassT (loop : ProofPath) :
    ContextualityEngine.CechObstructionClass :=
  if loop.loopLike && !loop.transportSupport.isEmpty then
    ContextualityEngine.triangleObstructionClass
  else
    .none

/-- Transport-support based witness extraction compatible with the quotient. -/
def h1WitnessT? (loop : ProofPath) :
    Option
      (LensSheaf.Cech.True.H1Class
        LensSheaf.Cech.True.Triangle.skeleton) :=
  if loop.loopLike && !loop.transportSupport.isEmpty then
    some LensSheaf.Cech.True.Triangle.parityClass
  else
    none

/-- The transport-based obstruction classifier respects proof-path homotopy. -/
theorem obstructionClassT_respects_homotopy (p q : ProofPath)
    (h : ProofPath.homotopic p q) :
    obstructionClassT p = obstructionClassT q := by
  unfold obstructionClassT
  rw [loopLike_eq_of_homotopic h, h.2.2]

/-- The transport-based witness extractor respects proof-path homotopy. -/
theorem h1WitnessT_respects_homotopy (p q : ProofPath)
    (h : ProofPath.homotopic p q) :
    h1WitnessT? p = h1WitnessT? q := by
  unfold h1WitnessT?
  rw [loopLike_eq_of_homotopic h, h.2.2]

/-- Quotient-compatible obstruction classifier on proof classes. -/
def groupoidObstructionClass : ProofGroupoid → ContextualityEngine.CechObstructionClass :=
  Quotient.lift obstructionClassT obstructionClassT_respects_homotopy

/-- Quotient-compatible `H¹` witness extractor on proof classes. -/
def groupoidH1Witness? (cls : ProofGroupoid) :
    Option
      (LensSheaf.Cech.True.H1Class
        LensSheaf.Cech.True.Triangle.skeleton) :=
  Quotient.lift h1WitnessT? h1WitnessT_respects_homotopy cls

@[simp] theorem groupoidObstructionClass_mk (p : ProofPath) :
    groupoidObstructionClass (Quotient.mk ProofPath.homotopicSetoid p) =
      obstructionClassT p := by
  rfl

@[simp] theorem groupoidH1Witness_mk (p : ProofPath) :
    groupoidH1Witness? (Quotient.mk ProofPath.homotopicSetoid p) = h1WitnessT? p := by
  rfl

/-- The stationary canonical loop stays unobstructed for the transport-based classifier. -/
theorem obstructionClassT_canonicalStationaryLoop :
    obstructionClassT canonicalStationaryLoop = .none := by
  native_decide

/-- On the canonical stationary loop, the transport classifier agrees
    with the original obstructionClass. -/
theorem obstructionClassT_canonical_stationary :
    obstructionClassT canonicalStationaryLoop = obstructionClass canonicalStationaryLoop := by
  native_decide

/-- The transport-based classifier agrees with the canonical obstructed loop. -/
theorem obstructionClassT_canonicalObstructedLoop :
    obstructionClassT canonicalObstructedLoop =
      ContextualityEngine.CechObstructionClass.h1_global_section := by
  native_decide

/-- On the canonical obstructed loop, the transport classifier agrees
    with the original obstructionClass. -/
theorem obstructionClassT_canonical_obstructed :
    obstructionClassT canonicalObstructedLoop = obstructionClass canonicalObstructedLoop := by
  simpa using obstructionClassT_canonicalObstructedLoop

/-- The quotient classifier agrees with the canonical obstructed loop class. -/
theorem groupoidObstructionClass_canonicalObstructedLoop :
    groupoidObstructionClass
        (Quotient.mk ProofPath.homotopicSetoid canonicalObstructedLoop) =
      ContextualityEngine.CechObstructionClass.h1_global_section := by
  simpa using obstructionClassT_canonicalObstructedLoop

/--
Any proof-groupoid class classified as obstructed yields the concrete triangle
`H¹` witness already present in the Cech cohomology layer.
-/
theorem groupoid_obstruction_yields_H1 (cls : ProofGroupoid)
    (hcls :
      groupoidObstructionClass cls =
        ContextualityEngine.CechObstructionClass.h1_global_section) :
    ∃ w :
        LensSheaf.Cech.True.H1Class
          LensSheaf.Cech.True.Triangle.skeleton,
      groupoidH1Witness? cls = some w := by
  refine Quotient.inductionOn cls ?_ hcls
  intro p hp
  by_cases hcond : (p.loopLike && !p.transportSupport.isEmpty) = true
  · refine ⟨LensSheaf.Cech.True.Triangle.parityClass, ?_⟩
    simp [groupoidH1Witness?, h1WitnessT?, hcond]
  · have hcontra :
      ContextualityEngine.CechObstructionClass.none =
        ContextualityEngine.CechObstructionClass.h1_global_section := by
      simp [groupoidObstructionClass, obstructionClassT, hcond] at hp
    cases hcontra

/--
The canonical obstructed loop class admits the triangle `H¹` witness through the
quotient-compatible extractor.
-/
theorem groupoidH1Witness_canonicalObstructedLoop :
    ∃ w,
      groupoidH1Witness?
          (Quotient.mk ProofPath.homotopicSetoid canonicalObstructedLoop) = some w := by
  have hloop :
      canonicalObstructedLoop.loopLike = true ∧ canonicalObstructedLoop.transportSupport ≠ [] := by
    native_decide
  have hsupport : canonicalObstructedLoop.transportSupport.isEmpty = false := by
    cases hsupp : canonicalObstructedLoop.transportSupport with
    | nil =>
        exfalso
        exact hloop.2 hsupp
    | cons _ _ =>
        simp
  refine ⟨LensSheaf.Cech.True.Triangle.parityClass, ?_⟩
  simp [groupoidH1Witness?, h1WitnessT?, hloop.1, hsupport]

end PathIntegral
end HeytingLean
