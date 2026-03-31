import HeytingLean.NucleusDB

namespace HeytingLean.Tests.NucleusDB

open HeytingLean.NucleusDB

namespace TraceTopologySanity

inductive DemoTool where
  | ingest
  | verify
  | dispatch
  deriving DecidableEq, Fintype

open Sheaf.TraceTopology

def coarseMetric : ToolMetricSpace DemoTool where
  decEq := inferInstance
  dist
    | .ingest, .ingest => 0
    | .verify, .verify => 0
    | .dispatch, .dispatch => 0
    | .ingest, .verify => 3
    | .verify, .ingest => 3
    | .verify, .dispatch => 4
    | .dispatch, .verify => 4
    | .ingest, .dispatch => 7
    | .dispatch, .ingest => 7
  dist_self := by intro x; cases x <;> rfl
  dist_symm := by intro x y; cases x <;> cases y <;> rfl

def refinedMetric : ToolMetricSpace DemoTool where
  decEq := inferInstance
  dist
    | .ingest, .ingest => 0
    | .verify, .verify => 0
    | .dispatch, .dispatch => 0
    | .ingest, .verify => 2
    | .verify, .ingest => 2
    | .verify, .dispatch => 2
    | .dispatch, .verify => 2
    | .ingest, .dispatch => 5
    | .dispatch, .ingest => 5
  dist_self := by intro x; cases x <;> rfl
  dist_symm := by intro x y; cases x <;> cases y <;> rfl

theorem refinedMetric_refines_coarse : Refines coarseMetric refinedMetric := by
  intro x y
  cases x <;> cases y <;> decide

example : Neighbor coarseMetric 3 DemoTool.ingest DemoTool.verify := by
  simp [Neighbor, coarseMetric]

example : Nonempty {τ : VRSimplex coarseMetric 1 3 //
    τ.1.1 0 = DemoTool.ingest ∧ τ.1.1 1 = DemoTool.verify} := by
  refine ⟨⟨edgeToVRSimplex coarseMetric (x := DemoTool.ingest) (y := DemoTool.verify)
    (by decide) (by simp [Neighbor, coarseMetric]), ?_⟩⟩
  constructor <;> rfl

example : Connected refinedMetric 3 DemoTool.ingest DemoTool.dispatch := by
  exact Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single
      (by simp [Neighbor, refinedMetric] : Neighbor refinedMetric 3 DemoTool.ingest DemoTool.verify))
    (Relation.ReflTransGen.single
      (by simp [Neighbor, refinedMetric] : Neighbor refinedMetric 3 DemoTool.verify DemoTool.dispatch))

example : Connected coarseMetric 3 DemoTool.ingest DemoTool.verify →
    Connected refinedMetric 3 DemoTool.ingest DemoTool.verify := by
  exact refines_preserves_connected refinedMetric_refines_coarse

example :
    Fintype.card (VRSimplex coarseMetric 0 3) =
      Fintype.card (VRSimplex refinedMetric 0 3) := by
  simpa using refines_preserves_degreeZero_rank refinedMetric_refines_coarse 3

example :
    Fintype.card (ConnectedComponent refinedMetric 3) ≤
      Fintype.card (ConnectedComponent coarseMetric 3) := by
  simpa using card_connectedComponent_mono_of_refines refinedMetric_refines_coarse (t := 3)

example :
    Fintype.card (ConnectedComponent coarseMetric 3) ≤
      Fintype.card (VRSimplex coarseMetric 0 3) := by
  simpa using card_connectedComponent_le_degreeZero_rank coarseMetric 3

example : componentCount refinedMetric 3 ≤ componentCount coarseMetric 3 := by
  simpa using componentCount_mono_of_refines refinedMetric_refines_coarse (t := 3)

def globalStageTag : DemoTool → Nat := fun _ => 7

example : ComponentConstant coarseMetric 3 globalStageTag := by
  intro x y _hxy
  rfl

example :
    ∃ g : ConnectedComponent coarseMetric 3 → Nat,
      ∀ x : DemoTool, g (Quotient.mk'' x) = globalStageTag x := by
  simpa using (componentConstant_iff_exists_lift coarseMetric 3 globalStageTag).mp
    (show ComponentConstant coarseMetric 3 globalStageTag from by
      intro x y _hxy
      rfl)

end TraceTopologySanity

/-- Tiny executable nucleus model for sanity checks. -/
def natSystem : Core.NucleusSystem where
  State := Nat
  Delta := Nat
  apply := Nat.add

example : natSystem.step (3 : Nat) (4 : Nat) = (7 : Nat) := rfl

/-- Minimal certificate sanity check. -/
def natPolicy : Core.AuthorizationPolicy Nat Nat Unit :=
  fun _ _ _ => True

def natCert : Core.CommitCertificate Nat Nat Unit Nat.add natPolicy where
  prev := 5
  delta := 7
  auth := ()
  next := 12
  authOk := trivial
  nextEq := rfl

example : Core.verifyCommitCertificate natCert :=
  Core.verifyCommitCertificate_sound natCert

/-- Transparency consistency sanity check. -/
def oldSTH : Transparency.STH :=
  { size := 2, root := "r2", sig := "s2" }

def newSTH : Transparency.STH :=
  { size := 5, root := "r5", sig := "s5" }

def proof25 : Transparency.ConsistencyProof :=
  { oldSize := 2, newSize := 5 }

example : Transparency.verifyConsistency oldSTH newSTH proof25 := by
  exact ⟨rfl, rfl, by decide⟩

example : Transparency.Extends oldSTH newSTH :=
  Transparency.verifyConsistency_implies_extends
    (old := oldSTH) (new := newSTH) (π := proof25)
    (by exact ⟨rfl, rfl, by decide⟩)

/-- Security assumptions/profile sanity checks. -/
def kzgProfile : Security.SecurityProfile :=
  {
    backend := Security.CommitmentBackend.kzg
    assumptions := [Security.Assumption.kzgTrustedSetup]
  }

example : kzgProfile.WellFormed := by
  simp [Security.SecurityProfile.WellFormed, kzgProfile]

/-- Security parameter validity sanity checks. -/
def defaultParams : Security.ParameterSet :=
  {
    fieldBits := 64
    maxVectorLen := 1024
    maxDeltaWrites := 64
    maxWitnesses := 16
    minWitnessThreshold := 1
    maxWitnessThreshold := 16
    requireKzgTrustedSetup := true
    kzgTrustedSetupId := some "demo-setup"
  }

example : defaultParams.ValidFor Security.CommitmentBackend.kzg 3 2 := by
  refine Security.validFor_of_bounds defaultParams Security.CommitmentBackend.kzg 3 2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro hBackend hReq
    cases hBackend
    simp [defaultParams] at hReq
    simp [defaultParams]

/-- Reduction/refinement sanity checks. -/
def sampleReduction : Security.ReductionContract :=
  {
    claim := "state_auth_soundness"
    assumption := Security.Assumption.collisionResistance
    lossBits := 16
    maxQueries := 1000
  }

example : Security.ReductionBundleValid [sampleReduction] := by
  apply Security.singleton_bundle_valid
  simp [Security.ReductionContract.Valid, sampleReduction]

def absCommit : Security.AbstractCommit :=
  { height := 3, prevRoot := 10, nextRoot := 20 }

def concCommit : Security.ConcreteCommit :=
  { height := 3, prevRoot := 10, nextRoot := 20, sthSize := 3 }

example : Security.Refines absCommit concCommit := by
  simp [Security.Refines, absCommit, concCommit]

end HeytingLean.Tests.NucleusDB
