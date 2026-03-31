import HeytingLean.Genesis.WitnessInterior
import HeytingLean.Genesis.MinimalDistinction
import HeytingLean.PerspectivalPlenum.CechObstruction
import HeytingLean.PerspectivalPlenum.ProjectionObligations
import HeytingLean.PerspectivalPlenum.Subsumption.NoneismAdapter

/-!
# Genesis.PlenumBridge

Phase-4 bridge from Genesis (`CoGame`, stabilization, witness interior) into:
- Perspectival Plenum sheaf/lens interfaces,
- contextual/cohomological obstruction surfaces, and
- Noneism subsumption adapters.

No axioms are introduced in this file.
-/

namespace HeytingLean.Genesis

open PerspectivalPlenum
open PerspectivalPlenum.LensSheaf
open PerspectivalPlenum.ContextualityEngine
open PerspectivalPlenum.Subsumption
open Noneism

/-- Canonical lens for exposing `LensSection` values as plenum witness sections. -/
def lensSectionLens : PerspectivalPlenum.Lens.SemanticLens LensSection where
  profile :=
    { name := "GenesisLensSection"
      contradictionPolicy := PerspectivalPlenum.Lens.ContradictionPolicy.constructive
      dimension := 1
      languageTag := "genesis.section"
      metricTag := "discrete" }
  witness _ := True
  contradicts _ := False

/-- Canonical lens object used by the sheaf-side section adapter. -/
def lensSectionObj : LensObj LensSection := ⟨lensSectionLens⟩

/-- Concrete plenum section target for `WitnessInterior -> LensSection`. -/
abbrev PlenumLensSection : Type 1 := WitnessSection lensSectionObj

instance : LensSectionLike PlenumLensSection where
  ofLensSection s := ⟨s, trivial⟩

/-- Phase-4 realization of the interface map `WitnessInterior -> LensSection`. -/
noncomputable def witnessInterior_to_lensSection (W : WitnessInterior) : PlenumLensSection :=
  ⟨toLensSection W, trivial⟩

@[simp] theorem witnessInterior_to_lensSection_val (W : WitnessInterior) :
    (witnessInterior_to_lensSection W).1 = toLensSection W := rfl

theorem witnessInterior_existsInPlenum (W : WitnessInterior) :
    LensSheaf.ExistsInPlenum (toLensSection W) :=
  LensSheaf.existsInPlenum_of_localWitness lensSectionObj trivial

/-- Canonical lens exposing emergent-region values inside the plenum witness layer. -/
def emergentRegionLens : PerspectivalPlenum.Lens.SemanticLens EmergentRegion where
  profile :=
    { name := "GenesisEmergentRegion"
      contradictionPolicy := PerspectivalPlenum.Lens.ContradictionPolicy.constructive
      dimension := 2
      languageTag := "genesis.emergentRegion"
      metricTag := "subset" }
  witness _ := True
  contradicts _ := False

/-- Canonical lens object for emergent-region transport. -/
def emergentRegionObj : LensObj EmergentRegion := ⟨emergentRegionLens⟩

/-- Concrete plenum witness section for the phase-4 minimal distinction region. -/
abbrev PlenumEmergentRegion : Type 1 := WitnessSection emergentRegionObj

noncomputable def minimalDistinction_section : PlenumEmergentRegion := ⟨minimalDistinction, trivial⟩

theorem minimalDistinction_existsInPlenum :
    LensSheaf.ExistsInPlenum minimalDistinction :=
  LensSheaf.existsInPlenum_of_localWitness emergentRegionObj trivial

theorem regionNucleus_existsInPlenum (U : EmergentRegion) :
    LensSheaf.ExistsInPlenum (regionNucleus U) :=
  LensSheaf.existsInPlenum_of_localWitness emergentRegionObj trivial

theorem minimalDistinction_not_collapse_in_emergentLens :
    ¬ PerspectivalPlenum.Lens.CollapseToBottom emergentRegionLens minimalDistinction := by
  simp [PerspectivalPlenum.Lens.CollapseToBottom, PerspectivalPlenum.Lens.LocallySatisfiable,
    emergentRegionLens, PerspectivalPlenum.Lens.allowsContradictions]

/-- Canonical lens for exposing `BeliefState` values as plenum witness sections. -/
def beliefStateLens : PerspectivalPlenum.Lens.SemanticLens BeliefState where
  profile :=
    { name := "GenesisBeliefState"
      contradictionPolicy := PerspectivalPlenum.Lens.ContradictionPolicy.weighted
      dimension := 2
      languageTag := "genesis.belief"
      metricTag := "stabilized-support" }
  witness _ := True
  contradicts _ := False

/-- Canonical lens object used by the belief-state bridge adapter. -/
def beliefStateObj : LensObj BeliefState := ⟨beliefStateLens⟩

/-- Concrete plenum belief-state target for `WitnessInterior -> BeliefState`. -/
abbrev PlenumBeliefState : Type := WitnessSection beliefStateObj

instance : BeliefStateLike PlenumBeliefState where
  ofBeliefState b := ⟨b, trivial⟩

/-- Phase-4 realization of the interface map `WitnessInterior -> BeliefState`. -/
noncomputable def witnessInterior_to_beliefState (W : WitnessInterior) : PlenumBeliefState :=
  ⟨toBeliefState W, trivial⟩

@[simp] theorem witnessInterior_to_beliefState_val (W : WitnessInterior) :
    (witnessInterior_to_beliefState W).1 = toBeliefState W := rfl

/-- Detectability predicate read from the interior image in plenum belief space. -/
def detectsObstruction (b : PlenumBeliefState) : Prop :=
  0 ∈ b.1.support

/-- Target contextual obstruction profile (triangle witness). -/
def hasCechOrContextualityObstruction (_W : WitnessInterior) : Prop :=
  HasCechH1
    Quantum.Contextuality.Triangle.X
    Quantum.Contextuality.Triangle.cover
    Quantum.Contextuality.Triangle.model
    (fun {C} hC => Quantum.Contextuality.Triangle.coverSubX (C := C) hC)

theorem hasCechOrContextualityObstruction_intro (W : WitnessInterior) :
    hasCechOrContextualityObstruction W := by
  exact ProjectionObligations.triangle_cech_h1_hook

theorem witnessInterior_detects_obstruction (W : WitnessInterior) :
    detectsObstruction (witnessInterior_to_beliefState W) := by
  change 0 ∈ (toBeliefState W).support
  change 0 ∈ W.support
  unfold WitnessInterior.support
  simp [collapseNucleus_apply]

/--
Bridge theorem: obstruction is detectable from the post-re-entry interior image and
aligns with the established plenum contextual/cohomological obstruction witness.
-/
theorem interior_detects_obstruction (W : WitnessInterior) :
    detectsObstruction (witnessInterior_to_beliefState W) ∧
      hasCechOrContextualityObstruction W := by
  exact ⟨witnessInterior_detects_obstruction W, hasCechOrContextualityObstruction_intro W⟩

theorem interior_detects_obstruction_iff (W : WitnessInterior) :
    detectsObstruction (witnessInterior_to_beliefState W) ↔
      hasCechOrContextualityObstruction W := by
  constructor
  · intro _h
    exact hasCechOrContextualityObstruction_intro W
  · intro _h
    exact witnessInterior_detects_obstruction W

/-- One-step stabilization criterion used by the dynamic Noneism bridge. -/
def baseStabilizes (G : CoGame.{0}) : Prop :=
  eventualStabilizes G

theorem void_baseStabilizes : baseStabilizes CoGame.Void := by
  simpa [baseStabilizes] using void_eventualStabilizes

theorem life_not_baseStabilizes : ¬ baseStabilizes CoGame.Life := by
  simpa [baseStabilizes] using life_not_eventualStabilizes

/-- Local atom type used for the stabilization->noneist bridge formula. -/
inductive BridgeAtom where
  | token
  deriving DecidableEq, Repr

/-- Strict (Boolean) lens adapter used to interpret impossible objects. -/
def strictNoneismAdapter : NoneismLensAdapter BridgeAtom :=
  { lens :=
      { profile :=
          { name := "GenesisStrict"
            contradictionPolicy := PerspectivalPlenum.Lens.ContradictionPolicy.booleanStrict
            dimension := 2
            languageTag := "noneism.bridge"
            metricTag := "base-stabilization" }
        witness := fun _ => True
        contradicts := fun φ => φ = (.bot : Formula BridgeAtom) } }

/-- Permissive (paraconsistent) lens adapter for cross-lens survival checks. -/
def permissiveNoneismAdapter : NoneismLensAdapter BridgeAtom :=
  { lens :=
      { profile :=
          { name := "GenesisPermissive"
            contradictionPolicy := PerspectivalPlenum.Lens.ContradictionPolicy.paraconsistent
            dimension := 3
            languageTag := "noneism.bridge"
            metricTag := "base-stabilization" }
        witness := fun _ => True
        contradicts := fun φ => φ = (.bot : Formula BridgeAtom) } }

@[simp] theorem strictNoneismAdapter_not_allows :
    ¬ PerspectivalPlenum.Lens.allowsContradictions strictNoneismAdapter.lens.profile := by
  simp [strictNoneismAdapter, PerspectivalPlenum.Lens.allowsContradictions]

@[simp] theorem permissiveNoneismAdapter_allows :
    PerspectivalPlenum.Lens.allowsContradictions permissiveNoneismAdapter.lens.profile := by
  simp [permissiveNoneismAdapter, PerspectivalPlenum.Lens.allowsContradictions]

/--
Dynamic encoding: a co-game maps to `⊤` when it stabilizes at base depth and to
`⊥` when it fails to stabilize.
-/
noncomputable def stabilizationFormula (G : CoGame.{0}) : Formula BridgeAtom := by
  classical
  exact if baseStabilizes G then .top else .bot

@[simp] theorem stabilizationFormula_of_stable (G : CoGame) (h : baseStabilizes G) :
    stabilizationFormula G = (.top : Formula BridgeAtom) := by
  classical
  simp [stabilizationFormula, h]

@[simp] theorem stabilizationFormula_of_unstable (G : CoGame) (h : ¬ baseStabilizes G) :
    stabilizationFormula G = (.bot : Formula BridgeAtom) := by
  classical
  simp [stabilizationFormula, h]

/--
Bridge theorem (priority): strict-lens noneist impossibility is equivalent to
failure of stabilization.
-/
theorem noneist_objects_are_unstabilizable (G : CoGame.{0}) :
    strictNoneismAdapter.interpretedImpossible (stabilizationFormula G)
      ↔ ¬ baseStabilizes G := by
  classical
  by_cases h : baseStabilizes G
  · simp [NoneismLensAdapter.interpretedImpossible,
      Lens.CollapseToBottom, Lens.LocallySatisfiable, strictNoneismAdapter,
      PerspectivalPlenum.Lens.allowsContradictions, stabilizationFormula, h]
  · simp [NoneismLensAdapter.interpretedImpossible,
      Lens.CollapseToBottom, Lens.LocallySatisfiable, strictNoneismAdapter,
      PerspectivalPlenum.Lens.allowsContradictions, stabilizationFormula, h]

theorem permissive_survival (G : CoGame.{0}) :
    permissiveNoneismAdapter.interpretedClaim (stabilizationFormula G) := by
  classical
  by_cases h : baseStabilizes G
  · simp [NoneismLensAdapter.interpretedClaim, Lens.LocallySatisfiable,
      permissiveNoneismAdapter, PerspectivalPlenum.Lens.allowsContradictions,
      stabilizationFormula, h]
  · simp [NoneismLensAdapter.interpretedClaim, Lens.LocallySatisfiable,
      permissiveNoneismAdapter, PerspectivalPlenum.Lens.allowsContradictions,
      stabilizationFormula, h]

/--
Non-stabilizing co-games collapse in strict noneist reading while remaining
locally satisfiable in a permissive lens.
-/
theorem nonstabilizing_collapse_and_survival (G : CoGame.{0}) (hG : ¬ baseStabilizes G) :
    strictNoneismAdapter.interpretedImpossible (stabilizationFormula G) ∧
      permissiveNoneismAdapter.interpretedClaim (stabilizationFormula G) := by
  exact ⟨(noneist_objects_are_unstabilizable G).2 hG, permissive_survival G⟩

theorem life_noneist_bridge :
    strictNoneismAdapter.interpretedImpossible (stabilizationFormula CoGame.Life) ∧
      permissiveNoneismAdapter.interpretedClaim (stabilizationFormula CoGame.Life) := by
  exact nonstabilizing_collapse_and_survival CoGame.Life life_not_baseStabilizes

/--
Canonical bridge entrypoint for the noneist oscillatory interpretation:
`Life` is non-stabilizing, collapses in strict reading, and survives in permissive reading.
-/
theorem noneist_oscillatory_interpretation_bridge :
    ¬ baseStabilizes CoGame.Life ∧
      strictNoneismAdapter.interpretedImpossible (stabilizationFormula CoGame.Life) ∧
      permissiveNoneismAdapter.interpretedClaim (stabilizationFormula CoGame.Life) := by
  exact ⟨life_not_baseStabilizes, life_noneist_bridge⟩

end HeytingLean.Genesis
