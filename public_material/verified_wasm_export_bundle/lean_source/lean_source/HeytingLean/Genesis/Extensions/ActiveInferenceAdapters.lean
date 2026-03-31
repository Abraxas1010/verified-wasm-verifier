import HeytingLean.Genesis.CantorTopology
import HeytingLean.ActiveInference.Agent

/-!
# Genesis.Extensions.ActiveInferenceAdapters

Active-inference-specific adapters from post-re-entry witness interiors.

This extension remains opt-in and keeps the Genesis core import surface unchanged.
-/

namespace HeytingLean.Genesis.Extensions

open HeytingLean.ActiveInference
open scoped Classical

abbrev TernaryWitnessPoint := Set.range evalPath_to_ternaryCantor

/-- Finite observation alphabet induced by witness stabilization class. -/
inductive WitnessObservation where
  | stable
  | unstable
  deriving DecidableEq, Repr, Fintype

/-- Finite latent-state alphabet induced by witness phase parity. -/
inductive WitnessState where
  | markLike
  | unmarkLike
  deriving DecidableEq, Repr, Fintype

/-- Minimal finite action alphabet for witness-aware planning stubs. -/
inductive WitnessAction where
  | hold
  | flip
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- Active-inference belief payload exported from a witness interior. -/
structure ActiveBeliefState where
  depth : Nat
  support : Support
  observation : WitnessObservation
  state : WitnessState

@[ext] theorem ActiveBeliefState.ext
    (a b : ActiveBeliefState)
    (hdepth : a.depth = b.depth)
    (hsupport : a.support = b.support)
    (hobs : a.observation = b.observation)
    (hstate : a.state = b.state) : a = b := by
  cases a
  cases b
  cases hdepth
  cases hsupport
  cases hobs
  cases hstate
  rfl

/-- Stabilization-derived observation classifier. -/
noncomputable def observationOf (W : WitnessInterior) : WitnessObservation := by
  classical
  exact if eventualStabilizes W.source then .stable else .unstable

/-- Chosen path representative for a ternary witness point in the encoded range. -/
noncomputable def pathOfTernaryWitnessPoint (x : TernaryWitnessPoint) : EvalPath :=
  Classical.choose x.2

theorem pathOfTernaryWitnessPoint_spec (x : TernaryWitnessPoint) :
    evalPath_to_ternaryCantor (pathOfTernaryWitnessPoint x) = x.1 :=
  Classical.choose_spec x.2

/-- Ternary-point classifier: interprets encoded witness points via their path representative. -/
noncomputable def observationOfTernaryWitnessPoint (x : TernaryWitnessPoint) : WitnessObservation :=
  if (pathOfTernaryWitnessPoint x) 0 then .stable else .unstable

/-- Depth-parity state classifier. -/
def stateOf (W : WitnessInterior) : WitnessState :=
  if W.depth % 2 = 0 then .unmarkLike else .markLike

/-- Export the canonical active-inference belief payload for a witness interior. -/
noncomputable def toActiveBeliefState (W : WitnessInterior) : ActiveBeliefState where
  depth := W.depth
  support := (toBeliefState W).support
  observation := observationOf W
  state := stateOf W

theorem observationOf_stable_iff (W : WitnessInterior) :
    observationOf W = .stable ↔ eventualStabilizes W.source := by
  classical
  unfold observationOf
  by_cases h : eventualStabilizes W.source
  · simp [h]
  · simp [h]

theorem stateOf_markLike_iff (W : WitnessInterior) :
    stateOf W = .markLike ↔ W.depth % 2 ≠ 0 := by
  unfold stateOf
  by_cases h : W.depth % 2 = 0
  · simp [h]
  · simp [h]

/-- Depth-only state classifier used for ternary-point belief payload assembly. -/
def stateOfDepth (depth : Nat) : WitnessState :=
  if depth % 2 = 0 then .unmarkLike else .markLike

theorem stateOfDepth_eq_stateOf (W : WitnessInterior) :
    stateOfDepth W.depth = stateOf W := by
  rfl

/-- Metadata used to assemble active-belief payloads from ternary witness points. -/
structure TernaryWitnessMeta where
  depth : Nat
  postReentry : 0 < depth
  support : Support

/-- Build ternary metadata from an existing witness interior. -/
noncomputable def metaOfWitnessInterior (W : WitnessInterior) : TernaryWitnessMeta where
  depth := W.depth
  postReentry := W.postReentry
  support := (toBeliefState W).support

/-- Export an active-belief payload directly from a ternary witness point plus metadata. -/
noncomputable def ternaryPoint_toActiveBeliefState
    (x : TernaryWitnessPoint) (m : TernaryWitnessMeta) : ActiveBeliefState where
  depth := m.depth
  support := m.support
  observation := observationOfTernaryWitnessPoint x
  state := stateOfDepth m.depth

/-- Witness-derived generative model (finite and executable-friendly). -/
noncomputable def witnessGenerativeModel (W : WitnessInterior) :
    GenerativeModel WitnessObservation WitnessState where
  prior := fun s =>
    if s = stateOf W then (3 / 4 : NNReal) else (1 / 4 : NNReal)
  likelihood := fun s o =>
    if (s = .markLike ∧ o = .stable) ∨ (s = .unmarkLike ∧ o = .unstable) then
      (3 / 4 : NNReal)
    else
      (1 / 4 : NNReal)

/-- Witness-derived recognition model. -/
noncomputable def witnessRecognitionModel (W : WitnessInterior) :
    RecognitionModel WitnessObservation WitnessState where
  posterior := fun o s =>
    if (o = observationOf W ∧ s = stateOf W) then
      (3 / 4 : NNReal)
    else
      (1 / 4 : NNReal)

/-- Witness-derived policy prior over actions. -/
noncomputable def witnessPolicy (W : WitnessInterior) : WitnessState → WitnessAction → NNReal :=
  fun _ a =>
    match observationOf W, a with
    | .stable, .hold => 1
    | .stable, .flip => 0
    | .unstable, .hold => (1 / 2 : NNReal)
    | .unstable, .flip => (1 / 2 : NNReal)

/-- Canonical active-inference agent adapter for witness interiors. -/
noncomputable def witnessInterior_toAgent (W : WitnessInterior) :
    Agent WitnessObservation WitnessState WitnessAction where
  generativeModel := witnessGenerativeModel W
  recognitionModel := witnessRecognitionModel W
  policy := witnessPolicy W

/-- Canonical free-energy value attached to the current witness observation class. -/
noncomputable def witnessFreeEnergy (W : WitnessInterior) : ℝ :=
  freeEnergy
    (witnessInterior_toAgent W).generativeModel
    (witnessInterior_toAgent W).recognitionModel
    (observationOf W)

/-- Canonical surprise value for the current witness observation class. -/
noncomputable def witnessSurprise (W : WitnessInterior) : ℝ :=
  surprise (witnessInterior_toAgent W).generativeModel (observationOf W)

theorem witnessInterior_freeEnergy_bounds_surprise (W : WitnessInterior) :
    witnessFreeEnergy W ≥ witnessSurprise W := by
  simpa [witnessFreeEnergy, witnessSurprise] using
    (freeEnergy_bounds_surprise
      (gen := (witnessInterior_toAgent W).generativeModel)
      (rec := (witnessInterior_toAgent W).recognitionModel)
      (o := observationOf W))

/-- Placeholder expected-free-energy hook inherited from the base agent scaffold. -/
noncomputable def witnessExpectedFreeEnergy (W : WitnessInterior) : ℝ :=
  expectedFreeEnergy (witnessInterior_toAgent W) (stateOf W) WitnessAction.hold

theorem witnessInterior_expectedFreeEnergy_def (W : WitnessInterior) :
    witnessExpectedFreeEnergy W = 0 := by
  rfl

theorem pathOfTernaryWitnessPoint_eq_of_encode_eq
    (x : TernaryWitnessPoint) (p : EvalPath)
    (h : evalPath_to_ternaryCantor p = x.1) :
    pathOfTernaryWitnessPoint x = p := by
  apply evalPath_to_ternaryCantor_injective
  calc
    evalPath_to_ternaryCantor (pathOfTernaryWitnessPoint x) = x.1 :=
      pathOfTernaryWitnessPoint_spec x
    _ = evalPath_to_ternaryCantor p := h.symm

theorem pathOfTernaryWitnessPoint_of_evalPath (p : EvalPath) :
    pathOfTernaryWitnessPoint (evalPath_equiv_ternaryCantor_range p) = p := by
  apply pathOfTernaryWitnessPoint_eq_of_encode_eq
  simp [evalPath_equiv_ternaryCantor_range_apply]

theorem observationOfTernaryWitnessPoint_of_evalPath (p : EvalPath) :
    observationOfTernaryWitnessPoint (evalPath_equiv_ternaryCantor_range p)
      = (if p 0 then .stable else .unstable) := by
  simp [observationOfTernaryWitnessPoint, pathOfTernaryWitnessPoint_of_evalPath]

theorem observationOf_cantorCut_to_witnessInterior (p : EvalPath) (depth : Nat) :
    observationOf (cantorCut_to_witnessInterior p depth)
      = (if p 0 then .stable else .unstable) := by
  unfold observationOf
  cases hp : p 0 <;>
    simp [cantorCut_to_witnessInterior, headWitnessSource, hp, void_eventualStabilizes,
      life_not_eventualStabilizes]

/-- Agreement theorem: canonical encoded paths induce the same observation class as witness interiors. -/
theorem observationOfTernaryWitnessPoint_agrees_with_cantorCut
    (p : EvalPath) (depth : Nat) :
    observationOfTernaryWitnessPoint (evalPath_equiv_ternaryCantor_range p)
      = observationOf (cantorCut_to_witnessInterior p depth) := by
  simp [observationOfTernaryWitnessPoint_of_evalPath, observationOf_cantorCut_to_witnessInterior]

/-- Agreement theorem for full active-belief payload under canonical metadata. -/
theorem ternaryPoint_toActiveBeliefState_agrees_with_toActiveBeliefState
    (p : EvalPath) (depth : Nat) :
    ternaryPoint_toActiveBeliefState
        (evalPath_equiv_ternaryCantor_range p)
        (metaOfWitnessInterior (cantorCut_to_witnessInterior p depth))
      = toActiveBeliefState (cantorCut_to_witnessInterior p depth) := by
  ext
  · simp [ternaryPoint_toActiveBeliefState, metaOfWitnessInterior, toActiveBeliefState,
      cantorCut_to_witnessInterior]
  · simp [ternaryPoint_toActiveBeliefState, metaOfWitnessInterior, toActiveBeliefState,
      cantorCut_to_witnessInterior]
  · simpa [cantorCut_to_witnessInterior] using
      (observationOfTernaryWitnessPoint_agrees_with_cantorCut p depth)
  · simp [ternaryPoint_toActiveBeliefState, metaOfWitnessInterior, toActiveBeliefState,
      stateOfDepth, stateOf, cantorCut_to_witnessInterior]

end HeytingLean.Genesis.Extensions
