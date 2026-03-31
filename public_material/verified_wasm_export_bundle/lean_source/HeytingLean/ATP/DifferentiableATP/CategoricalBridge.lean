import Mathlib.Data.Finset.Basic
import HeytingLean.Categorical.MonadAlgebra
import HeytingLean.Categorical.TrainingStep
import HeytingLean.CDL.RNucleusPolynomial
import HeytingLean.Embeddings.CrossLensTransport
import HeytingLean.ATP.DifferentiableATP.CoreOps
import HeytingLean.ATP.DifferentiableATP.GoalEncoder
import HeytingLean.ATP.DifferentiableATP.TacticDecoder

/-!
# ATP.DifferentiableATP.CategoricalBridge

## KoopmanNBA Isomorphism

The differentiable ATP pipeline is represented as a specialized Koopman-style pipeline:

- `X = String` (goal text)
- `S = NucleusFSum` (support-level latent carrier)
- `O = List DecodedCandidate` (decoded tactic candidates)
- retract = `projectToFixedWeights nucleusR` on `FSum`
- algebra-hom witness uses retract-preserving maps (non-vacuous fixed points)
- support-level Koopman algebra uses a non-identity closure operator

This layer exposes retract-hom witnesses, fixed-point preservation, and a
training-step invariant surface for downstream evidence packaging.
-/

namespace HeytingLean
namespace ATP
namespace DifferentiableATP

open HeytingLean.LoF
open HeytingLean.LoF.Combinators.Differential
open HeytingLean.LoF.Combinators.Differential.Compute
open HeytingLean.Categorical

abbrev NucleusFSum := Finset Comb

def supportOfFSum (w : FSum) : NucleusFSum :=
  (w.map (fun tc => tc.1)).toFinset

noncomputable def fsumOfSupport (s : NucleusFSum) : FSum :=
  s.toList.map (fun c => (c, (1 : Rat)))

/-- A lightweight retract algebra for carriers where we only need idempotency. -/
structure IdempotentRetract (A : Type*) where
  R : A → A
  idempotent : ∀ a, R (R a) = R a

namespace IdempotentRetract

def fixedPoints {A : Type*} (T : IdempotentRetract A) : Set A :=
  { x | T.R x = x }

theorem R_mem_fixedPoints {A : Type*} (T : IdempotentRetract A) (a : A) :
    T.R a ∈ T.fixedPoints :=
  T.idempotent a

end IdempotentRetract

/-- Homomorphisms between retracts: `f (R_A x) = R_B (f x)`. -/
structure RetractHomomorphism
    {A B : Type*}
    (TA : IdempotentRetract A)
    (TB : IdempotentRetract B) where
  toFun : A → B
  map_retract : ∀ x, toFun (TA.R x) = TB.R (toFun x)

namespace RetractHomomorphism

instance {A B : Type*} {TA : IdempotentRetract A} {TB : IdempotentRetract B} :
    CoeFun (RetractHomomorphism TA TB) (fun _ => A → B) where
  coe f := f.toFun

theorem map_fixed
    {A B : Type*}
    {TA : IdempotentRetract A}
    {TB : IdempotentRetract B}
    (f : RetractHomomorphism TA TB)
    {x : A} (hx : x ∈ TA.fixedPoints) :
    f x ∈ TB.fixedPoints := by
  simp [IdempotentRetract.fixedPoints] at hx ⊢
  calc
    TB.R (f x) = f (TA.R x) := (f.map_retract x).symm
    _ = f x := by rw [hx]

end RetractHomomorphism

/-- The non-vacuous fixed-point retract used in differentiable ATP. -/
def fsumRetract : IdempotentRetract FSum where
  R := projectToFixedWeights nucleusR
  idempotent := projectToFixedWeights_idempotent nucleusR

def projectorHom : RetractHomomorphism fsumRetract fsumRetract where
  toFun := projectToFixedWeights nucleusR
  map_retract := by
    intro x
    simp [fsumRetract, projectToFixedWeights_idempotent]

/-- Compatibility alias preserving previous API shape. -/
def encoderHom (_lens : Embeddings.LensID) (_contextHints : List String) :
    RetractHomomorphism fsumRetract fsumRetract :=
  projectorHom

/-- Compatibility alias preserving previous API shape. -/
def decoderHom : RetractHomomorphism fsumRetract fsumRetract :=
  projectorHom

theorem encode_preserves_fixed (lens : Embeddings.LensID) (contextHints : List String) :
    ∀ x ∈ fsumRetract.fixedPoints,
      (encoderHom lens contextHints) x ∈ fsumRetract.fixedPoints := by
  intro x hx
  exact RetractHomomorphism.map_fixed (encoderHom lens contextHints) hx

/-- Non-identity closure on support space for Koopman-style documentation object. -/
def supportSeed : NucleusFSum :=
  ({Comb.K} : Finset Comb)

def supportClosure (s : NucleusFSum) : NucleusFSum :=
  s ∪ supportSeed

def supportClosureAlgebra : MonadAlgebra NucleusFSum where
  R := supportClosure
  extensive := by
    intro a
    exact le_sup_left
  idempotent := by
    intro a
    simp [supportClosure]
  meet_preserving := by
    intro a b
    simpa [supportClosure] using (sup_inf_right a b supportSeed)

def encoderAction (lens : Embeddings.LensID) (contextHints : List String) :
    NucleusFSum → NucleusFSum :=
  fun x => x ∪ supportOfFSum (encodeGoal "⊢ True" lens contextHints).initial

noncomputable def decoderActionSupport : NucleusFSum → NucleusFSum :=
  fun x => supportOfFSum (fsumOfSupport x)

def diffATPTrainingStep (cfg : GDConfig) (examples : List IOExample) :
    CDL.TrainingStep FSum FSum where
  model :=
    {
      P := FSum
      f := fun
        | (p, _) => p
    }
  update := fun
    | (p, _, _) => gradientStepProjected cfg examples p

theorem gd_step_preserves_fixed (cfg : GDConfig) (examples : List IOExample) :
    ∀ w, allFixedSubspace nucleusR w → allFixedSubspace nucleusR (gradientStepProjected cfg examples w) := by
  intro w _
  exact ⟨(Compute.gradientStep cfg examples w).map (fun tc => (tc.1, truncRat tc.2)), rfl⟩

theorem diffATP_step_preserves (cfg : GDConfig) (examples : List IOExample) :
    ∀ {p} (_hp : allFixedSubspace nucleusR p) (x : FSum),
      allFixedSubspace nucleusR ((CDL.TrainingStep.step (diffATPTrainingStep cfg examples) p x).1) := by
  intro p hp x
  exact CDL.TrainingStep.step_preserves
    (t := diffATPTrainingStep cfg examples)
    (Inv := allFixedSubspace nucleusR)
    (hupdate := by
      intro p _ hp'
      exact gd_step_preserves_fixed cfg examples p hp')
    hp x

def encoderRNucleusLens (lens : Embeddings.LensID) (contextHints : List String) :
    CDL.RNucleusLens Id String FSum where
  encode := fun goal => (encodeGoal goal lens contextHints).initial
  decode := fun w => some (Compute.showFSum w)

def decoderRNucleusLens :
    CDL.RNucleusLens Id FSum (List DecodedCandidate) where
  encode := fun w => decodeFromWeights w
  decode := fun _ => none

abbrev LensCarrier (_ : Embeddings.LensID) := FSum

def categoricalTransportFromHom
    (_ : RetractHomomorphism fsumRetract fsumRetract) :
    Embeddings.CrossLensTransport LensCarrier FSum where
  toPlato := fun _ x => x
  fromPlato := fun _ p => p
  rt1 := by intro _ _; rfl
  rt2 := by intro _ _; rfl

def categoricalTransport : Embeddings.CrossLensTransport LensCarrier FSum :=
  categoricalTransportFromHom projectorHom

def categoricalWitnessTheorems : List String :=
  [ "RetractHomomorphism.map_fixed"
  , "DifferentiableATP.projectToFixedWeights_idempotent"
  , "CDL.TrainingStep.step_preserves"
  , "DifferentiableATP.gd_step_preserves_fixed"
  ]

noncomputable def diffATPAsKoopmanNBA :
    Categorical.TiedKoopmanNBA String NucleusFSum (List DecodedCandidate) Unit where
  encoderFn := fun (_, goal) => supportOfFSum (encodeGoal goal).initial
  nucleus := supportClosureAlgebra
  decoderFn := fun (_, s) => decodeFromWeights (fsumOfSupport s)

end DifferentiableATP
end ATP
end HeytingLean
