import HeytingLean.ATP.LaneChanging
import HeytingLean.ATP.DifferentiableATP.SheafTransport

/-!
# PathIntegral.ProofPath

Discrete proof paths over the existing multi-lens ATP surface.
-/

namespace HeytingLean
namespace PathIntegral

open HeytingLean.Embeddings
open HeytingLean.ATP
open HeytingLean.LoF.Combinators.Differential.Compute

/-- Local tactic identifier for path-integral ATP search. -/
abbrev TacticId := String

/-- Proof-search state encoded in a specific lens. -/
structure ProofState where
  lens : LensID
  goal : FSum
  context : String := ""
  depth : Nat := 0
  history : List LensID := []
  deriving Repr, DecidableEq

namespace ProofState

def toPosition (s : ProofState) : ATP.ProofPosition :=
  {
    lens := s.lens
    depth := s.depth
    history := s.history
  }

end ProofState

/-- One directed move in proof space. -/
structure ProofStep where
  source : ProofState
  target : ProofState
  tactic : TacticId
  lensTransition : Option (LensID × LensID) := none
  deriving Repr, DecidableEq

/-- Signature data used by action and topology layers. -/
structure StepSignature where
  sourceLens : LensID
  targetLens : LensID
  tacticLength : Nat
  sourceGoalComplexity : Rat
  targetGoalComplexity : Rat
  sourceDepth : Nat
  targetDepth : Nat
  deriving Repr, DecidableEq

namespace ProofStep

def goalComplexity (s : ProofState) : Rat :=
  l2NormSq s.goal

def signature (step : ProofStep) : StepSignature :=
  {
    sourceLens := step.source.lens
    targetLens := step.target.lens
    tacticLength := step.tactic.length
    sourceGoalComplexity := goalComplexity step.source
    targetGoalComplexity := goalComplexity step.target
    sourceDepth := step.source.depth
    targetDepth := step.target.depth
  }

end ProofStep

/-- Connectivity witness for a list of proof steps. -/
inductive PathValid : ProofState → List ProofStep → ProofState → Prop where
  | nil (s : ProofState) : PathValid s [] s
  | cons {s t : ProofState} {step : ProofStep} {rest : List ProofStep}
      (hs : step.source = s)
      (hrest : PathValid step.target rest t) :
      PathValid s (step :: rest) t

/-- A path through proof search space. -/
structure ProofPath where
  start : ProofState
  finish : ProofState
  steps : List ProofStep
  deriving Repr, DecidableEq

namespace ProofPath

def valid (p : ProofPath) : Prop :=
  PathValid p.start p.steps p.finish

def signature (p : ProofPath) : List StepSignature :=
  p.steps.map ProofStep.signature

def id (s : ProofState) : ProofPath :=
  {
    start := s
    finish := s
    steps := []
  }

def singleton (step : ProofStep) : ProofPath :=
  {
    start := step.source
    finish := step.target
    steps := [step]
  }

def comp (p q : ProofPath) : ProofPath :=
  {
    start := p.start
    finish := q.finish
    steps := p.steps ++ q.steps
  }

def length (p : ProofPath) : Nat :=
  p.steps.length

def finalPosition (p : ProofPath) : ATP.ProofPosition :=
  p.finish.toPosition

def lensSet (p : ProofPath) : List LensID :=
  (p.steps.map (·.source.lens)) ++ [p.finish.lens]

theorem singleton_valid (step : ProofStep) :
    (singleton step).valid := by
  exact PathValid.cons rfl (PathValid.nil step.target)

theorem id_valid (s : ProofState) : (id s).valid := by
  exact PathValid.nil s

theorem PathValid.append
    {s mid t : ProofState}
    {xs ys : List ProofStep}
    (hx : PathValid s xs mid)
    (hy : PathValid mid ys t) :
    PathValid s (xs ++ ys) t := by
  induction hx with
  | nil _ =>
      simpa using hy
  | @cons s t step rest hs hrest ih =>
      simp [List.cons_append]
      exact PathValid.cons hs (ih hy)

theorem comp_valid {p q : ProofPath}
    (hp : p.valid)
    (hq : q.valid)
    (hjoin : p.finish = q.start) :
    (p.comp q).valid := by
  unfold ProofPath.valid at hp hq ⊢
  cases p
  cases q
  simp [ProofPath.comp] at hjoin ⊢
  subst hjoin
  exact PathValid.append hp hq

theorem comp_assoc (p q r : ProofPath) :
    (p.comp q).comp r = p.comp (q.comp r) := by
  cases p
  cases q
  cases r
  simp [ProofPath.comp, List.append_assoc]

theorem comp_id_left (s : ProofState) (p : ProofPath) (h : s = p.start) :
    (ProofPath.id s).comp p = p := by
  cases p
  cases h
  simp [ProofPath.id, ProofPath.comp]

theorem comp_id_right (s : ProofState) (p : ProofPath) (h : p.finish = s) :
    p.comp (ProofPath.id s) = p := by
  cases p
  cases h
  simp [ProofPath.id, ProofPath.comp]

theorem length_comp (p q : ProofPath) :
    (p.comp q).length = p.length + q.length := by
  simp [ProofPath.comp, ProofPath.length, List.length_append]

end ProofPath

end PathIntegral
end HeytingLean
