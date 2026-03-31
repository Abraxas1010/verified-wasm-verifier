import HeytingLean.PathIntegral.Topology

/-!
# PathIntegral.ObstructionMonitor

Thin obstruction-monitoring layer over the existing Čech obstruction detector.
-/

namespace HeytingLean
namespace PathIntegral

abbrev CechObstructionClass :=
  HeytingLean.PerspectivalPlenum.ContextualityEngine.CechObstructionClass

inductive ObstructionResult where
  | clear
  | obstructed (cls : CechObstructionClass)
  deriving Repr, DecidableEq

/-- Delegate directly to the topology layer's obstruction classifier. -/
def checkObstruction (path : ProofPath) : ObstructionResult :=
  let cls := obstructionClass path
  if cls = .none then
    .clear
  else
    .obstructed cls

/-- Partition a scored beam into clear and obstructed paths. -/
def partitionByObstruction (beam : List (ProofPath × Float)) :
    List (ProofPath × Float) × List (ProofPath × Float) :=
  beam.partition fun (path, _) => checkObstruction path = .clear

theorem canonical_loop_detected :
    checkObstruction canonicalObstructedLoop = .obstructed .h1_global_section := by
  native_decide

theorem singleton_clear (step : ProofStep) :
    checkObstruction (ProofPath.singleton step) = .clear := by
  unfold checkObstruction
  by_cases hloop : (ProofPath.singleton step).loopLike = true
  · have hsame : step.source = step.target := by
      simpa [ProofPath.loopLike, ProofPath.singleton] using hloop
    have hmult : (ProofPath.singleton step).usesMultipleLenses = false := by
      have hlen : [step.target.lens, step.target.lens].eraseDups.length ≤ 1 := by
        cases step.target.lens <;> native_decide
      simpa [ProofPath.usesMultipleLenses, ProofPath.lensSet, ProofPath.singleton, hsame] using hlen
    simp [obstructionClass, hloop, hmult]
  · simp [obstructionClass, hloop]

theorem simple_path_clear (step : ProofStep) (_h : step.lensTransition = none) :
    checkObstruction (ProofPath.singleton step) = .clear := by
  exact singleton_clear step

end PathIntegral
end HeytingLean
