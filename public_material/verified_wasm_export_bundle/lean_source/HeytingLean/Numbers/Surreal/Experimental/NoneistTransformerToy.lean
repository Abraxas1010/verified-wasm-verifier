import HeytingLean.Numbers.Surreal.Experimental.UnmarkedPrior

namespace HeytingLean
namespace Numbers
namespace Surreal
namespace Experimental

open HeytingLean.Numbers.SurrealCore

noncomputable section

/-- Minimal parameter surface for the experimental transformer lane. -/
structure TransformerWeights where
  budget : Nat := 0

/-- Choose one contextual token and apply boundary-aware projection. -/
def computeAttention (w : TransformerWeights)
    (q : AttentionToken) (ctx : List AttentionToken) : AttentionToken :=
  match ctx with
  | [] => unmarkedSpace
  | k :: _ => boundaryProjection w.budget q k

/-- One toy transformer layer over experimental tokens. -/
def toyTransformerLayer (w : TransformerWeights)
    (xs : List AttentionToken) : List AttentionToken :=
  xs.map (fun q => computeAttention w q xs)

@[simp] theorem toyTransformerLayer_length
    (w : TransformerWeights) (xs : List AttentionToken) :
    (toyTransformerLayer w xs).length = xs.length := by
  simp [toyTransformerLayer]

/-- Convenience entry point from pregame streams. -/
def runFromPregames (w : TransformerWeights)
    (xs : List PreGame) : List AttentionToken :=
  toyTransformerLayer w (initWithUnmarked xs)

@[simp] theorem runFromPregames_length
    (w : TransformerWeights) (xs : List PreGame) :
    (runFromPregames w xs).length = xs.length := by
  simp [runFromPregames, toyTransformerLayer, initWithUnmarked]

/-- Single-token first step is completely classified by unmarked-boundary behavior. -/
theorem first_step_singleton_is_identity_or_boundary
    (w : TransformerWeights) (g : PreGame) :
    let t := { core := g, velocity := 0, anchor := unmarkedSpace.anchor }
    boundaryProjection w.budget t t = t ∨
      (boundaryProjection w.budget t t).core = attendBoundary t t := by
  intro t
  by_cases h : syncBudget w.budget t t
  · left
    simp [boundaryProjection, h]
  · right
    simp [boundaryProjection, h]

end

end Experimental
end Surreal
end Numbers
end HeytingLean
