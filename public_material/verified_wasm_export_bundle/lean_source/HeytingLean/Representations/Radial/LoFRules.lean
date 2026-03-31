import HeytingLean.Representations.Radial.Core
import Mathlib.Data.List.Basic

/-!
# LoF rules as ring transitions (scaffold)

This module provides a minimal bridge between:
- rule applications (with a declared ring delta), and
- an induced adjacency matrix over a radial graph.

It also defines a lightweight `LoFExpr` and a correspondence predicate used as a theorem hook.
-/

namespace HeytingLean
namespace Representations
namespace Radial
namespace LoFRules

open HeytingLean.Representations.Radial

/-- LoF rule types with their ring effect. -/
inductive RuleType
  | mark
  | cross
  | call
  | reentry
  deriving Repr, DecidableEq

/-- Apply the ring delta of a rule to a ring index (as a natural number). -/
def RuleType.applyDelta : RuleType → Nat → Nat
  | .mark => fun r => r + 1
  | .cross => fun r => r
  | .call => fun r => r - 1
  | .reentry => fun r => r

/-- A rule application between states, with a well-formed ring transition. -/
structure RuleApplication (G : RadialGraph) where
  source : G.StateIdx
  target : G.StateIdx
  rule : RuleType
  valid : G.assemblyIndex target = rule.applyDelta (G.assemblyIndex source)

/-- Build an unweighted radial matrix from a list of rules (entry = 1 iff a rule exists). -/
def loFRadialMatrix (G : RadialGraph) (rules : List (RuleApplication G)) : RadialMatrix G Nat :=
  { mat := fun s t =>
      if rules.any (fun r => r.source = s ∧ r.target = t) then 1 else 0 }

/-! ## Expression depth hook -/

/-- A lightweight LoF expression type used for depth accounting (scaffold). -/
inductive LoFExpr
  | void
  | mark (a : LoFExpr)
  | cross (a b : LoFExpr)
  | reentry (a : LoFExpr)
  deriving Repr, DecidableEq

def loFExprDepth : LoFExpr → Nat
  | .void => 0
  | .mark a => 1 + loFExprDepth a
  | .cross a b => max (loFExprDepth a) (loFExprDepth b)
  | .reentry a => loFExprDepth a

/-- Correspondence predicate (hook): a state corresponds to an expression at matching depth. -/
def stateCorrespondsToExpr (G : RadialGraph) (s : G.StateIdx) (e : LoFExpr) : Prop :=
  G.assemblyIndex s = loFExprDepth e

theorem lof_depth_eq_ring (G : RadialGraph) (s : G.StateIdx) (e : LoFExpr)
    (h : stateCorrespondsToExpr G s e) :
    loFExprDepth e = G.assemblyIndex s := by
  simpa [stateCorrespondsToExpr] using h.symm

end LoFRules
end Radial
end Representations
end HeytingLean

