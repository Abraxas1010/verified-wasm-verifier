import HeytingLean.Geo.GQRE.Core
import HeytingLean.Geo.GQRE.PMFlow
import HeytingLean.Logic.Nucleus.R_GQRE
import HeytingLean.Occam.GQRE

/-!
# GQRE contract guards

Predicate-level guards expressing simple policy-style constraints on
GQRE / Perona–Malik flows over discrete fields.

These are intended to be used by higher-level payment or agent
contracts (e.g. AgentPM) that want to require:

* a minimum GQRE action gain,
* a minimum edge-preservation score,
* an upper bound on the average GQRE Lagrangian, and/or
* that a field has been preprocessed by the `R_GQRE` flow.
-/

namespace HeytingLean
namespace Contracts
namespace GQREGuards

open HeytingLean.Geo.GQRE

/-- Context for evaluating GQRE guards: the parameters and
input/output fields around a GQRE / PM flow. -/
structure Context where
  params : Params
  iters  : Nat
  dt     : Float
  φIn    : Field2
  φOut   : Field2
  deriving Repr

/-- A GQRE guard is a pure predicate over a `Context`. -/
abbrev Guard := Context → Prop

/-- Require a minimum GQRE action gain:
`S_out - S_in ≥ δ`. -/
def RequiresGQREGain (δ : Float) : Guard :=
  fun ctx =>
    let gain := HeytingLean.Occam.GQRE.GQREGain ctx.params ctx.φIn ctx.φOut
    gain ≥ δ

/-- Require that the Jaccard-based edge-preservation score is at
least `τ` when edges are extracted from the top-`q` fraction of
gradient magnitudes (default: 10%). -/
def MinEdgePreserve (τ : Float) (q : Float := 0.1) : Guard :=
  fun ctx =>
    let score := HeytingLean.Occam.GQRE.edgePreserve ctx.φIn ctx.φOut q
    score ≥ τ

/-- Require that the average GQRE Lagrangian on the output field
is bounded above by `ub`.  This can be used as an Occam-style
complexity regulariser. -/
def MaxLgqre (ub : Float) : Guard :=
  fun ctx =>
    let L := HeytingLean.Occam.GQRE.LgqreMean ctx.params ctx.φOut
    L ≤ ub

/-- Require that the output field is exactly the result of applying
`R_GQRE` with the context's parameters to the input field. -/
def UseRGQRE : Guard :=
  fun ctx =>
    ctx.φOut =
      HeytingLean.Logic.Nucleus.GQRE.R_GQRE ctx.iters ctx.dt ctx.params ctx.φIn

/-- Guard expressing one-step action stability for the output field:
the GQRE action changes by at most `tol` under one more application
of `R_GQRE` with the same parameters. -/
def StableOutput (tol : Float) : Guard :=
  fun ctx =>
    HeytingLean.Logic.Nucleus.GQRE.Stable ctx.params ctx.iters ctx.dt tol ctx.φOut

end GQREGuards
end Contracts
end HeytingLean
