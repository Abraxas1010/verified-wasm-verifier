import Mathlib.Data.Real.Basic
import HeytingLean.Geo.GQRE.Core
import HeytingLean.Geo.GQRE.PMFlow

/-!
# GQRE nucleus-like flow on 2D fields

This module wraps the Perona–Malik gradient flow as a reusable
operator on discrete 2D fields (`Field2`), together with a simple
stability predicate expressed via the GQRE action.

The full Ωᴿ / `Reentry` integration lives elsewhere; here we only
provide a proto‑nucleus on numerical fields that can be composed
with those logical nuclei via bridges.
-/

namespace HeytingLean.Logic
namespace Nucleus
namespace GQRE

open HeytingLean.Geo.GQRE

/-- Perona–Malik / GQRE reentry operator on discrete fields.

`R_GQRE iters dt p` applies `iters` Perona–Malik steps with timestep
`dt` and parameters `p` to a 2D scalar field. -/
def R_GQRE (iters : Nat) (dt : Float) (p : Params) (φ : Field2) : Field2 :=
  pmIter p dt iters φ

/-- Convenience alias: apply the GQRE action functional to a field
by first computing its discrete gradient. -/
def gqreAction (p : Params) (φ : Field2) : Float :=
  let g := grad φ
  action p g.gx g.gy

/-- GQRE action gain between two fields. -/
def gqreGain (p : Params) (φIn φOut : Field2) : Float :=
  gqreAction p φOut - gqreAction p φIn

/-- Stability predicate: a field is `Stable` if a single application
of `R_GQRE iters dt p` changes the GQRE action by at most `tol`.

Intuitively, `Stable ... φ` means that `φ` is an approximate fixed
point of the GQRE flow, measured in the action space. -/
def Stable (p : Params) (iters : Nat) (dt tol : Float) (φ : Field2) : Prop :=
  let φOut := R_GQRE iters dt p φ
  let SIn  := gqreAction p φ
  let SOut := gqreAction p φOut
  Float.abs (SOut - SIn) ≤ tol

/-- Unfolding lemma for the stability predicate. -/
lemma Stable_iff (p : Params) (iters : Nat) (dt tol : Float) (φ : Field2) :
    Stable p iters dt tol φ ↔
      Float.abs (gqreAction p (R_GQRE iters dt p φ) - gqreAction p φ) ≤ tol := by
  rfl

/-- If a field is `Stable`, then the GQRE action changes by at most `tol`
under one application of `R_GQRE iters dt p`. -/
lemma Stable.action_diff_le (p : Params) (iters : Nat) (dt tol : Float)
    (φ : Field2) (h : Stable p iters dt tol φ) :
    Float.abs (gqreAction p (R_GQRE iters dt p φ) - gqreAction p φ) ≤ tol := by
  simpa [Stable] using h

end GQRE
end Nucleus
end HeytingLean.Logic

