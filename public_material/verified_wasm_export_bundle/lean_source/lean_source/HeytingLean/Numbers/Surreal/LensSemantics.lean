import HeytingLean.Numbers.Surreal.LensLattice

/-!
# Surreal lens semantics (lightweight constraints)

`LensLattice` intentionally provides only *structural* compossibility (Hamming distance ≤ 1).
This module adds a lightweight, executable layer of **semantic compatibility** checks, keeping
the policy local and transparent.

The checks are intentionally conservative and are meant to prevent obviously incoherent
combinations such as:
- a `Relative` semantic lens paired with a non-`Turing` computational lens.
- transitions between mutually incompatible semantic lenses.

This is a *validation* layer, not a formal semantics development.
-/

namespace HeytingLean
namespace Numbers
namespace Surreal

open Lean

structure LensRequirements where
  requiredAxioms : List String := []
  incompatibleWith : List SemanticLens := []
  computationalOk : ComputationalLens → Bool := fun _ => true

def semanticRequirements : SemanticLens → LensRequirements
  | .eff =>
      { requiredAxioms := ["decidable_equality", "computable_functions"]
        incompatibleWith := []
        computationalOk := fun _ => true }
  | .modified =>
      { requiredAxioms := ["modified_realizability"]
        incompatibleWith := [.relative]
        computationalOk := fun c => c != .turing }
  | .lifschitz =>
      { requiredAxioms := ["lifschitz_realizability"]
        incompatibleWith := [.sheafOnR]
        computationalOk := fun c => c == .functional }
  | .relative =>
      { requiredAxioms := ["oracle_access", "relative_computability"]
        incompatibleWith := [.modified]
        computationalOk := fun c => c == .turing }
  | .dialectica =>
      { requiredAxioms := ["witness", "challenge_response"]
        incompatibleWith := []
        computationalOk := fun _ => true }
  | .sheafOnR =>
      { requiredAxioms := ["continuity", "topology"]
        incompatibleWith := [.lifschitz]
        computationalOk := fun c => c != .method }

private def checkPoint (p : LensPoint) : Except String Unit := do
  let req := semanticRequirements p.sem
  if !(req.computationalOk p.comp) then
    throw s!"semantic/computational mismatch: sem={p.sem}, comp={p.comp}"

private def checkTransition (p q : LensPoint) : Except String Unit := do
  let reqP := semanticRequirements p.sem
  let reqQ := semanticRequirements q.sem
  if q.sem ∈ reqP.incompatibleWith then
    throw s!"semantic transition incompatible: {p.sem} → {q.sem}"
  if p.sem ∈ reqQ.incompatibleWith then
    throw s!"semantic transition incompatible: {p.sem} → {q.sem}"

/-- Semantic compatibility check for a lattice path. -/
def compossiblePathSemantic (path : List LensPoint) : Except String Unit := do
  if !compossiblePath path then
    throw "lensPath violates structural constraint (changes > 1 axis per step)"
  for p in path do
    checkPoint p
  match path with
  | [] => pure ()
  | [_] => pure ()
  | p :: rest =>
      let mut prev := p
      for q in rest do
        checkTransition prev q
        prev := q

end Surreal
end Numbers
end HeytingLean

