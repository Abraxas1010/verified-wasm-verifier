import HeytingLean.ProgramCalculus.Core
import HeytingLean.Embeddings.Adelic
import HeytingLean.Embeddings.CoreLenses
import HeytingLean.Embeddings.LensIDCoreBridge

/-!
# ProgramCalculus.AdelicOps

An interface for testing “adelic arithmetic as program transformation” hypotheses.

The intent is **not** to assert identities like “multiplication *is* partial evaluation”.
Instead, we:

* define a lens-indexed depth/valuation `Depth := LensID → Int`,
* expose program operations (`mul`, `add`, `normalize`, `renormDiv`),
* require *valuation-style laws* and a *division reconstruction* law.

Concrete instantiations can then be validated both in Lean (semantic laws) and at runtime
(via the repo’s executable pipeline).
-/

namespace HeytingLean
namespace ProgramCalculus

open HeytingLean.Embeddings

universe u

/-- Tag-indexed “depth/valuation” (adelic-style). -/
abbrev GenericDepth (τ : Type u) : Type u :=
  τ → Int

/-- Legacy 7-lens depth profile (kept for backwards compatibility). -/
abbrev Depth : Type := GenericDepth LensID

/-- Abstract operations and laws making the “adelic arithmetic” hypothesis testable. -/
structure GenericAdelicProgramOps (τ : Type u) (language : Language) where
  depth : language.Program → GenericDepth τ
  mul : language.Program → language.Program → language.Program
  add : language.Program → language.Program → language.Program
  normalize : language.Program → language.Program
  renormDiv : language.Program → language.Program → language.Program × language.Program

  /- ### Laws (the “why”) -/

  /-- Multiplicative depth law (valuation additivity). -/
  depth_mul :
    ∀ (a b : language.Program) (lens : τ),
      depth (mul a b) lens = depth a lens + depth b lens

  /-- Additive depth law (valuation inequality; adelic/p-adic style). -/
  depth_add :
    ∀ (a b : language.Program) (lens : τ),
      min (depth a lens) (depth b lens) ≤ depth (add a b) lens

  /-- Normalization does not increase depth. -/
  depth_norm :
    ∀ (a : language.Program) (lens : τ),
      depth (normalize a) lens ≤ depth a lens

  /-- Division-style reconstruction: quotient+residual recombine back to the original, semantically. -/
  div_reconstruct :
    ∀ (a e : language.Program),
      let (q, r) := renormDiv a e
      ObsEq language (add (mul q e) r) a

/-- Legacy 7-lens specialization retained for existing callers. -/
abbrev AdelicProgramOps (language : Language) :=
  GenericAdelicProgramOps LensID language

/-- Project a 100-lens depth profile down to the legacy 7-lens profile. -/
def restrictCoreDepthToLensID (d : GenericDepth CoreLensTag) : Depth :=
  fun lens => d (LensIDCoreBridge.toCoreLensTag lens)

/-- Lift a legacy depth profile into the 100-lens space (0 on non-legacy tags). -/
def liftDepthToCoreLensTag (d : Depth) : GenericDepth CoreLensTag :=
  fun tag =>
    match LensIDCoreBridge.fromCoreLensTag? tag with
    | some lens => d lens
    | none => 0

end ProgramCalculus
end HeytingLean
