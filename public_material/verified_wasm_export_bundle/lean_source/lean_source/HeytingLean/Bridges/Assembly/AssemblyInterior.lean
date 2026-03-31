import Mathlib.Logic.Relation
import Mathlib.Data.Set.Lattice
import HeytingLean.ATheory.AssemblySpace
import HeytingLean.Bridges.Assembly.AssemblyGraph
import HeytingLean.LoF.Instances
import HeytingLean.LoF.IntReentry
import HeytingLean.LoF.Lens.Rewriting

/-
# Assembly interior (Alexandroff opens)

This packages the canonical reachability-based "opens" operator on `Set G.V` as an
`IntReentry`, so it can be fed to `HeytingLean.Generative.IntNucleusKit`.

The operator is an Alexandroff-style interior: keep `t` only when every vertex
reachable *from* `t` lies in the target set.
-/

namespace HeytingLean
namespace Bridges
namespace Assembly

open HeytingLean.ATheory
open HeytingLean.LoF

universe u

namespace ASpace

variable {α : Type u} (G : ASpace α)

/-- Reverse the edge relation so we can reuse the generic `Rewriting.I` laws.

`Relation.ReflTransGen (step := stepRev G) u t` is equivalent to
`Relation.ReflTransGen G.E t u`.
-/
abbrev stepRev : G.V → G.V → Prop := fun u t => G.E t u

/-- Canonical Alexandroff-style interior ("opens") on `Set G.V`. -/
abbrev opens (U : Set G.V) : Set G.V :=
  HeytingLean.LoF.Lens.Rewriting.I (step := stepRev G) U

lemma opens_eq_ofASpace_toOpens (U : Set G.V) :
    opens G U = (ofASpace α G).toOpens U := by
  ext t
  simp [opens, HeytingLean.LoF.Lens.Rewriting.I, ofASpace, Relation.reflTransGen_swap]

lemma opens_subset (U : Set G.V) : opens G U ⊆ U := by
  intro t ht
  exact ht t (Relation.ReflTransGen.refl)

noncomputable def intNucleus : IntNucleus (Set G.V) where
  act := opens G
  monotone := by
    intro X Y hXY
    exact
      HeytingLean.LoF.Lens.Rewriting.I.monotone (step := stepRev G) (X := X) (Y := Y) hXY
  idempotent := by
    intro X
    simpa [opens] using
      (HeytingLean.LoF.Lens.Rewriting.I.idempotent (step := stepRev G) (X := X))
  apply_le := by
    intro X
    exact opens_subset G X
  map_inf := by
    intro X Y
    simpa [opens] using
      (HeytingLean.LoF.Lens.Rewriting.I.inf_preserving (step := stepRev G) (X := X) (Y := Y))

noncomputable def intReentry : IntReentry (Set G.V) where
  nucleus := intNucleus G

end ASpace

end Assembly
end Bridges
end HeytingLean
