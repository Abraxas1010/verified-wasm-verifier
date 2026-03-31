import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Sets.Opens
import HeytingLean.GU.Base

/-!
# GU.Observerse (topological core)

GU’s “Observerse” is described (informally) as a map `ι : X → Y` embedding an “observer space” `X`
into a larger ambient space `Y`.  A robust, *formal* semantic handle for this in Lean is:

- treat propositions about a space as **opens** (`Opens X`),
- treat the observer map as inducing an inverse-image **frame hom**
  `Opens.comap : C(X, Y) → FrameHom (Opens Y) (Opens X)`,
- and (when `ι` is an embedding) treat `X` as **homeomorphic to the range** of `ι`,
  yielding a Bauer-style `FrameGeomEmbedding` between `Opens X` and `Opens (range ι)`.

This gives us an “observer-relative semantics” layer that is real mathlib code (no placeholders).
-/

namespace HeytingLean
namespace GU

open HeytingLean.LoF
open scoped Classical

universe u v

/-! ## Observerse as a topological embedding -/

structure Observerse (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] where
  /-- The observer map (bundled as a continuous map). -/
  ι : C(X, Y)
  /-- Topological embedding hypothesis for the observer map. -/
  isEmbedding : Topology.IsEmbedding ι

namespace Observerse

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The underlying function `X → Y`. -/
abbrev toFun (obs : Observerse X Y) : X → Y := fun x => obs.ι x

/-- Identity observer embedding. -/
def id (X : Type u) [TopologicalSpace X] : Observerse X X :=
  { ι := ContinuousMap.id X
    isEmbedding := Topology.IsEmbedding.id }

/-- Composition of observer embeddings. -/
def comp {Z : Type _} [TopologicalSpace Z] (obsXY : Observerse X Y) (obsYZ : Observerse Y Z) :
    Observerse X Z :=
  { ι := obsYZ.ι.comp obsXY.ι
    isEmbedding := obsYZ.isEmbedding.comp obsXY.isEmbedding }

/-- The induced inverse-image map on opens (a frame hom). -/
def opensComap (obs : Observerse X Y) :
    FrameHom (TopologicalSpace.Opens Y) (TopologicalSpace.Opens X) :=
  TopologicalSpace.Opens.comap obs.ι

@[simp] theorem toFun_id (X : Type u) [TopologicalSpace X] :
    (Observerse.id X).toFun = (fun x : X => x) := rfl

@[simp] theorem toFun_comp {Z : Type _} [TopologicalSpace Z]
    (obsXY : Observerse X Y) (obsYZ : Observerse Y Z) :
    (Observerse.comp obsXY obsYZ).toFun = fun x => obsYZ.toFun (obsXY.toFun x) := rfl

@[simp] theorem opensComap_id (X : Type u) [TopologicalSpace X] :
    (Observerse.id X).opensComap = FrameHom.id _ := by
  simp [Observerse.id, opensComap]

@[simp] theorem opensComap_comp {Z : Type _} [TopologicalSpace Z]
    (obsXY : Observerse X Y) (obsYZ : Observerse Y Z) :
    (Observerse.comp obsXY obsYZ).opensComap = obsXY.opensComap.comp obsYZ.opensComap := by
  rfl

/-- `X` is homeomorphic to the range of the embedding `ι`. -/
noncomputable def rangeHomeomorph (obs : Observerse X Y) : X ≃ₜ Set.range obs.toFun :=
  obs.isEmbedding.toHomeomorph

/-- The range of the observer map as a (subtype) space. -/
abbrev Range (obs : Observerse X Y) : Type v :=
  { y : Y // y ∈ Set.range obs.toFun }

instance (obs : Observerse X Y) : TopologicalSpace (obs.Range) := inferInstance

/-!
### Bauer-style frame embedding between `Opens X` and `Opens (range ι)`

Because `X ≃ₜ range(ι)`, the lattices of opens are order-isomorphic. We package the induced
`comap` maps as a `FrameGeomEmbedding` (encode ⊣ decode, with a round-trip law).
-/

noncomputable def opensRangeEmbedding (obs : Observerse X Y) :
    LoF.Bauer.FrameGeomEmbedding (A := TopologicalSpace.Opens obs.Range)
      (B := TopologicalSpace.Opens X) := by
  classical
  let h : X ≃ₜ obs.Range := (obs.rangeHomeomorph : X ≃ₜ Set.range obs.toFun)
  let f : C(X, obs.Range) := ⟨h, h.continuous⟩
  let g : C(obs.Range, X) := ⟨h.symm, h.continuous_symm⟩
  refine
    { encode := TopologicalSpace.Opens.comap f
      decode := TopologicalSpace.Opens.comap g
      gc := ?_
      round := ?_ }
  · intro U V
    -- Expand to set-theoretic preimage inclusion, then use the inverse laws.
    change (f ⁻¹' (U : Set obs.Range)) ⊆ (V : Set X) ↔ (U : Set obs.Range) ⊆ (g ⁻¹' (V : Set X))
    constructor
    · intro hUV x hxU
      have : g x ∈ (f ⁻¹' (U : Set obs.Range)) := by
        -- `f (g x) = x` as `f = h` and `g = h.symm`.
        simpa [f, g, ContinuousMap.coe_mk, h.apply_symm_apply x] using hxU
      exact hUV this
    · intro hUV x hx
      -- `hx` says `f x ∈ U`. By `hUV`, we get `g (f x) ∈ V`, and `g (f x) = x`.
      have hxV : g (f x) ∈ (V : Set X) := hUV hx
      simpa [f, g, ContinuousMap.coe_mk, h.symm_apply_apply x] using hxV
  · intro U
    -- `decode (encode U) = U` since `f ∘ g = id`.
    ext x
    change x ∈ TopologicalSpace.Opens.comap g (TopologicalSpace.Opens.comap f U) ↔ x ∈ U
    -- both sides are definitional preimages; rewrite with `f (g x) = x`.
    simp [TopologicalSpace.Opens.comap, f, g, ContinuousMap.coe_mk, h.apply_symm_apply x]

end Observerse

end GU
end HeytingLean
