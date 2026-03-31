import HeytingLean.GU.Diff.Base
import HeytingLean.GU.Bundles
import Mathlib.Algebra.Exact
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# GU.Diff.Observerse

Smooth-manifold refinement of `HeytingLean.GU.Observerse`.

This is intentionally conservative: it provides *definitions* and small lemmas only.
Heavy differential-geometry theorems (Levi-Civita, curvature identities, Dirac operators, etc.)
are deferred to future phases once we decide the exact Mathlib API surface we want to commit to.
-/

namespace HeytingLean
namespace GU
namespace Diff

open scoped Manifold

universe u v uE uH uE' uH'

section

variable
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type uH'} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}

/-- Smooth observer embedding `ι : X → Y`. -/
structure Observerse (X : Type u) (Y : Type v)
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X] [IsManifold I 1 X]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ⊤ Y] [IsManifold I' 1 Y] where
  ι : X → Y
  smooth : ContMDiff I I' ⊤ ι
  isEmbedding : Topology.IsEmbedding ι

namespace Observerse

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X] [IsManifold I 1 X]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ⊤ Y] [IsManifold I' 1 Y]

variable (obs : Observerse (I := I) (I' := I') (H := H) (H' := H') X Y)

/-- `ι` as a bundled continuous map. -/
noncomputable def toContinuousMap : C(X, Y) :=
  ⟨obs.ι, obs.smooth.continuous⟩

/-- Induced inverse-image map on opens (a frame hom). -/
noncomputable def opensComap :
    FrameHom (TopologicalSpace.Opens Y) (TopologicalSpace.Opens X) :=
  TopologicalSpace.Opens.comap obs.toContinuousMap

/-- The range of the observer map as a subtype type. -/
abbrev Range : Type v :=
  Set.range obs.ι

instance : TopologicalSpace obs.Range := inferInstance

/-- `X` is homeomorphic to the range of the embedding `ι`. -/
noncomputable def rangeHomeomorph : X ≃ₜ obs.Range :=
  obs.isEmbedding.toHomeomorph

/-! ### Optional Riemannian constructions -/

section PseudoRiemannian

/-!
Mathlib’s `TangentSpace I x` is a non-reducible synonym for the model vector space `E`. This is
excellent for computation (it keeps the kernel happy), but it can occasionally make typeclass
search noisy in downstream code when we only want a “metric-on-fibers” interface.

For the GU scaffold we therefore expose a *model-space* API:
- tangent fibers are represented by the underlying model spaces `E` and `E'`;
- manifold derivatives are transported across the definitional equality `TangentSpace = E`.

This keeps the file compiling and still matches the intended semantics.
-/

variable (g : Y → E' →ₗ[ℝ] E' →ₗ[ℝ] ℝ)

/-- The manifold derivative of the observer map at `x`. -/
noncomputable def dι (x : X) : E →L[ℝ] E' := by
  classical
  -- `mfderiv` is defined on tangent spaces; we transport along `TangentSpace = E`.
  simpa [TangentSpace] using (mfderiv I I' obs.ι x)

/-!
We model a “metric” on `Y` as an externally provided bilinear form `g y` on each tangent space.
This avoids introducing any normed / inner-product structure on tangent spaces (Mathlib’s
`TangentSpace` is just the model vector space), while still supporting “orthogonal complement”
constructions.
-/

/-- Pullback bilinear form on `TX x` induced from `g (ι x)` on `TY (ι x)`. -/
noncomputable def pullbackForm (g : Y → E' →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (x : X) (u v : E) : ℝ :=
  g (obs.ι x) (obs.dι x u) (obs.dι x v)

/-- Tangent image subspace at `x`. -/
noncomputable def tangentImage (x : X) : Submodule ℝ E' :=
  LinearMap.range (obs.dι x).toLinearMap

theorem exact_dι_mkQ_tangentImage (x : X) :
    Function.Exact (obs.dι x).toLinearMap (Submodule.mkQ (obs.tangentImage x)) := by
  simpa [tangentImage] using
    (LinearMap.exact_map_mkQ_range (f := (obs.dι x).toLinearMap))

/-- Normal space at `x` as the `g (ι x)`-orthogonal complement of the tangent image. -/
noncomputable def normalSpace (g : Y → E' →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (x : X) : Submodule ℝ E' :=
  (obs.tangentImage x).orthogonalBilin (g (obs.ι x))

/-- Normal bundle over `X` induced by the observer embedding, as a GU `Bundle`. -/
noncomputable def normalBundle (g : Y → E' →ₗ[ℝ] E' →ₗ[ℝ] ℝ) : HeytingLean.GU.Bundle (X := X) :=
  { fiber := fun x => obs.normalSpace (g := g) x }

/-- A minimal “chimeric fiber” model: vertical (normal) directions in `Y` plus covectors on `X`. -/
abbrev chimericFiber (g : Y → E' →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (x : X) : Type _ :=
  (obs.normalSpace (g := g) x) ⊕ Module.Dual ℝ E

/-- A minimal “chimeric bundle” over `X` (fiberwise `V ⊕ H*` in GU language). -/
noncomputable def chimericBundle (g : Y → E' →ₗ[ℝ] E' →ₗ[ℝ] ℝ) : HeytingLean.GU.Bundle (X := X) :=
  { fiber := fun x => obs.chimericFiber (g := g) x }

end PseudoRiemannian

end Observerse

end

end Diff
end GU
end HeytingLean
