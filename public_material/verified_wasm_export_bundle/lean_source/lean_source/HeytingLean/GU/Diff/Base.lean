import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Topology.Sets.Opens
import HeytingLean.LoF.Bauer.GeometricMorphisms

/-!
# GU.Diff.Base

Differential-geometric base layer for the GU scaffold.

This file intentionally follows Mathlib’s “standard block” conventions for manifolds:
we parameterize over model-with-corners data and require the relevant typeclass instances,
instead of inventing new foundational notions.

We keep the surface area small: definitions here should be *reusable* in later GU modules
without forcing a heavy physics-specific API.
-/

namespace HeytingLean
namespace GU
namespace Diff

open scoped Manifold
open scoped Classical

end Diff
end GU
end HeytingLean

