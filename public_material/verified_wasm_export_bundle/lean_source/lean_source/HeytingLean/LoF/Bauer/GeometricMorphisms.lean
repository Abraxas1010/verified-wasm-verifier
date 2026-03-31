import Mathlib.Order.Closure
import Mathlib.Order.Hom.CompleteLattice
import HeytingLean.LoF.ComparisonNucleus

/-!
# Bauer: lens transports as geometric morphisms (frame-level)

This file makes the “geometric morphism” viewpoint explicit **at the level of truth values**:

* a lens-style **encode** is packaged as a `FrameHom` (preserving finite meets and arbitrary joins),
* a **decode** is recorded as its right adjoint (a `GaloisConnection`),
* the comparison nucleus transport `HeytingLean.LoF.Comparison.enc/dec` instantiates this interface.

The key technical bridge is that the comparison core `ΩR` is definitionaly the fixed-point type of the
closure operator induced by the composite `R := g ∘ f`.
-/

namespace HeytingLean
namespace LoF
namespace Bauer

open scoped Classical

universe u v

/-- A frame-level “geometric embedding”: an inverse-image map on truth values (`FrameHom`)
with a specified right adjoint and a round-trip law. -/
structure FrameGeomEmbedding (A : Type u) (B : Type v)
    [CompleteLattice A] [CompleteLattice B] where
  /-- Intended inverse-image map on truth values. -/
  encode : FrameHom A B
  /-- Right adjoint to `encode` (direct image on truth values). -/
  decode : B → A
  /-- Adjunction data: `encode ⊣ decode`. -/
  gc : GaloisConnection encode decode
  /-- Geometric embedding (“round-trip 1”): decode after encode is the identity. -/
  round : ∀ a : A, decode (encode a) = a

end Bauer
end LoF
end HeytingLean

namespace HeytingLean
namespace LoF
namespace Comparison

open scoped Classical

universe u v

variable {L : Type u} {Ω : Type v}
variable [CompleteLattice L] [CompleteLattice Ω]

/-! ## Closure operator and complete lattice structure on `ΩR` -/

/-- The closure operator induced by the comparison composite `R := g ∘ f`.

This exists for any `CompSpec` (no meet-preservation needed). -/
noncomputable def actClosure (S : CompSpec L Ω) : ClosureOperator L :=
  ClosureOperator.mk' (act S) (act_monotone (S := S)) (act_le (S := S)) (act_idem_le (S := S))

@[simp] lemma actClosure_apply (S : CompSpec L Ω) (x : L) :
    actClosure (S := S) x = act S x := rfl

/-- `ΩR` inherits a complete lattice structure as the closed elements of `actClosure`. -/
noncomputable instance instCompleteLatticeΩR (S : CompSpec L Ω) : CompleteLattice (ΩR S) := by
  classical
  change CompleteLattice ((actClosure (S := S)).Closeds)
  exact (ClosureOperator.gi (actClosure (S := S))).liftCompleteLattice

/-! ## Encode/decode as an adjunction -/

/-- The restricted comparison encode/decode maps form a Galois connection. -/
lemma gc_enc_dec (S : CompSpec L Ω) : GaloisConnection (enc S) (dec S) := by
  intro a u
  change S.f a.val ≤ u ↔ a.val ≤ (dec S u).val
  simpa [enc, dec] using (S.gc a.val u)

/-! ## `enc` as a `FrameHom` (inverse image) -/

/-- Under the usual “geometric” hypotheses (finite meets + top), `enc` is a `FrameHom`. -/
noncomputable def encFrameHom (S : StrongHyp L Ω) (htop : S.f ⊤ = (⊤ : Ω)) :
    FrameHom (ΩR (S : CompSpec L Ω)) Ω := by
  classical
  refine
    { toFun := enc (S := (S : CompSpec L Ω))
      map_inf' := ?_
      map_top' := ?_
      map_sSup' := ?_ }
  · intro a b
    -- inf in `ΩR` is definitionaly the inf of underlying values.
    simpa [enc] using (S.map_inf a.val b.val)
  · simpa [enc] using htop
  · intro s
    have h := (gc_enc_dec (S := (S : CompSpec L Ω))).l_sSup (s := s)
    simpa [sSup_image] using h

/-! ## Packaging as a Bauer `FrameGeomEmbedding` -/

/-- The comparison transport induces a Bauer-style frame-level geometric embedding. -/
noncomputable def comparisonGeomEmbedding (S : StrongHyp L Ω) (htop : S.f ⊤ = (⊤ : Ω)) :
    HeytingLean.LoF.Bauer.FrameGeomEmbedding (A := ΩR (S : CompSpec L Ω)) (B := Ω) where
  encode := encFrameHom (S := S) htop
  decode := dec (S := (S : CompSpec L Ω))
  gc := by
    -- `encFrameHom` is definitionally `enc`, so we reuse `gc_enc_dec`.
    simpa [encFrameHom] using gc_enc_dec (S := (S : CompSpec L Ω))
  round := by
    intro a
    -- `RT1` is stated as a function equality; specialize it at `a`.
    have h := RT1 (S := (S : CompSpec L Ω))
    simpa using congrArg (fun f => f a) h

end Comparison
end LoF
end HeytingLean
