import HeytingLean.LoF.Nucleus
import HeytingLean.Topos.LTfromNucleus
import HeytingLean.LoF.Combinators.Topos.NucleusFunctor
import Mathlib.CategoryTheory.Topos.Classifier
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

namespace HeytingLean
namespace PerspectivalPlenum

open CategoryTheory

universe u v w

/--
A ratchet step upgrades nuclei in an idempotence-safe way.

This is the formal shell for second witnessing / re-re-entry:
- it must be extensive (`J ≤ step J`),
- monotone in the input nucleus, and
- idempotent as an operator on nuclei.

We avoid modeling re-re-entry as raw composition by default.
-/
structure RatchetStep (α : Type u) [Order.Frame α] where
  step : Nucleus α → Nucleus α
  extensive : ∀ J : Nucleus α, J ≤ step J
  monotone : Monotone step
  idempotent : ∀ J : Nucleus α, step (step J) = step J

namespace RatchetStep

variable {α : Type u} [Order.Frame α]

instance : CoeFun (RatchetStep α) (fun _ => Nucleus α → Nucleus α) where
  coe S := S.step

@[simp] lemma coe_step (S : RatchetStep α) : (S.step : Nucleus α → Nucleus α) = S := rfl

lemma le_step (S : RatchetStep α) (J : Nucleus α) : J ≤ S J :=
  S.extensive J

lemma mono (S : RatchetStep α) : Monotone S :=
  S.monotone

@[simp] lemma step_step (S : RatchetStep α) (J : Nucleus α) : S (S J) = S J :=
  S.idempotent J

end RatchetStep

/--
`ReentryLTBridge` is the interface-level direct connection between:
1. ontology-side re-entry nucleus dynamics (`LoF.Reentry`), and
2. category-side Lawvere-Tierney/local-operator closure.

The bridge is intentionally assumption-driven: it stores a truth-carrier order equivalence
and a compatibility law equating ontology closure with LT reclassification at `Ω`.
-/
structure ReentryLTBridge
    (Ωα : Type u) [HeytingLean.LoF.PrimaryAlgebra Ωα]
    (C : Type v) [Category.{w} C]
    [CategoryTheory.Limits.HasPullbacks C]
    [CategoryTheory.HasClassifier C] where
  R : HeytingLean.LoF.Reentry Ωα
  ltKit : HeytingLean.Topos.LTfromNucleus.LawvereTierneyKit (C := C)
  truthEquiv : Ωα ≃o Subobject (HeytingLean.Topos.LTfromNucleus.Omega (C := C))
  compat : ∀ p : Ωα,
    truthEquiv (R.nucleus p)
      = HeytingLean.Topos.LTfromNucleus.reclassify (C := C) ltKit.j (truthEquiv p)

namespace ReentryLTBridge

variable {Ωα : Type u} [HeytingLean.LoF.PrimaryAlgebra Ωα]
variable {C : Type v} [Category.{w} C]
variable [CategoryTheory.Limits.HasPullbacks C] [CategoryTheory.HasClassifier C]

/-- Local operator induced by the bridge's Lawvere-Tierney kit. -/
noncomputable def localOperator (B : ReentryLTBridge Ωα C) :
    HeytingLean.Topos.LocalOperator C :=
  HeytingLean.Topos.LTfromNucleus.ofLawvereTierneyKit (C := C) B.ltKit

/-- Closure-on-`Ω` view of the bridge-local-operator, used by compatibility theorems. -/
noncomputable def omegaClosure (B : ReentryLTBridge Ωα C) :
    ClosureOperator (Subobject (CategoryTheory.HasClassifier.Ω C)) :=
  HeytingLean.Topos.LTfromNucleus.closureAtOmega (C := C) (localOperator (C := C) B)

/-- Canonical packaging into the existing `FromReentrySpec` bridge scaffold. -/
noncomputable def toFromReentrySpec (B : ReentryLTBridge Ωα C) :
    HeytingLean.Topos.LTfromNucleus.FromReentrySpec Ωα C :=
  HeytingLean.Topos.LTfromNucleus.FromReentrySpec.build
    (Ωα := Ωα) (C := C) B.R (localOperator (C := C) B)

/-- The bridge compatibility law, restated under a theorem name for rewriting. -/
@[simp] theorem compat_apply (B : ReentryLTBridge Ωα C) (p : Ωα) :
    B.truthEquiv (B.R.nucleus p)
      = HeytingLean.Topos.LTfromNucleus.reclassify (C := C) B.ltKit.j (B.truthEquiv p) :=
  B.compat p

/-- Closedness for subobjects under the bridge-local-operator is exactly LT fixedness. -/
@[simp] theorem isClosed_iff_reclassify_eq
    (B : ReentryLTBridge Ωα C) {X : C} (S : Subobject X) :
    HeytingLean.Topos.LocalOperator.IsClosed
        (C := C) (localOperator (C := C) B) S
      ↔ HeytingLean.Topos.LTfromNucleus.reclassify (C := C) B.ltKit.j S = S := by
  simpa [localOperator]
    using (HeytingLean.Topos.LTfromNucleus.ofLawvereTierneyKit_isClosed_iff
      (C := C) B.ltKit (S := S))

/-- A bridge point is `R`-fixed iff its transported image is LT-reclassify-fixed. -/
@[simp] theorem reentry_fixed_iff_reclassify_fixed
    (B : ReentryLTBridge Ωα C) (p : Ωα) :
    B.R.nucleus p = p
      ↔ HeytingLean.Topos.LTfromNucleus.reclassify (C := C) B.ltKit.j (B.truthEquiv p)
          = B.truthEquiv p := by
  constructor
  · intro hp
    simpa [hp] using (B.compat p).symm
  · intro hfix
    apply B.truthEquiv.injective
    calc
      B.truthEquiv (B.R.nucleus p)
          = HeytingLean.Topos.LTfromNucleus.reclassify (C := C) B.ltKit.j (B.truthEquiv p) :=
            B.compat p
      _ = B.truthEquiv p := hfix

/-- `R`-fixed points correspond exactly to `IsClosed` points at the classifier object `Ω`. -/
@[simp] theorem reentry_fixed_iff_isClosed_omega
    (B : ReentryLTBridge Ωα C) (p : Ωα) :
    B.R.nucleus p = p
      ↔ HeytingLean.Topos.LocalOperator.IsClosed
          (C := C) (localOperator (C := C) B) (B.truthEquiv p) := by
  constructor
  · intro hfix
    exact (isClosed_iff_reclassify_eq (C := C) (B := B) (X := CategoryTheory.HasClassifier.Ω C)
      (S := B.truthEquiv p)).2 ((reentry_fixed_iff_reclassify_fixed (C := C) B p).1 hfix)
  · intro hClosed
    exact (reentry_fixed_iff_reclassify_fixed (C := C) B p).2
      ((isClosed_iff_reclassify_eq (C := C) (B := B) (X := CategoryTheory.HasClassifier.Ω C)
        (S := B.truthEquiv p)).1 hClosed)

/-- Forward transport corollary: `R`-fixed points map to `Ω`-closed subobjects. -/
theorem map_reentry_fixed_to_closed
    (B : ReentryLTBridge Ωα C) {p : Ωα} (hp : B.R.nucleus p = p) :
    HeytingLean.Topos.LocalOperator.IsClosed
      (C := C) (localOperator (C := C) B) (B.truthEquiv p) :=
  (reentry_fixed_iff_isClosed_omega (C := C) B p).1 hp

/-- Backward transport corollary: `Ω`-closed transported points are `R`-fixed. -/
theorem closed_to_reentry_fixed
    (B : ReentryLTBridge Ωα C) {p : Ωα}
    (hp : HeytingLean.Topos.LocalOperator.IsClosed
      (C := C) (localOperator (C := C) B) (B.truthEquiv p)) :
    B.R.nucleus p = p :=
  (reentry_fixed_iff_isClosed_omega (C := C) B p).2 hp

end ReentryLTBridge

end PerspectivalPlenum
end HeytingLean

universe u v w

namespace HeytingLean
namespace PerspectivalPlenum

open CategoryTheory

/--
Queue anchor theorem for `ontology_reentry_grothendieck_closure_20260219`:
re-entry fixed points coincide with fixed points of the Grothendieck sieve nucleus
once local-operator closedness is transported through `htransport`.
-/
theorem ontology_reentry_grothendieck_closure_20260219
    {Ωα : Type u} [HeytingLean.LoF.PrimaryAlgebra Ωα]
    {C : Type v} [CategoryTheory.Category.{w} C]
    [CategoryTheory.Limits.HasPullbacks C] [CategoryTheory.HasClassifier C]
    (B : ReentryLTBridge Ωα C)
    (J : CategoryTheory.GrothendieckTopology C)
    {X : C} (S : CategoryTheory.Sieve X) (p : Ωα)
    (htransport :
      HeytingLean.Topos.LocalOperator.IsClosed
        (C := C) (ReentryLTBridge.localOperator (C := C) B) (B.truthEquiv p)
        ↔ J.IsClosed S) :
    B.R.nucleus p = p ↔
      S ∈ HeytingLean.LoF.Combinators.Heyting.FixedPoints
        (HeytingLean.LoF.Combinators.Topos.sieveNucleus (C := C) J X) :=
  by
    calc
      B.R.nucleus p = p ↔
          HeytingLean.Topos.LocalOperator.IsClosed
            (C := C) (ReentryLTBridge.localOperator (C := C) B) (B.truthEquiv p) :=
        ReentryLTBridge.reentry_fixed_iff_isClosed_omega (C := C) (B := B) p
      _ ↔ J.IsClosed S := htransport
      _ ↔ S ∈ HeytingLean.LoF.Combinators.Heyting.FixedPoints
            (HeytingLean.LoF.Combinators.Topos.sieveNucleus (C := C) J X) :=
        (HeytingLean.LoF.Combinators.Topos.mem_fixedPoints_sieveNucleus_iff_isClosed
          (C := C) (J := J) (S := S)).symm

end PerspectivalPlenum
end HeytingLean
