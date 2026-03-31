import HeytingLean.Hyperseries.Category.CanonicalizationBridge

namespace HeytingLean
namespace Hyperseries
namespace Category

open CategoryTheory

/--
Fiber of expressions that rewrite to a fixed target `n`.
This is the weak "normal-form fiber" used in the staged contractibility layer.
-/
def FiberTo (n a : HExpr) : Prop :=
  HRewriteSteps a n

theorem fiber_refl (n : HExpr) : FiberTo n n :=
  HRewriteSteps.refl n

/--
Any two terms in the same rewrite-to-`n` fiber are connected in the free groupoid.
-/
theorem fiber_connected {n a b : HExpr} (ha : FiberTo n a) (hb : FiberTo n b) :
    Nonempty (GObj a ⟶ GObj b) := by
  refine ⟨HRewriteSteps.toGroupoid ha ≫ inv (HRewriteSteps.toGroupoid hb)⟩

theorem fiber_to_center {n a : HExpr} (ha : FiberTo n a) :
    Nonempty (GObj a ⟶ GObj n) :=
  ⟨HRewriteSteps.toGroupoid ha⟩

theorem center_to_fiber {n a : HExpr} (ha : FiberTo n a) :
    Nonempty (GObj n ⟶ GObj a) :=
  ⟨inv (HRewriteSteps.toGroupoid ha)⟩

theorem eval_eq_of_fiber {K : Type*} [CommRing K] (M : HyperserialModel K)
    {n a b : HExpr} (ha : FiberTo n a) (hb : FiberTo n b) :
    HExpr.eval M a = HExpr.eval M b := by
  calc
    HExpr.eval M a = HExpr.eval M n := HRewriteSteps.eval_sound (M := M) ha
    _ = HExpr.eval M b := (HRewriteSteps.eval_sound (M := M) hb).symm

theorem normalizedConnected_of_fiber
    {K : Type*} [CommRing K] [HyperserialDescription K] (M : HyperserialModel K)
    {n a b : HExpr} (ha : FiberTo n a) (hb : FiberTo n b) :
    NormalizedConnected (M := M) a b := by
  unfold NormalizedConnected canonicalDesc
  apply congrArg (HyperserialDescription.describe (K := K))
  calc
    HExpr.eval M (nf a) = HExpr.eval M a := nf_sound (M := M) a
    _ = HExpr.eval M b := eval_eq_of_fiber (M := M) ha hb
    _ = HExpr.eval M (nf b) := (nf_sound (M := M) b).symm

theorem canonicalDesc_eq_of_fiber
    {K : Type*} [CommRing K] [HyperserialDescription K] (M : HyperserialModel K)
    {n a b : HExpr} (ha : FiberTo n a) (hb : FiberTo n b) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b := by
  unfold canonicalDesc
  exact congrArg (HyperserialDescription.describe (K := K)) (eval_eq_of_fiber (M := M) ha hb)

theorem quotient_eq_of_fiber
    {K : Type*} [CommRing K] [HyperserialDescription K] (M : HyperserialModel K)
    {n a b : HExpr} (ha : FiberTo n a) (hb : FiberTo n b) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  quotient_eq_of_normalizedConnected (M := M) (normalizedConnected_of_fiber (M := M) ha hb)

theorem canonicalDescClass_eq_of_fiber
    {K : Type*} [CommRing K] [HyperserialDescription K] (M : HyperserialModel K)
    {n a b : HExpr} (ha : FiberTo n a) (hb : FiberTo n b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  canonicalDescClass_eq_of_normalizedConnected (M := M)
    (normalizedConnected_of_fiber (M := M) ha hb)

/--
Uniqueness assumption for the staged normalizer over the fiber to `n`.
-/
def UniqueNFOnFiber (n : HExpr) : Prop :=
  ∀ {a : HExpr}, FiberTo n a → nf a = n

theorem normalizedConnected_of_uniqueNF
    {K : Type*} [CommRing K] [HyperserialDescription K] (M : HyperserialModel K)
    {n a b : HExpr} (huniq : UniqueNFOnFiber n)
    (ha : FiberTo n a) (hb : FiberTo n b) :
    NormalizedConnected (M := M) a b := by
  unfold NormalizedConnected
  rw [huniq ha, huniq hb]

theorem quotient_eq_of_uniqueNF
    {K : Type*} [CommRing K] [HyperserialDescription K] (M : HyperserialModel K)
    {n a b : HExpr} (huniq : UniqueNFOnFiber n)
    (ha : FiberTo n a) (hb : FiberTo n b) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  quotient_eq_of_normalizedConnected (M := M)
    (normalizedConnected_of_uniqueNF (M := M) huniq ha hb)

theorem canonicalDesc_eq_of_uniqueNF
    {K : Type*} [CommRing K] [HyperserialDescription K] (M : HyperserialModel K)
    {n a b : HExpr} (huniq : UniqueNFOnFiber n)
    (ha : FiberTo n a) (hb : FiberTo n b) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b := by
  apply (canonicalDesc_eq_iff_normalizedConnected (M := M) a b).2
  exact normalizedConnected_of_uniqueNF (M := M) huniq ha hb

theorem canonicalDesc_nf_eq_of_uniqueNF
    {K : Type*} [CommRing K] [HyperserialDescription K] (M : HyperserialModel K)
    {n a b : HExpr} (huniq : UniqueNFOnFiber n)
    (ha : FiberTo n a) (hb : FiberTo n b) :
    canonicalDesc (M := M) (nf a) = canonicalDesc (M := M) (nf b) := by
  simpa [NormalizedConnected] using
    (normalizedConnected_of_uniqueNF (M := M) huniq ha hb)

theorem canonicalDescClass_eq_of_uniqueNF
    {K : Type*} [CommRing K] [HyperserialDescription K] (M : HyperserialModel K)
    {n a b : HExpr} (huniq : UniqueNFOnFiber n)
    (ha : FiberTo n a) (hb : FiberTo n b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  canonicalDescClass_eq_of_normalizedConnected (M := M)
    (normalizedConnected_of_uniqueNF (M := M) huniq ha hb)

theorem canonicalDescClass_mk_eq_of_uniqueNF
    {K : Type*} [CommRing K] [HyperserialDescription K] (M : HyperserialModel K)
    {n a b : HExpr} (huniq : UniqueNFOnFiber n)
    (ha : FiberTo n a) (hb : FiberTo n b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  canonicalDescClass_eq_of_uniqueNF (M := M) huniq ha hb

end Category
end Hyperseries
end HeytingLean
