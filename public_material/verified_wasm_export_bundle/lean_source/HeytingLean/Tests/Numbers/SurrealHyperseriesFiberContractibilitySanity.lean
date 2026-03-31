import HeytingLean.Hyperseries.Category.FiberContractibility

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Hyperseries
open HeytingLean.Hyperseries.Category
open CategoryTheory

noncomputable section

local instance instHyperserialDescriptionIntFiber : HyperserialDescription Int :=
  HyperserialDescription.idDescription Int

example (n : HExpr) : FiberTo n n :=
  fiber_refl n

example (n a b : HExpr) (ha : FiberTo n a) (hb : FiberTo n b) :
    Nonempty (GObj a ⟶ GObj b) :=
  fiber_connected ha hb

example (n a : HExpr) (ha : FiberTo n a) :
    Nonempty (GObj a ⟶ GObj n) :=
  fiber_to_center ha

example (n a : HExpr) (ha : FiberTo n a) :
    Nonempty (GObj n ⟶ GObj a) :=
  center_to_fiber ha

example (M : HyperserialModel Int) (n a b : HExpr) (ha : FiberTo n a) (hb : FiberTo n b) :
    HExpr.eval M a = HExpr.eval M b :=
  eval_eq_of_fiber (M := M) ha hb

example (M : HyperserialModel Int) (n a b : HExpr) (ha : FiberTo n a) (hb : FiberTo n b) :
    NormalizedConnected (M := M) a b :=
  normalizedConnected_of_fiber (M := M) ha hb

example (M : HyperserialModel Int) (n a b : HExpr) (ha : FiberTo n a) (hb : FiberTo n b) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b :=
  canonicalDesc_eq_of_fiber (M := M) ha hb

example (M : HyperserialModel Int) (n a b : HExpr) (ha : FiberTo n a) (hb : FiberTo n b) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  quotient_eq_of_fiber (M := M) ha hb

example (M : HyperserialModel Int) (n a b : HExpr) (ha : FiberTo n a) (hb : FiberTo n b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  canonicalDescClass_eq_of_fiber (M := M) ha hb

example (M : HyperserialModel Int) (n a b : HExpr)
    (huniq : UniqueNFOnFiber n) (ha : FiberTo n a) (hb : FiberTo n b) :
    NormalizedConnected (M := M) a b :=
  normalizedConnected_of_uniqueNF (M := M) huniq ha hb

example (M : HyperserialModel Int) (n a b : HExpr)
    (huniq : UniqueNFOnFiber n) (ha : FiberTo n a) (hb : FiberTo n b) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  quotient_eq_of_uniqueNF (M := M) huniq ha hb

example (M : HyperserialModel Int) (n a b : HExpr)
    (huniq : UniqueNFOnFiber n) (ha : FiberTo n a) (hb : FiberTo n b) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b :=
  canonicalDesc_eq_of_uniqueNF (M := M) huniq ha hb

example (M : HyperserialModel Int) (n a b : HExpr)
    (huniq : UniqueNFOnFiber n) (ha : FiberTo n a) (hb : FiberTo n b) :
    canonicalDesc (M := M) (nf a) = canonicalDesc (M := M) (nf b) :=
  canonicalDesc_nf_eq_of_uniqueNF (M := M) huniq ha hb

example (M : HyperserialModel Int) (n a b : HExpr)
    (huniq : UniqueNFOnFiber n) (ha : FiberTo n a) (hb : FiberTo n b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  canonicalDescClass_eq_of_uniqueNF (M := M) huniq ha hb

example (M : HyperserialModel Int) (n a b : HExpr)
    (huniq : UniqueNFOnFiber n) (ha : FiberTo n a) (hb : FiberTo n b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  canonicalDescClass_mk_eq_of_uniqueNF (M := M) huniq ha hb

end
end Numbers
end Tests
end HeytingLean
