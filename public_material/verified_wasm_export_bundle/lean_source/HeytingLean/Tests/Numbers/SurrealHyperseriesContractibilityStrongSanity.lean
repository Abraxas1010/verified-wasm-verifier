import HeytingLean.Hyperseries.Category.ContractibilityStrong

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Hyperseries
open HeytingLean.Hyperseries.Category
open CategoryTheory

noncomputable section

local instance instHyperserialDescriptionIntStrong : HyperserialDescription Int :=
  HyperserialDescription.idDescription Int

example (M : HyperserialModel Int) :
    RewriteComplete (M := M) ↔
      (∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → HRewriteSteps a b) := by
  rfl

example (M : HyperserialModel Int) (hcomplete : RewriteComplete (M := M))
    {a b : HExpr} (h : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    Nonempty (GObj a ⟶ GObj b) :=
  connected_of_canonicalDesc_eq (M := M) hcomplete h

example (M : HyperserialModel Int) (hcomplete : RewriteComplete (M := M))
    (a b : HExpr) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b ↔ Nonempty (GObj a ⟶ GObj b) := by
  simpa using canonicalDesc_eq_iff_connected (M := M) hcomplete a b

example (M : HyperserialModel Int) (hcomplete : RewriteComplete (M := M))
    {a b : HExpr} (h : Nonempty (GObj a ⟶ GObj b)) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b :=
  canonicalDesc_eq_of_connected (M := M) hcomplete h

example (M : HyperserialModel Int) (hcomplete : RewriteComplete (M := M))
    (d : HDesc Int) (x y : CanonicalFiber (M := M) d) :
    Nonempty (GObj x.1 ⟶ GObj y.1) :=
  canonicalFiber_connected (M := M) hcomplete x y

example (M : HyperserialModel Int) (hcomplete : RewriteComplete (M := M))
    (d : HDesc Int) (c : CanonicalFiber (M := M) d) :
    ∀ x : CanonicalFiber (M := M) d, Nonempty (GObj x.1 ⟶ GObj c.1) :=
  canonicalFiber_contractible_at (M := M) hcomplete c

example (M : HyperserialModel Int) (hcomplete : RewriteComplete (M := M))
    {a b : HExpr} (h : NormalizedConnected (M := M) a b) :
    Nonempty (GObj (nf a) ⟶ GObj (nf b)) :=
  normalizedConnected_implies_connected_nf (M := M) hcomplete h

example (M : HyperserialModel Int) (hcomplete : RewriteComplete (M := M))
    (a b : HExpr) :
    NormalizedConnected (M := M) a b ↔ Nonempty (GObj (nf a) ⟶ GObj (nf b)) := by
  simpa using normalizedConnected_iff_connected_nf (M := M) hcomplete a b

example (M : HyperserialModel Int) (hcomplete : RewriteComplete (M := M))
    (a b : HExpr) :
    canonicalDesc (M := M) (nf a) = canonicalDesc (M := M) (nf b) ↔
      Nonempty (GObj (nf a) ⟶ GObj (nf b)) := by
  simpa using canonicalDesc_nf_eq_iff_connected_nf (M := M) hcomplete a b

example (M : HyperserialModel Int) (hcomplete : RewriteComplete (M := M))
    {a b : HExpr}
    (h : canonicalDesc (M := M) (nf a) = canonicalDesc (M := M) (nf b)) :
    Nonempty (GObj (nf a) ⟶ GObj (nf b)) :=
  connected_nf_of_canonicalDesc_nf_eq (M := M) hcomplete h

example (M : HyperserialModel Int) (hcomplete : RewriteComplete (M := M))
    {a b : HExpr}
    (h : Nonempty (GObj (nf a) ⟶ GObj (nf b))) :
    canonicalDesc (M := M) (nf a) = canonicalDesc (M := M) (nf b) :=
  canonicalDesc_nf_eq_of_connected_nf (M := M) hcomplete h

example (M : HyperserialModel Int) (hcomplete : RewriteComplete (M := M))
    (a b : HExpr) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      Nonempty (GObj (nf a) ⟶ GObj (nf b)) := by
  simpa using canonicalDescClass_mk_eq_iff_connected_nf (M := M) hcomplete a b

example (M : HyperserialModel Int) (hcomplete : RewriteComplete (M := M))
    (a b : HExpr) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      Nonempty (GObj a ⟶ GObj b) := by
  simpa using canonicalDescClass_mk_eq_iff_connected (M := M) hcomplete a b

example (M : HyperserialModel Int) (hcomplete : RewriteComplete (M := M))
    {a b : HExpr}
    (h : canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) :
    Nonempty (GObj (nf a) ⟶ GObj (nf b)) :=
  connected_nf_of_canonicalDescClass_mk_eq (M := M) hcomplete h

example (M : HyperserialModel Int) (hcomplete : RewriteComplete (M := M))
    {a b : HExpr}
    (h : canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) :
    Nonempty (GObj a ⟶ GObj b) :=
  connected_of_canonicalDescClass_mk_eq (M := M) hcomplete h

example (M : HyperserialModel Int) (hcomplete : RewriteComplete (M := M))
    {a b : HExpr}
    (h : Nonempty (GObj (nf a) ⟶ GObj (nf b))) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  canonicalDescClass_mk_eq_of_connected_nf (M := M) hcomplete h

example (M : HyperserialModel Int) (hcomplete : RewriteComplete (M := M))
    {a b : HExpr}
    (h : Nonempty (GObj a ⟶ GObj b)) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  quotient_eq_of_connected (M := M) hcomplete h

example (M : HyperserialModel Int) (hcomplete : RewriteComplete (M := M))
    {a b : HExpr}
    (h : (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :
    Nonempty (GObj a ⟶ GObj b) :=
  connected_of_quotient_eq (M := M) hcomplete h

example (M : HyperserialModel Int) (hcomplete : RewriteComplete (M := M))
    (a b : HExpr) :
    ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) ↔
      Nonempty (GObj a ⟶ GObj b) := by
  simpa using quotient_eq_iff_connected (M := M) hcomplete a b

example (M : HyperserialModel Int) (a b : HExpr) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) := by
  simpa using canonicalDescClass_mk_eq_iff_quotient_eq (M := M) a b

example (M : HyperserialModel Int) (hcomplete : RewriteComplete (M := M))
    {a b : HExpr}
    (h : (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b :=
  canonicalDesc_eq_of_quotient_eq_of_rewriteComplete (M := M) hcomplete h

example (M : HyperserialModel Int) (hcomplete : RewriteComplete (M := M))
    {a b : HExpr}
    (h : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  quotient_eq_of_canonicalDesc_eq_of_rewriteComplete (M := M) hcomplete h

example (M : HyperserialModel Int) (hcomplete : RewriteComplete (M := M))
    (a b : HExpr) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b ↔
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) := by
  simpa using canonicalDesc_eq_iff_quotient_eq_of_rewriteComplete (M := M) hcomplete a b

example {n a b : HExpr} (ha : FiberTo n a) (hb : FiberTo n b) :
    Nonempty (GObj a ⟶ GObj b) :=
  connected_of_shared_fiber ha hb

example {n a b : HExpr} (ha : FiberTo n a) (hb : FiberTo n b) :
    Nonempty (GObj (nf a) ⟶ GObj (nf b)) :=
  connected_nf_of_shared_fiber ha hb

example (M : HyperserialModel Int) {n a b : HExpr} (ha : FiberTo n a) (hb : FiberTo n b) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b :=
  canonicalDesc_eq_of_shared_fiber (M := M) ha hb

example (M : HyperserialModel Int) {n a b : HExpr} (ha : FiberTo n a) (hb : FiberTo n b) :
    canonicalDesc (M := M) (nf a) = canonicalDesc (M := M) (nf b) :=
  canonicalDesc_eq_nf_of_shared_fiber (M := M) ha hb

example (M : HyperserialModel Int) {n a b : HExpr} (ha : FiberTo n a) (hb : FiberTo n b) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  quotient_eq_of_shared_fiber (M := M) ha hb

example (M : HyperserialModel Int) {n a b : HExpr} (ha : FiberTo n a) (hb : FiberTo n b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  canonicalDescClass_mk_eq_of_shared_fiber (M := M) ha hb

example (M : HyperserialModel Int)
    (hcompleteν : RewriteCompleteFromValuation (M := M) (fun _ : HExpr => (0 : ℤ)))
    (a b : HExpr) :
    canonicalDesc (M := M) (nf a) = canonicalDesc (M := M) (nf b) ↔
      Nonempty (GObj (nf a) ⟶ GObj (nf b)) := by
  simpa using
    (canonicalDesc_nf_eq_iff_connected_nf_of_valuation
      (M := M) (ν := fun _ : HExpr => (0 : ℤ))
      (hν := by intro _ _ _; rfl) hcompleteν a b)

example (M : HyperserialModel Int)
    (hcompleteν : RewriteCompleteFromValuation (M := M) (fun _ : HExpr => (0 : ℤ)))
    {a b : HExpr}
    (h : canonicalDesc (M := M) (nf a) = canonicalDesc (M := M) (nf b)) :
    Nonempty (GObj (nf a) ⟶ GObj (nf b)) := by
  exact
    connected_nf_of_canonicalDesc_nf_eq_of_valuation
      (M := M) (ν := fun _ : HExpr => (0 : ℤ))
      (hν := by intro _ _ _; rfl) hcompleteν h

example (M : HyperserialModel Int)
    (hcompleteν : RewriteCompleteFromValuation (M := M) (fun _ : HExpr => (0 : ℤ)))
    {a b : HExpr}
    (h : Nonempty (GObj a ⟶ GObj b)) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)) := by
  exact
    quotient_eq_of_connected_of_valuation
      (M := M) (ν := fun _ : HExpr => (0 : ℤ))
      (hν := by intro _ _ _; rfl) hcompleteν h

example (M : HyperserialModel Int)
    (hcompleteν : RewriteCompleteFromValuation (M := M) (fun _ : HExpr => (0 : ℤ)))
    {a b : HExpr}
    (h : (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :
    Nonempty (GObj a ⟶ GObj b) := by
  exact
    connected_of_quotient_eq_of_valuation
      (M := M) (ν := fun _ : HExpr => (0 : ℤ))
      (hν := by intro _ _ _; rfl) hcompleteν h

example (M : HyperserialModel Int)
    (hcompleteν : RewriteCompleteFromValuation (M := M) (fun _ : HExpr => (0 : ℤ)))
    (a b : HExpr) :
    ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) ↔
      Nonempty (GObj a ⟶ GObj b) := by
  simpa using
    quotient_eq_iff_connected_of_valuation
      (M := M) (ν := fun _ : HExpr => (0 : ℤ))
      (hν := by intro _ _ _; rfl) hcompleteν a b

example (M : HyperserialModel Int)
    (hcompleteν : RewriteCompleteFromValuation (M := M) (fun _ : HExpr => (0 : ℤ)))
    (a b : HExpr) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) := by
  simpa using
    canonicalDescClass_mk_eq_iff_quotient_eq_of_valuation
      (M := M) (ν := fun _ : HExpr => (0 : ℤ))
      (by intro _ _ _; rfl) hcompleteν a b

example (M : HyperserialModel Int)
    (hcompleteν : RewriteCompleteFromValuation (M := M) (fun _ : HExpr => (0 : ℤ)))
    {a b : HExpr}
    (h : (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b := by
  exact
    canonicalDesc_eq_of_quotient_eq_of_valuation
      (M := M) (ν := fun _ : HExpr => (0 : ℤ))
      (hν := by intro _ _ _; rfl) hcompleteν h

example (M : HyperserialModel Int)
    (hcompleteν : RewriteCompleteFromValuation (M := M) (fun _ : HExpr => (0 : ℤ)))
    {a b : HExpr}
    (h : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)) := by
  exact
    quotient_eq_of_canonicalDesc_eq_of_valuation
      (M := M) (ν := fun _ : HExpr => (0 : ℤ))
      (hν := by intro _ _ _; rfl) hcompleteν h

example (M : HyperserialModel Int)
    (hcompleteν : RewriteCompleteFromValuation (M := M) (fun _ : HExpr => (0 : ℤ)))
    (a b : HExpr) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b ↔
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) := by
  simpa using
    canonicalDesc_eq_iff_quotient_eq_of_valuation
      (M := M) (ν := fun _ : HExpr => (0 : ℤ))
      (hν := by intro _ _ _; rfl) hcompleteν a b

example (M : HyperserialModel Int) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b) :
    (canonicalDesc (M := M) a = canonicalDesc (M := M) b ↔
      canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
        canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) ∧
    (canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)))) ∧
    (((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) ↔
      Nonempty (GObj a ⟶ GObj b)) := by
  exact canonicalDesc_class_quotient_connected_bundle_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx

example (M : HyperserialModel Int) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b)
    (h : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    Nonempty (GObj a ⟶ GObj b) ∧
      canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
        canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ∧
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) := by
  exact connected_class_quotient_of_canonicalDesc_eq_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx h

example (M : HyperserialModel Int) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b)
    (h : Nonempty (GObj a ⟶ GObj b) ∧
      canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
        canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)) := by
  exact quotient_eq_of_connected_class_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx h

example (M : HyperserialModel Int) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b ↔
      Nonempty (GObj a ⟶ GObj b) := by
  exact canonicalDesc_eq_iff_connected_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx

example (M : HyperserialModel Int) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b) :
    ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) ↔
      Nonempty (GObj a ⟶ GObj b) := by
  exact quotient_eq_iff_connected_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx

example (M : HyperserialModel Int) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) := by
  exact canonicalDescClass_mk_eq_iff_quotient_eq_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx

example (M : HyperserialModel Int) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      canonicalDesc (M := M) a = canonicalDesc (M := M) b := by
  exact canonicalDescClass_mk_eq_iff_canonicalDesc_eq_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx

example (M : HyperserialModel Int) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      Nonempty (GObj a ⟶ GObj b) := by
  exact canonicalDescClass_mk_eq_iff_connected_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx

example (M : HyperserialModel Int) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b) :
    ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) ↔
      Nonempty (GObj a ⟶ GObj b) ∧
        canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
          canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) := by
  exact quotient_eq_iff_connected_class_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx

example (M : HyperserialModel Int) (ν : HExpr → ℤ)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b)
    (hdesc : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    Nonempty (GObj a ⟶ GObj b) := by
  exact connected_of_canonicalDesc_eq_of_valuation_sameIndex_core
    (M := M) ν hcompleteν hidx hdesc

example (M : HyperserialModel Int) (ν : HExpr → ℤ)
    {a b : HExpr}
    (hidx : ν a = ν b)
    (hdesc : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)) := by
  exact quotient_eq_of_canonicalDesc_eq_of_valuation_sameIndex_core
    (M := M) ν hidx hdesc

example (M : HyperserialModel Int) (ν : HExpr → ℤ)
    {a b : HExpr}
    (hidx : ν a = ν b)
    (hdesc : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) := by
  exact canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_valuation_sameIndex_core
    (M := M) ν hidx hdesc

example (M : HyperserialModel Int) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} (hidx : ν a = ν b) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b ↔
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) := by
  exact canonicalDesc_eq_iff_quotient_eq_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx

end
end Numbers
end Tests
end HeytingLean
