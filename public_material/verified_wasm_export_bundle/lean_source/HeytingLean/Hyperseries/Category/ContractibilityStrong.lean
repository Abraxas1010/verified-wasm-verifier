import HeytingLean.Hyperseries.Category.CanonicalizationBridge
import HeytingLean.Hyperseries.Category.FiberContractibility

namespace HeytingLean
namespace Hyperseries
namespace Category

open CategoryTheory

section

variable {K : Type*} [CommRing K] [HyperserialDescription K]

/--
Strong-stage completeness assumption:
semantic equality can be reflected back to a rewrite chain.
-/
def RewriteComplete (M : HyperserialModel K) : Prop :=
  ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → HRewriteSteps a b

/--
Valuation-guided completeness assumption:
semantic equality plus valuation agreement yields a rewrite chain.
-/
def RewriteCompleteFromValuation (M : HyperserialModel K) (ν : HExpr → ℤ) : Prop :=
  ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b → HRewriteSteps a b

omit [HyperserialDescription K] in
theorem rewriteComplete_of_valuation_bridge (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν) :
    RewriteComplete (M := M) := by
  intro a b hab
  exact hcompleteν hab (hν hab)

theorem eval_eq_of_canonicalDesc_eq (M : HyperserialModel K) {a b : HExpr}
    (h : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    HExpr.eval M a = HExpr.eval M b := by
  simpa [canonicalDesc] using
    congrArg (HyperserialDescription.realize (K := K)) h

/--
Under rewrite completeness, canonical-description equality yields
actual connectivity in the free rewrite groupoid.
-/
theorem connected_of_canonicalDesc_eq (M : HyperserialModel K)
    (hcomplete : RewriteComplete (M := M))
    {a b : HExpr} (h : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    Nonempty (GObj a ⟶ GObj b) := by
  refine ⟨HRewriteSteps.toGroupoid ?_⟩
  exact hcomplete (eval_eq_of_canonicalDesc_eq (M := M) h)

/--
Assumption-scoped strong equivalence between canonical descriptions
and groupoid connectivity.
-/
theorem canonicalDesc_eq_iff_connected (M : HyperserialModel K)
    (hcomplete : RewriteComplete (M := M))
    (a b : HExpr) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b ↔ Nonempty (GObj a ⟶ GObj b) := by
  constructor
  · intro h
    exact connected_of_canonicalDesc_eq (M := M) hcomplete h
  · intro h
    rcases h with ⟨f⟩
    exact groupoid_hom_implies_canonicalDesc_eq (M := M) f

theorem canonicalDesc_eq_of_connected (M : HyperserialModel K)
    (hcomplete : RewriteComplete (M := M))
    {a b : HExpr} (h : Nonempty (GObj a ⟶ GObj b)) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b :=
  (canonicalDesc_eq_iff_connected (M := M) hcomplete a b).2 h

/-- Fiber over a fixed canonical description representative. -/
def CanonicalFiber (M : HyperserialModel K) (d : HDesc K) : Type _ :=
  { e : HExpr // canonicalDesc (M := M) e = d }

theorem canonicalFiber_connected (M : HyperserialModel K) (hcomplete : RewriteComplete (M := M))
    {d : HDesc K}
    (x y : CanonicalFiber M d) :
    Nonempty (GObj x.1 ⟶ GObj y.1) := by
  apply connected_of_canonicalDesc_eq (M := M) hcomplete
  calc
    canonicalDesc (M := M) x.1 = d := x.2
    _ = canonicalDesc (M := M) y.1 := y.2.symm

/--
Contractibility-style center statement for each canonical fiber:
choosing any element as center connects all other fiber points to it.
-/
theorem canonicalFiber_contractible_at (M : HyperserialModel K)
    (hcomplete : RewriteComplete (M := M)) {d : HDesc K}
    (c : CanonicalFiber M d) :
    ∀ x : CanonicalFiber M d, Nonempty (GObj x.1 ⟶ GObj c.1) := by
  intro x
  exact canonicalFiber_connected (M := M) hcomplete x c

theorem canonicalFiber_connected_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {d : HDesc K}
    (x y : CanonicalFiber M d) :
    Nonempty (GObj x.1 ⟶ GObj y.1) := by
  have hdesc : canonicalDesc (M := M) x.1 = canonicalDesc (M := M) y.1 := by
    calc
      canonicalDesc (M := M) x.1 = d := x.2
      _ = canonicalDesc (M := M) y.1 := y.2.symm
  refine ⟨HRewriteSteps.toGroupoid ?_⟩
  exact hcompleteν (eval_eq_of_canonicalDesc_eq (M := M) hdesc)
    (hν (eval_eq_of_canonicalDesc_eq (M := M) hdesc))

theorem canonicalFiber_contractible_at_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {d : HDesc K}
    (c : CanonicalFiber M d) :
    ∀ x : CanonicalFiber M d, Nonempty (GObj x.1 ⟶ GObj c.1) := by
  intro x
  exact canonicalFiber_connected_of_valuation (M := M) ν hν hcompleteν x c

/-- Fiber over a fixed canonical description and an integer valuation index. -/
def CanonicalValuationFiber (M : HyperserialModel K) (ν : HExpr → ℤ)
    (d : HDesc K) (e : ℤ) : Type _ :=
  {x : HExpr // canonicalDesc (M := M) x = d ∧ ν x = e}

theorem canonicalDesc_eq_of_canonicalValuationFiber
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    {d : HDesc K} {e : ℤ}
    (x y : CanonicalValuationFiber M ν d e) :
    canonicalDesc (M := M) x.1 = canonicalDesc (M := M) y.1 := by
  calc
    canonicalDesc (M := M) x.1 = d := x.2.1
    _ = canonicalDesc (M := M) y.1 := y.2.1.symm

theorem valuation_eq_of_canonicalValuationFiber
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    {d : HDesc K} {e : ℤ}
    (x y : CanonicalValuationFiber M ν d e) :
    ν x.1 = ν y.1 := by
  calc
    ν x.1 = e := x.2.2
    _ = ν y.1 := y.2.2.symm

theorem eval_eq_of_canonicalValuationFiber
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    {d : HDesc K} {e : ℤ}
    (x y : CanonicalValuationFiber M ν d e) :
    HExpr.eval M x.1 = HExpr.eval M y.1 :=
  eval_eq_of_canonicalDesc_eq (M := M)
    (canonicalDesc_eq_of_canonicalValuationFiber (M := M) ν x y)

theorem canonicalValuationFiber_connected
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {d : HDesc K} {e : ℤ}
    (x y : CanonicalValuationFiber M ν d e) :
    Nonempty (GObj x.1 ⟶ GObj y.1) := by
  refine ⟨HRewriteSteps.toGroupoid ?_⟩
  exact hcompleteν
    (eval_eq_of_canonicalValuationFiber (M := M) ν x y)
    (valuation_eq_of_canonicalValuationFiber (M := M) ν x y)

theorem canonicalValuationFiber_contractible_at
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {d : HDesc K} {e : ℤ}
    (c : CanonicalValuationFiber M ν d e) :
    ∀ x : CanonicalValuationFiber M ν d e, Nonempty (GObj x.1 ⟶ GObj c.1) := by
  intro x
  exact canonicalValuationFiber_connected (M := M) ν hcompleteν x c

theorem normalizedConnected_of_canonicalValuationFiber
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    {d : HDesc K} {e : ℤ}
    (x y : CanonicalValuationFiber M ν d e) :
    NormalizedConnected (M := M) x.1 y.1 := by
  unfold NormalizedConnected
  exact congrArg (HyperserialDescription.describe (K := K))
    (eval_eq_of_canonicalValuationFiber (M := M) ν x y)

theorem quotient_eq_of_canonicalValuationFiber
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    {d : HDesc K} {e : ℤ}
    (x y : CanonicalValuationFiber M ν d e) :
    (Quot.mk _ x.1 : NormalizedQuotient (M := M)) =
      (Quot.mk _ y.1 : NormalizedQuotient (M := M)) :=
  quotient_eq_of_normalizedConnected (M := M)
    (normalizedConnected_of_canonicalValuationFiber (M := M) ν x y)

theorem canonicalDescClass_eq_of_canonicalValuationFiber
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    {d : HDesc K} {e : ℤ}
    (x y : CanonicalValuationFiber M ν d e) :
    canonicalDescClass (M := M) (Quot.mk _ x.1 : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ y.1 : NormalizedQuotient (M := M)) :=
  canonicalDescClass_mk_eq_of_quotient_eq (M := M)
    (quotient_eq_of_canonicalValuationFiber (M := M) ν x y)

theorem connected_of_canonicalDesc_eq_of_valuation_index
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ}
    (hdesc : canonicalDesc (M := M) a = canonicalDesc (M := M) b)
    (ha : ν a = e) (hb : ν b = e) :
    Nonempty (GObj a ⟶ GObj b) := by
  have hνeq : ν a = ν b := by
    calc
      ν a = e := ha
      _ = ν b := hb.symm
  exact canonicalValuationFiber_connected (M := M) ν hcompleteν
    (x := ⟨a, hdesc, hνeq⟩)
    (y := ⟨b, rfl, rfl⟩)

theorem quotient_eq_of_canonicalDesc_eq_of_valuation_index
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    {a b : HExpr} {e : ℤ}
    (hdesc : canonicalDesc (M := M) a = canonicalDesc (M := M) b)
    (ha : ν a = e) (hb : ν b = e) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) =
      (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  quotient_eq_of_canonicalValuationFiber (M := M) ν
    (x := ⟨a, hdesc, ha⟩) (y := ⟨b, rfl, hb⟩)

theorem canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_valuation_index
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    {a b : HExpr} {e : ℤ}
    (hdesc : canonicalDesc (M := M) a = canonicalDesc (M := M) b)
    (ha : ν a = e) (hb : ν b = e) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  canonicalDescClass_eq_of_canonicalValuationFiber (M := M) ν
    (x := ⟨a, hdesc, ha⟩) (y := ⟨b, rfl, hb⟩)

theorem normalizedConnected_implies_connected_nf
    (M : HyperserialModel K) (hcomplete : RewriteComplete (M := M)) {a b : HExpr}
    (h : NormalizedConnected (M := M) a b) :
    Nonempty (GObj (nf a) ⟶ GObj (nf b)) := by
  apply connected_of_canonicalDesc_eq (M := M) hcomplete
  simpa [NormalizedConnected] using h

theorem normalizedConnected_iff_connected_nf
    (M : HyperserialModel K) (hcomplete : RewriteComplete (M := M))
    (a b : HExpr) :
    NormalizedConnected (M := M) a b ↔ Nonempty (GObj (nf a) ⟶ GObj (nf b)) := by
  constructor
  · intro h
    exact normalizedConnected_implies_connected_nf (M := M) hcomplete h
  · intro h
    unfold NormalizedConnected
    exact canonicalDesc_eq_of_connected (M := M) hcomplete (a := nf a) (b := nf b) h

theorem canonicalDesc_nf_eq_iff_connected_nf
    (M : HyperserialModel K) (hcomplete : RewriteComplete (M := M))
    (a b : HExpr) :
    canonicalDesc (M := M) (nf a) = canonicalDesc (M := M) (nf b) ↔
      Nonempty (GObj (nf a) ⟶ GObj (nf b)) := by
  simpa [nf] using
    (canonicalDesc_eq_iff_connected (M := M) hcomplete (nf a) (nf b))

theorem connected_nf_of_canonicalDesc_nf_eq
    (M : HyperserialModel K) (hcomplete : RewriteComplete (M := M))
    {a b : HExpr}
    (h : canonicalDesc (M := M) (nf a) = canonicalDesc (M := M) (nf b)) :
    Nonempty (GObj (nf a) ⟶ GObj (nf b)) :=
  (canonicalDesc_nf_eq_iff_connected_nf (M := M) hcomplete a b).1 h

theorem canonicalDesc_nf_eq_of_connected_nf
    (M : HyperserialModel K) (hcomplete : RewriteComplete (M := M))
    {a b : HExpr}
    (h : Nonempty (GObj (nf a) ⟶ GObj (nf b))) :
    canonicalDesc (M := M) (nf a) = canonicalDesc (M := M) (nf b) :=
  (canonicalDesc_nf_eq_iff_connected_nf (M := M) hcomplete a b).2 h

omit [HyperserialDescription K] in
theorem connected_of_shared_fiber
    {n a b : HExpr} (ha : FiberTo n a) (hb : FiberTo n b) :
    Nonempty (GObj a ⟶ GObj b) :=
  fiber_connected ha hb

omit [HyperserialDescription K] in
theorem connected_nf_of_shared_fiber
    {n a b : HExpr} (ha : FiberTo n a) (hb : FiberTo n b) :
    Nonempty (GObj (nf a) ⟶ GObj (nf b)) := by
  simpa [nf] using (fiber_connected (n := n) ha hb)

theorem canonicalDesc_eq_of_shared_fiber
    (M : HyperserialModel K) {n a b : HExpr}
    (ha : FiberTo n a) (hb : FiberTo n b) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b := by
  rcases connected_of_shared_fiber (n := n) ha hb with ⟨f⟩
  exact groupoid_hom_implies_canonicalDesc_eq (M := M) f

theorem canonicalDesc_eq_nf_of_shared_fiber
    (M : HyperserialModel K) {n a b : HExpr}
    (ha : FiberTo n a) (hb : FiberTo n b) :
    canonicalDesc (M := M) (nf a) = canonicalDesc (M := M) (nf b) := by
  simpa [nf] using canonicalDesc_eq_of_shared_fiber (M := M) (n := n) ha hb

theorem quotient_eq_of_shared_fiber
    (M : HyperserialModel K) {n a b : HExpr}
    (ha : FiberTo n a) (hb : FiberTo n b) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  quotient_eq_of_fiber (M := M) ha hb

theorem canonicalDescClass_mk_eq_of_shared_fiber
    (M : HyperserialModel K) {n a b : HExpr}
    (ha : FiberTo n a) (hb : FiberTo n b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  canonicalDescClass_eq_of_fiber (M := M) ha hb

theorem canonicalDesc_eq_iff_connected_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    (a b : HExpr) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b ↔ Nonempty (GObj a ⟶ GObj b) := by
  apply canonicalDesc_eq_iff_connected (M := M)
  exact rewriteComplete_of_valuation_bridge (M := M) ν hν hcompleteν

theorem connected_of_canonicalDesc_eq_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    Nonempty (GObj a ⟶ GObj b) := by
  exact canonicalFiber_connected_of_valuation (M := M) ν hν hcompleteν
    (x := ⟨a, rfl⟩) (y := ⟨b, h.symm⟩)

theorem canonicalDesc_eq_of_connected_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : Nonempty (GObj a ⟶ GObj b)) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b :=
  (canonicalDesc_eq_iff_connected_of_valuation
    (M := M) ν hν hcompleteν a b).2 h

theorem canonicalDesc_nf_eq_iff_connected_nf_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    (a b : HExpr) :
    canonicalDesc (M := M) (nf a) = canonicalDesc (M := M) (nf b) ↔
      Nonempty (GObj (nf a) ⟶ GObj (nf b)) := by
  simpa [nf] using
    (canonicalDesc_eq_iff_connected_of_valuation
      (M := M) ν hν hcompleteν (nf a) (nf b))

theorem normalizedConnected_iff_connected_nf_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    (a b : HExpr) :
    NormalizedConnected (M := M) a b ↔ Nonempty (GObj (nf a) ⟶ GObj (nf b)) := by
  simpa [NormalizedConnected] using
    (canonicalDesc_nf_eq_iff_connected_nf_of_valuation
      (M := M) ν hν hcompleteν a b)

theorem canonicalDescClass_mk_eq_iff_connected_nf
    (M : HyperserialModel K) (hcomplete : RewriteComplete (M := M))
    (a b : HExpr) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      Nonempty (GObj (nf a) ⟶ GObj (nf b)) := by
  simpa [canonicalDescClass_mk] using
    (canonicalDesc_nf_eq_iff_connected_nf (M := M) hcomplete a b)

theorem canonicalDescClass_mk_eq_iff_normalizedConnected_of_rewriteComplete
    (M : HyperserialModel K) (hcomplete : RewriteComplete (M := M))
    (a b : HExpr) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      NormalizedConnected (M := M) a b := by
  constructor
  · intro h
    exact (normalizedConnected_iff_connected_nf (M := M) hcomplete a b).2
      ((canonicalDescClass_mk_eq_iff_connected_nf (M := M) hcomplete a b).1 h)
  · intro h
    exact (canonicalDescClass_mk_eq_iff_connected_nf (M := M) hcomplete a b).2
      ((normalizedConnected_iff_connected_nf (M := M) hcomplete a b).1 h)

theorem normalizedConnected_of_canonicalDescClass_mk_eq_of_rewriteComplete
    (M : HyperserialModel K) (hcomplete : RewriteComplete (M := M))
    {a b : HExpr}
    (h : canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) :
    NormalizedConnected (M := M) a b :=
  (canonicalDescClass_mk_eq_iff_normalizedConnected_of_rewriteComplete
    (M := M) hcomplete a b).1 h

theorem canonicalDescClass_mk_eq_of_normalizedConnected_of_rewriteComplete
    (M : HyperserialModel K) (hcomplete : RewriteComplete (M := M))
    {a b : HExpr}
    (h : NormalizedConnected (M := M) a b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  (canonicalDescClass_mk_eq_iff_normalizedConnected_of_rewriteComplete
    (M := M) hcomplete a b).2 h

theorem canonicalDescClass_mk_eq_iff_connected
    (M : HyperserialModel K) (hcomplete : RewriteComplete (M := M))
    (a b : HExpr) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      Nonempty (GObj a ⟶ GObj b) := by
  simpa [nf] using canonicalDescClass_mk_eq_iff_connected_nf (M := M) hcomplete a b

theorem connected_nf_of_canonicalDescClass_mk_eq
    (M : HyperserialModel K) (hcomplete : RewriteComplete (M := M))
    {a b : HExpr}
    (h : canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) :
    Nonempty (GObj (nf a) ⟶ GObj (nf b)) :=
  (canonicalDescClass_mk_eq_iff_connected_nf (M := M) hcomplete a b).1 h

theorem connected_of_canonicalDescClass_mk_eq
    (M : HyperserialModel K) (hcomplete : RewriteComplete (M := M))
    {a b : HExpr}
    (h : canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) :
    Nonempty (GObj a ⟶ GObj b) := by
  simpa [nf] using connected_nf_of_canonicalDescClass_mk_eq (M := M) hcomplete h

theorem canonicalDescClass_mk_eq_of_connected_nf
    (M : HyperserialModel K) (hcomplete : RewriteComplete (M := M))
    {a b : HExpr}
    (h : Nonempty (GObj (nf a) ⟶ GObj (nf b))) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  (canonicalDescClass_mk_eq_iff_connected_nf (M := M) hcomplete a b).2 h

theorem quotient_eq_of_connected
    (M : HyperserialModel K) (hcomplete : RewriteComplete (M := M))
    {a b : HExpr}
    (h : Nonempty (GObj a ⟶ GObj b)) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)) := by
  apply quotient_eq_of_canonicalDescClass_mk_eq (M := M)
  exact (canonicalDescClass_mk_eq_iff_connected (M := M) hcomplete a b).2 h

theorem connected_of_quotient_eq
    (M : HyperserialModel K) (hcomplete : RewriteComplete (M := M))
    {a b : HExpr}
    (h : (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :
    Nonempty (GObj a ⟶ GObj b) := by
  apply connected_of_canonicalDescClass_mk_eq (M := M) hcomplete
  exact canonicalDescClass_mk_eq_of_quotient_eq (M := M) h

theorem quotient_eq_iff_connected
    (M : HyperserialModel K) (hcomplete : RewriteComplete (M := M))
    (a b : HExpr) :
    ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) ↔
      Nonempty (GObj a ⟶ GObj b) := by
  constructor
  · exact connected_of_quotient_eq (M := M) hcomplete
  · exact quotient_eq_of_connected (M := M) hcomplete

theorem canonicalDescClass_mk_eq_iff_quotient_eq
    (M : HyperserialModel K) (a b : HExpr) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) := by
  constructor
  · exact quotient_eq_of_canonicalDescClass_mk_eq (M := M)
  · exact canonicalDescClass_mk_eq_of_quotient_eq (M := M)

theorem canonicalDesc_eq_of_quotient_eq_of_rewriteComplete
    (M : HyperserialModel K) (hcomplete : RewriteComplete (M := M))
    {a b : HExpr}
    (h : (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b :=
  canonicalDesc_eq_of_connected (M := M) hcomplete
    (connected_of_quotient_eq (M := M) hcomplete h)

theorem quotient_eq_of_canonicalDesc_eq_of_rewriteComplete
    (M : HyperserialModel K) (hcomplete : RewriteComplete (M := M))
    {a b : HExpr}
    (h : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  quotient_eq_of_connected (M := M) hcomplete
    (connected_of_canonicalDesc_eq (M := M) hcomplete h)

theorem canonicalDesc_eq_iff_quotient_eq_of_rewriteComplete
    (M : HyperserialModel K) (hcomplete : RewriteComplete (M := M))
    (a b : HExpr) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b ↔
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) := by
  constructor
  · exact quotient_eq_of_canonicalDesc_eq_of_rewriteComplete (M := M) hcomplete
  · exact canonicalDesc_eq_of_quotient_eq_of_rewriteComplete (M := M) hcomplete

theorem canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_rewriteComplete
    (M : HyperserialModel K) (hcomplete : RewriteComplete (M := M))
    {a b : HExpr}
    (h : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  canonicalDescClass_mk_eq_of_quotient_eq (M := M)
    (quotient_eq_of_canonicalDesc_eq_of_rewriteComplete (M := M) hcomplete h)

theorem canonicalDesc_eq_of_canonicalDescClass_mk_eq_of_rewriteComplete
    (M : HyperserialModel K) (hcomplete : RewriteComplete (M := M))
    {a b : HExpr}
    (h : canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b :=
  canonicalDesc_eq_of_quotient_eq_of_rewriteComplete (M := M) hcomplete
    (quotient_eq_of_canonicalDescClass_mk_eq (M := M) h)

theorem canonicalDescClass_mk_eq_iff_canonicalDesc_eq_of_rewriteComplete
    (M : HyperserialModel K) (hcomplete : RewriteComplete (M := M))
    (a b : HExpr) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      canonicalDesc (M := M) a = canonicalDesc (M := M) b := by
  constructor
  · exact canonicalDesc_eq_of_canonicalDescClass_mk_eq_of_rewriteComplete
      (M := M) hcomplete
  · exact canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_rewriteComplete
      (M := M) hcomplete

theorem canonicalDescClass_mk_eq_iff_connected_nf_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    (a b : HExpr) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      Nonempty (GObj (nf a) ⟶ GObj (nf b)) := by
  simpa [canonicalDescClass_mk] using
    (canonicalDesc_nf_eq_iff_connected_nf_of_valuation
      (M := M) ν hν hcompleteν a b)

theorem canonicalDescClass_mk_eq_iff_normalizedConnected_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    (a b : HExpr) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      NormalizedConnected (M := M) a b := by
  constructor
  · intro h
    exact (normalizedConnected_iff_connected_nf_of_valuation
      (M := M) ν hν hcompleteν a b).2
        ((canonicalDescClass_mk_eq_iff_connected_nf_of_valuation
          (M := M) ν hν hcompleteν a b).1 h)
  · intro h
    exact (canonicalDescClass_mk_eq_iff_connected_nf_of_valuation
      (M := M) ν hν hcompleteν a b).2
        ((normalizedConnected_iff_connected_nf_of_valuation
          (M := M) ν hν hcompleteν a b).1 h)

theorem normalizedConnected_of_canonicalDescClass_mk_eq_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) :
    NormalizedConnected (M := M) a b :=
  (canonicalDescClass_mk_eq_iff_normalizedConnected_of_valuation
    (M := M) ν hν hcompleteν a b).1 h

theorem canonicalDescClass_mk_eq_of_normalizedConnected_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : NormalizedConnected (M := M) a b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  (canonicalDescClass_mk_eq_iff_normalizedConnected_of_valuation
    (M := M) ν hν hcompleteν a b).2 h

theorem canonicalDescClass_mk_eq_iff_connected_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    (a b : HExpr) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      Nonempty (GObj a ⟶ GObj b) := by
  simpa [nf] using
    canonicalDescClass_mk_eq_iff_connected_nf_of_valuation
      (M := M) ν hν hcompleteν a b

theorem connected_nf_of_canonicalDescClass_mk_eq_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) :
    Nonempty (GObj (nf a) ⟶ GObj (nf b)) :=
  (canonicalDescClass_mk_eq_iff_connected_nf_of_valuation
    (M := M) ν hν hcompleteν a b).1 h

theorem connected_of_canonicalDescClass_mk_eq_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) :
    Nonempty (GObj a ⟶ GObj b) := by
  simpa [nf] using
    connected_nf_of_canonicalDescClass_mk_eq_of_valuation
      (M := M) ν hν hcompleteν h

theorem canonicalDescClass_mk_eq_of_connected_nf_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : Nonempty (GObj (nf a) ⟶ GObj (nf b))) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  (canonicalDescClass_mk_eq_iff_connected_nf_of_valuation
    (M := M) ν hν hcompleteν a b).2 h

theorem canonicalDescClass_mk_eq_of_connected_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : Nonempty (GObj a ⟶ GObj b)) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) := by
  simpa [nf] using
    canonicalDescClass_mk_eq_of_connected_nf_of_valuation
      (M := M) ν hν hcompleteν h

theorem quotient_eq_of_connected_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : Nonempty (GObj a ⟶ GObj b)) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)) := by
  apply quotient_eq_of_canonicalDescClass_mk_eq (M := M)
  exact canonicalDescClass_mk_eq_of_connected_of_valuation
    (M := M) ν hν hcompleteν h

theorem connected_of_quotient_eq_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :
    Nonempty (GObj a ⟶ GObj b) := by
  exact connected_of_canonicalDescClass_mk_eq_of_valuation
    (M := M) ν hν hcompleteν (canonicalDescClass_mk_eq_of_quotient_eq (M := M) h)

theorem quotient_eq_iff_connected_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    (a b : HExpr) :
    ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) ↔
      Nonempty (GObj a ⟶ GObj b) := by
  constructor
  · exact connected_of_quotient_eq_of_valuation (M := M) ν hν hcompleteν
  · exact quotient_eq_of_connected_of_valuation (M := M) ν hν hcompleteν

theorem canonicalDescClass_mk_eq_of_quotient_eq_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (_hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (_hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  canonicalDescClass_mk_eq_of_quotient_eq (M := M) h

theorem quotient_eq_of_canonicalDescClass_mk_eq_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (_hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (_hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  quotient_eq_of_canonicalDescClass_mk_eq (M := M) h

theorem canonicalDescClass_mk_eq_iff_quotient_eq_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (_hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (_hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    (a b : HExpr) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) := by
  exact canonicalDescClass_mk_eq_iff_quotient_eq (M := M) a b

theorem canonicalDesc_eq_of_quotient_eq_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b :=
  canonicalDesc_eq_of_connected_of_valuation (M := M) ν hν hcompleteν
    (connected_of_quotient_eq_of_valuation (M := M) ν hν hcompleteν h)

theorem quotient_eq_of_canonicalDesc_eq_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (_hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)) := by
  have hνeq : ν a = ν b := hν (eval_eq_of_canonicalDesc_eq (M := M) h)
  exact quotient_eq_of_canonicalDesc_eq_of_valuation_index
    (M := M) ν h rfl hνeq.symm

theorem canonicalDesc_eq_iff_quotient_eq_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    (a b : HExpr) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b ↔
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) := by
  constructor
  · exact quotient_eq_of_canonicalDesc_eq_of_valuation (M := M) ν hν hcompleteν
  · exact canonicalDesc_eq_of_quotient_eq_of_valuation (M := M) ν hν hcompleteν

theorem canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (_hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) := by
  have hνeq : ν a = ν b := hν (eval_eq_of_canonicalDesc_eq (M := M) h)
  exact canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_valuation_index
    (M := M) ν h rfl hνeq.symm

theorem canonicalDesc_eq_of_canonicalDescClass_mk_eq_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b :=
  canonicalDesc_eq_of_quotient_eq_of_valuation (M := M) ν hν hcompleteν
    (quotient_eq_of_canonicalDescClass_mk_eq_of_valuation (M := M) ν hν hcompleteν h)

theorem canonicalDescClass_mk_eq_iff_canonicalDesc_eq_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    (a b : HExpr) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      canonicalDesc (M := M) a = canonicalDesc (M := M) b := by
  constructor
  · exact canonicalDesc_eq_of_canonicalDescClass_mk_eq_of_valuation
      (M := M) ν hν hcompleteν
  · exact canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_valuation
      (M := M) ν hν hcompleteν

theorem canonicalDesc_eq_iff_connected_class_quotient_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    (a b : HExpr) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b ↔
      Nonempty (GObj a ⟶ GObj b) ∧
        canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
          canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ∧
        ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) := by
  constructor
  · intro hdesc
    refine ⟨?_, ?_, ?_⟩
    · exact (canonicalDesc_eq_iff_connected_of_valuation
        (M := M) ν hν hcompleteν a b).1 hdesc
    · exact (canonicalDescClass_mk_eq_iff_canonicalDesc_eq_of_valuation
        (M := M) ν hν hcompleteν a b).2 hdesc
    · exact (canonicalDesc_eq_iff_quotient_eq_of_valuation
        (M := M) ν hν hcompleteν a b).1 hdesc
  · intro hall
    exact (canonicalDesc_eq_iff_connected_of_valuation
      (M := M) ν hν hcompleteν a b).2 hall.1

theorem canonicalDescClass_mk_eq_iff_connected_quotient_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    (a b : HExpr) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      Nonempty (GObj a ⟶ GObj b) ∧
        ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) := by
  constructor
  · intro hclass
    refine ⟨?_, ?_⟩
    · exact (canonicalDescClass_mk_eq_iff_connected_of_valuation
        (M := M) ν hν hcompleteν a b).1 hclass
    · exact (canonicalDescClass_mk_eq_iff_quotient_eq_of_valuation
        (M := M) ν hν hcompleteν a b).1 hclass
  · intro h
    exact (canonicalDescClass_mk_eq_iff_quotient_eq_of_valuation
      (M := M) ν hν hcompleteν a b).2 h.2

theorem quotient_eq_iff_connected_class_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    (a b : HExpr) :
    ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) ↔
      Nonempty (GObj a ⟶ GObj b) ∧
        canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
          canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) := by
  constructor
  · intro hq
    refine ⟨?_, ?_⟩
    · exact (quotient_eq_iff_connected_of_valuation
        (M := M) ν hν hcompleteν a b).1 hq
    · exact (canonicalDescClass_mk_eq_iff_quotient_eq_of_valuation
        (M := M) ν hν hcompleteν a b).2 hq
  · intro h
    exact (quotient_eq_iff_connected_of_valuation
      (M := M) ν hν hcompleteν a b).2 h.1

theorem canonicalDesc_class_quotient_connected_bundle_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    (a b : HExpr) :
    (canonicalDesc (M := M) a = canonicalDesc (M := M) b ↔
      canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
        canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) ∧
    (canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)))) ∧
    (((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) ↔
      Nonempty (GObj a ⟶ GObj b)) := by
  refine ⟨?_, ?_⟩
  · exact canonicalDescClass_mk_eq_iff_canonicalDesc_eq_of_valuation
      (M := M) ν hν hcompleteν a b |>.symm
  · refine ⟨?_, ?_⟩
    · exact canonicalDescClass_mk_eq_iff_quotient_eq_of_valuation
        (M := M) ν hν hcompleteν a b
    · exact quotient_eq_iff_connected_of_valuation
        (M := M) ν hν hcompleteν a b

theorem connected_class_quotient_of_canonicalDesc_eq_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    Nonempty (GObj a ⟶ GObj b) ∧
      canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
        canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ∧
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :=
  (canonicalDesc_eq_iff_connected_class_quotient_of_valuation
    (M := M) ν hν hcompleteν a b).1 h

theorem canonicalDesc_eq_of_connected_class_quotient_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : Nonempty (GObj a ⟶ GObj b) ∧
      canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
        canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ∧
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)))) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b :=
  (canonicalDesc_eq_iff_connected_class_quotient_of_valuation
    (M := M) ν hν hcompleteν a b).2 h

theorem connected_quotient_of_canonicalDescClass_mk_eq_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) :
    Nonempty (GObj a ⟶ GObj b) ∧
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :=
  (canonicalDescClass_mk_eq_iff_connected_quotient_of_valuation
    (M := M) ν hν hcompleteν a b).1 h

theorem canonicalDescClass_mk_eq_of_connected_quotient_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : Nonempty (GObj a ⟶ GObj b) ∧
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)))) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  (canonicalDescClass_mk_eq_iff_connected_quotient_of_valuation
    (M := M) ν hν hcompleteν a b).2 h

theorem connected_class_of_quotient_eq_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :
    Nonempty (GObj a ⟶ GObj b) ∧
      canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
        canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  (quotient_eq_iff_connected_class_of_valuation
    (M := M) ν hν hcompleteν a b).1 h

theorem quotient_eq_of_connected_class_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : Nonempty (GObj a ⟶ GObj b) ∧
      canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
        canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  (quotient_eq_iff_connected_class_of_valuation
    (M := M) ν hν hcompleteν a b).2 h

theorem canonicalDesc_eq_iff_connected_of_valuation_index
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ}
    (ha : ν a = e) (hb : ν b = e) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b ↔
      Nonempty (GObj a ⟶ GObj b) := by
  constructor
  · intro hdesc
    exact connected_of_canonicalDesc_eq_of_valuation_index
      (M := M) ν hcompleteν hdesc ha hb
  · intro hconn
    exact canonicalDesc_eq_of_connected_of_valuation
      (M := M) ν hν hcompleteν hconn

theorem canonicalDesc_eq_of_connected_of_valuation_index
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ}
    (ha : ν a = e) (hb : ν b = e)
    (h : Nonempty (GObj a ⟶ GObj b)) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b :=
  (canonicalDesc_eq_iff_connected_of_valuation_index
    (M := M) ν hν hcompleteν ha hb).2 h

theorem canonicalDescClass_mk_eq_iff_canonicalDesc_eq_of_valuation_index
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ}
    (ha : ν a = e) (hb : ν b = e) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      canonicalDesc (M := M) a = canonicalDesc (M := M) b := by
  constructor
  · intro hclass
    exact canonicalDesc_eq_of_canonicalDescClass_mk_eq_of_valuation
      (M := M) ν hν hcompleteν hclass
  · intro hdesc
    exact canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_valuation_index
      (M := M) ν hdesc ha hb

theorem canonicalDesc_eq_of_canonicalDescClass_mk_eq_of_valuation_index
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ}
    (ha : ν a = e) (hb : ν b = e)
    (h : canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b :=
  (canonicalDescClass_mk_eq_iff_canonicalDesc_eq_of_valuation_index
    (M := M) ν hν hcompleteν ha hb).1 h

theorem quotient_eq_iff_connected_of_valuation_index
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ}
    (_ha : ν a = e) (_hb : ν b = e) :
    ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) ↔
      Nonempty (GObj a ⟶ GObj b) := by
  constructor
  · intro hq
    exact connected_of_quotient_eq_of_valuation (M := M) ν hν hcompleteν hq
  · intro hconn
    exact quotient_eq_of_connected_of_valuation (M := M) ν hν hcompleteν hconn

theorem connected_of_quotient_eq_of_valuation_index
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ}
    (ha : ν a = e) (hb : ν b = e)
    (h : (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :
    Nonempty (GObj a ⟶ GObj b) :=
  (quotient_eq_iff_connected_of_valuation_index
    (M := M) ν hν hcompleteν ha hb).1 h

theorem quotient_eq_of_connected_of_valuation_index
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ}
    (ha : ν a = e) (hb : ν b = e)
    (h : Nonempty (GObj a ⟶ GObj b)) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  (quotient_eq_iff_connected_of_valuation_index
    (M := M) ν hν hcompleteν ha hb).2 h

theorem canonicalDescClass_mk_eq_iff_connected_of_valuation_index
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ}
    (_ha : ν a = e) (_hb : ν b = e) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      Nonempty (GObj a ⟶ GObj b) := by
  constructor
  · intro hclass
    exact connected_of_canonicalDescClass_mk_eq_of_valuation (M := M) ν hν hcompleteν hclass
  · intro hconn
    exact canonicalDescClass_mk_eq_of_connected_of_valuation (M := M) ν hν hcompleteν hconn

theorem connected_of_canonicalDescClass_mk_eq_of_valuation_index
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ}
    (ha : ν a = e) (hb : ν b = e)
    (h : canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) :
    Nonempty (GObj a ⟶ GObj b) :=
  (canonicalDescClass_mk_eq_iff_connected_of_valuation_index
    (M := M) ν hν hcompleteν ha hb).1 h

theorem canonicalDescClass_mk_eq_of_connected_of_valuation_index
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ}
    (ha : ν a = e) (hb : ν b = e)
    (h : Nonempty (GObj a ⟶ GObj b)) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  (canonicalDescClass_mk_eq_iff_connected_of_valuation_index
    (M := M) ν hν hcompleteν ha hb).2 h

theorem canonicalDesc_eq_iff_quotient_eq_of_valuation_index
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ}
    (_ha : ν a = e) (_hb : ν b = e) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b ↔
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) := by
  constructor
  · intro hdesc
    exact quotient_eq_of_canonicalDesc_eq_of_valuation (M := M) ν hν hcompleteν hdesc
  · intro hq
    exact canonicalDesc_eq_of_quotient_eq_of_valuation (M := M) ν hν hcompleteν hq

theorem canonicalDesc_eq_of_quotient_eq_of_valuation_index
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ}
    (ha : ν a = e) (hb : ν b = e)
    (h : (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b :=
  (canonicalDesc_eq_iff_quotient_eq_of_valuation_index
    (M := M) ν hν hcompleteν ha hb).2 h

theorem canonicalDescClass_mk_eq_iff_quotient_eq_of_valuation_index
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ}
    (_ha : ν a = e) (_hb : ν b = e) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) := by
  constructor
  · intro hclass
    exact quotient_eq_of_canonicalDescClass_mk_eq_of_valuation (M := M) ν hν hcompleteν hclass
  · intro hq
    exact canonicalDescClass_mk_eq_of_quotient_eq_of_valuation (M := M) ν hν hcompleteν hq

theorem quotient_eq_of_canonicalDescClass_mk_eq_of_valuation_index
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ}
    (_ha : ν a = e) (_hb : ν b = e)
    (h : canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) :
    ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :=
  quotient_eq_of_canonicalDescClass_mk_eq_of_valuation (M := M) ν hν hcompleteν h

theorem canonicalDescClass_mk_eq_of_quotient_eq_of_valuation_index
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (_hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (_hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ}
    (_ha : ν a = e) (_hb : ν b = e)
    (h : (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  canonicalDescClass_mk_eq_of_quotient_eq (M := M) h

theorem canonicalDesc_eq_iff_connected_class_quotient_of_valuation_index
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ}
    (ha : ν a = e) (hb : ν b = e) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b ↔
      Nonempty (GObj a ⟶ GObj b) ∧
        canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
          canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ∧
        ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) := by
  constructor
  · intro hdesc
    refine ⟨?_, ?_, ?_⟩
    · exact (canonicalDesc_eq_iff_connected_of_valuation_index
        (M := M) ν hν hcompleteν ha hb).1 hdesc
    · exact (canonicalDescClass_mk_eq_iff_canonicalDesc_eq_of_valuation_index
        (M := M) ν hν hcompleteν ha hb).2 hdesc
    · exact (canonicalDesc_eq_iff_quotient_eq_of_valuation_index
        (M := M) ν hν hcompleteν ha hb).1 hdesc
  · intro hall
    exact (canonicalDesc_eq_iff_connected_of_valuation_index
      (M := M) ν hν hcompleteν ha hb).2 hall.1

theorem canonicalDescClass_mk_eq_iff_connected_quotient_of_valuation_index
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ}
    (ha : ν a = e) (hb : ν b = e) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      Nonempty (GObj a ⟶ GObj b) ∧
        ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) := by
  constructor
  · intro hclass
    refine ⟨?_, ?_⟩
    · exact connected_of_canonicalDescClass_mk_eq_of_valuation_index
        (M := M) ν hν hcompleteν ha hb hclass
    · exact quotient_eq_of_canonicalDescClass_mk_eq_of_valuation_index
        (M := M) ν hν hcompleteν ha hb hclass
  · intro h
    exact canonicalDescClass_mk_eq_of_quotient_eq_of_valuation_index
      (M := M) ν hν hcompleteν ha hb h.2

theorem quotient_eq_iff_connected_class_of_valuation_index
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ}
    (ha : ν a = e) (hb : ν b = e) :
    ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) ↔
      Nonempty (GObj a ⟶ GObj b) ∧
        canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
          canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) := by
  constructor
  · intro hq
    refine ⟨?_, ?_⟩
    · exact connected_of_quotient_eq_of_valuation_index
        (M := M) ν hν hcompleteν ha hb hq
    · exact canonicalDescClass_mk_eq_of_quotient_eq_of_valuation_index
        (M := M) ν hν hcompleteν ha hb hq
  · intro h
    exact quotient_eq_of_connected_of_valuation_index
      (M := M) ν hν hcompleteν ha hb h.1

theorem canonicalDesc_class_quotient_connected_bundle_of_valuation_index
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ}
    (ha : ν a = e) (hb : ν b = e) :
    (canonicalDesc (M := M) a = canonicalDesc (M := M) b ↔
      canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
        canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) ∧
    (canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)))) ∧
    (((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) ↔
      Nonempty (GObj a ⟶ GObj b)) := by
  refine ⟨?_, ?_⟩
  · exact canonicalDescClass_mk_eq_iff_canonicalDesc_eq_of_valuation_index
      (M := M) ν hν hcompleteν ha hb |>.symm
  · refine ⟨?_, ?_⟩
    · exact canonicalDescClass_mk_eq_iff_quotient_eq_of_valuation_index
        (M := M) ν hν hcompleteν ha hb
    · exact quotient_eq_iff_connected_of_valuation_index
        (M := M) ν hν hcompleteν ha hb

theorem connected_class_quotient_of_canonicalDesc_eq_of_valuation_index
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ}
    (ha : ν a = e) (hb : ν b = e)
    (h : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    Nonempty (GObj a ⟶ GObj b) ∧
      canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
        canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ∧
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :=
  (canonicalDesc_eq_iff_connected_class_quotient_of_valuation_index
    (M := M) ν hν hcompleteν ha hb).1 h

theorem canonicalDesc_eq_of_connected_class_quotient_of_valuation_index
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ}
    (ha : ν a = e) (hb : ν b = e)
    (h : Nonempty (GObj a ⟶ GObj b) ∧
      canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
        canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ∧
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)))) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b :=
  (canonicalDesc_eq_iff_connected_class_quotient_of_valuation_index
    (M := M) ν hν hcompleteν ha hb).2 h

theorem connected_quotient_of_canonicalDescClass_mk_eq_of_valuation_index
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ}
    (ha : ν a = e) (hb : ν b = e)
    (h : canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) :
    Nonempty (GObj a ⟶ GObj b) ∧
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :=
  (canonicalDescClass_mk_eq_iff_connected_quotient_of_valuation_index
    (M := M) ν hν hcompleteν ha hb).1 h

theorem canonicalDescClass_mk_eq_of_connected_quotient_of_valuation_index
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ}
    (ha : ν a = e) (hb : ν b = e)
    (h : Nonempty (GObj a ⟶ GObj b) ∧
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)))) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  (canonicalDescClass_mk_eq_iff_connected_quotient_of_valuation_index
    (M := M) ν hν hcompleteν ha hb).2 h

theorem connected_class_of_quotient_eq_of_valuation_index
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ}
    (ha : ν a = e) (hb : ν b = e)
    (h : (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :
    Nonempty (GObj a ⟶ GObj b) ∧
      canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
        canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  (quotient_eq_iff_connected_class_of_valuation_index
    (M := M) ν hν hcompleteν ha hb).1 h

theorem quotient_eq_of_connected_class_of_valuation_index
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr} {e : ℤ}
    (ha : ν a = e) (hb : ν b = e)
    (h : Nonempty (GObj a ⟶ GObj b) ∧
      canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
        canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  (quotient_eq_iff_connected_class_of_valuation_index
    (M := M) ν hν hcompleteν ha hb).2 h

theorem canonicalDesc_class_quotient_connected_bundle_of_valuation_sameIndex
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b) :
    (canonicalDesc (M := M) a = canonicalDesc (M := M) b ↔
      canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
        canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) ∧
    (canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)))) ∧
    (((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) ↔
      Nonempty (GObj a ⟶ GObj b)) := by
  exact canonicalDesc_class_quotient_connected_bundle_of_valuation_index
    (M := M) ν hν hcompleteν (a := a) (b := b) (e := ν a) rfl
    (by simpa using hidx.symm)

theorem connected_class_quotient_of_canonicalDesc_eq_of_valuation_sameIndex
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b)
    (h : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    Nonempty (GObj a ⟶ GObj b) ∧
      canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
        canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ∧
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :=
  connected_class_quotient_of_canonicalDesc_eq_of_valuation_index
    (M := M) ν hν hcompleteν (ha := rfl)
    (hb := by simpa using hidx.symm) h

theorem canonicalDesc_eq_of_connected_class_quotient_of_valuation_sameIndex
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b)
    (h : Nonempty (GObj a ⟶ GObj b) ∧
      canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
        canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ∧
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)))) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b :=
  canonicalDesc_eq_of_connected_class_quotient_of_valuation_index
    (M := M) ν hν hcompleteν (ha := rfl)
    (hb := by simpa using hidx.symm) h

theorem connected_quotient_of_canonicalDescClass_mk_eq_of_valuation_sameIndex
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b)
    (h : canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) :
    Nonempty (GObj a ⟶ GObj b) ∧
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :=
  connected_quotient_of_canonicalDescClass_mk_eq_of_valuation_index
    (M := M) ν hν hcompleteν (ha := rfl)
    (hb := by simpa using hidx.symm) h

theorem canonicalDescClass_mk_eq_of_connected_quotient_of_valuation_sameIndex
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b)
    (h : Nonempty (GObj a ⟶ GObj b) ∧
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)))) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  canonicalDescClass_mk_eq_of_connected_quotient_of_valuation_index
    (M := M) ν hν hcompleteν (ha := rfl)
    (hb := by simpa using hidx.symm) h

theorem connected_class_of_quotient_eq_of_valuation_sameIndex
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b)
    (h : (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :
    Nonempty (GObj a ⟶ GObj b) ∧
      canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
        canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  connected_class_of_quotient_eq_of_valuation_index
    (M := M) ν hν hcompleteν (ha := rfl)
    (hb := by simpa using hidx.symm) h

theorem quotient_eq_of_connected_class_of_valuation_sameIndex
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b)
    (h : Nonempty (GObj a ⟶ GObj b) ∧
      canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
        canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  quotient_eq_of_connected_class_of_valuation_index
    (M := M) ν hν hcompleteν (ha := rfl)
    (hb := by simpa using hidx.symm) h

theorem canonicalDesc_eq_iff_connected_class_quotient_of_valuation_sameIndex
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b ↔
      Nonempty (GObj a ⟶ GObj b) ∧
        canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
          canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ∧
        ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) := by
  constructor
  · intro h
    exact connected_class_quotient_of_canonicalDesc_eq_of_valuation_sameIndex
      (M := M) ν hν hcompleteν hidx h
  · intro h
    exact canonicalDesc_eq_of_connected_class_quotient_of_valuation_sameIndex
      (M := M) ν hν hcompleteν hidx h

theorem canonicalDescClass_mk_eq_iff_connected_quotient_of_valuation_sameIndex
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      Nonempty (GObj a ⟶ GObj b) ∧
        ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) := by
  constructor
  · intro h
    exact connected_quotient_of_canonicalDescClass_mk_eq_of_valuation_sameIndex
      (M := M) ν hν hcompleteν hidx h
  · intro h
    exact canonicalDescClass_mk_eq_of_connected_quotient_of_valuation_sameIndex
      (M := M) ν hν hcompleteν hidx h

theorem quotient_eq_iff_connected_class_of_valuation_sameIndex
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b) :
    ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) ↔
      Nonempty (GObj a ⟶ GObj b) ∧
        canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
          canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) := by
  constructor
  · intro h
    exact connected_class_of_quotient_eq_of_valuation_sameIndex
      (M := M) ν hν hcompleteν hidx h
  · intro h
    exact quotient_eq_of_connected_class_of_valuation_sameIndex
      (M := M) ν hν hcompleteν hidx h

theorem connected_of_canonicalDesc_eq_of_valuation_sameIndex_core
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b)
    (hdesc : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    Nonempty (GObj a ⟶ GObj b) :=
  connected_of_canonicalDesc_eq_of_valuation_index
    (M := M) ν hcompleteν hdesc (e := ν a) rfl
    (by simpa using hidx.symm)

theorem quotient_eq_of_canonicalDesc_eq_of_valuation_sameIndex_core
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    {a b : HExpr}
    (hidx : ν a = ν b)
    (hdesc : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  quotient_eq_of_canonicalDesc_eq_of_valuation_index
    (M := M) ν hdesc (e := ν a) rfl
    (by simpa using hidx.symm)

theorem canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_valuation_sameIndex_core
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    {a b : HExpr}
    (hidx : ν a = ν b)
    (hdesc : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_valuation_index
    (M := M) ν hdesc (e := ν a) rfl
    (by simpa using hidx.symm)

theorem canonicalDesc_eq_iff_connected_of_valuation_sameIndex
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b ↔
      Nonempty (GObj a ⟶ GObj b) :=
  canonicalDesc_eq_iff_connected_of_valuation_index
    (M := M) ν hν hcompleteν (ha := rfl)
    (hb := by simpa using hidx.symm)

theorem connected_of_canonicalDesc_eq_of_valuation_sameIndex
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b)
    (h : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    Nonempty (GObj a ⟶ GObj b) :=
  (canonicalDesc_eq_iff_connected_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx).1 h

theorem canonicalDesc_eq_of_connected_of_valuation_sameIndex
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b)
    (h : Nonempty (GObj a ⟶ GObj b)) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b :=
  (canonicalDesc_eq_iff_connected_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx).2 h

theorem canonicalDescClass_mk_eq_iff_connected_of_valuation_sameIndex
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      Nonempty (GObj a ⟶ GObj b) :=
  canonicalDescClass_mk_eq_iff_connected_of_valuation_index
    (M := M) ν hν hcompleteν (e := ν a) rfl
    (by simpa using hidx.symm)

theorem connected_of_canonicalDescClass_mk_eq_of_valuation_sameIndex
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b)
    (h : canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) :
    Nonempty (GObj a ⟶ GObj b) :=
  (canonicalDescClass_mk_eq_iff_connected_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx).1 h

theorem canonicalDescClass_mk_eq_of_connected_of_valuation_sameIndex
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b)
    (h : Nonempty (GObj a ⟶ GObj b)) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  (canonicalDescClass_mk_eq_iff_connected_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx).2 h

theorem quotient_eq_iff_connected_of_valuation_sameIndex
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b) :
    ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) ↔
      Nonempty (GObj a ⟶ GObj b) :=
  quotient_eq_iff_connected_of_valuation_index
    (M := M) ν hν hcompleteν (e := ν a) rfl
    (by simpa using hidx.symm)

theorem connected_of_quotient_eq_of_valuation_sameIndex
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b)
    (h : (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :
    Nonempty (GObj a ⟶ GObj b) :=
  (quotient_eq_iff_connected_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx).1 h

theorem quotient_eq_of_connected_of_valuation_sameIndex
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b)
    (h : Nonempty (GObj a ⟶ GObj b)) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  (quotient_eq_iff_connected_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx).2 h

theorem canonicalDescClass_mk_eq_iff_quotient_eq_of_valuation_sameIndex
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :=
  canonicalDescClass_mk_eq_iff_quotient_eq_of_valuation_index
    (M := M) ν hν hcompleteν (e := ν a) rfl
    (by simpa using hidx.symm)

theorem quotient_eq_of_canonicalDescClass_mk_eq_of_valuation_sameIndex
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b)
    (h : canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  (canonicalDescClass_mk_eq_iff_quotient_eq_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx).1 h

theorem canonicalDescClass_mk_eq_of_quotient_eq_of_valuation_sameIndex
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b)
    (h : (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  (canonicalDescClass_mk_eq_iff_quotient_eq_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx).2 h

theorem canonicalDescClass_mk_eq_iff_canonicalDesc_eq_of_valuation_sameIndex
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      canonicalDesc (M := M) a = canonicalDesc (M := M) b :=
  canonicalDescClass_mk_eq_iff_canonicalDesc_eq_of_valuation_index
    (M := M) ν hν hcompleteν (e := ν a) rfl
    (by simpa using hidx.symm)

theorem canonicalDesc_eq_of_canonicalDescClass_mk_eq_of_valuation_sameIndex
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b)
    (h : canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b :=
  (canonicalDescClass_mk_eq_iff_canonicalDesc_eq_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx).1 h

theorem canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_valuation_sameIndex
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b)
    (h : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  (canonicalDescClass_mk_eq_iff_canonicalDesc_eq_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx).2 h

theorem canonicalDesc_eq_iff_quotient_eq_of_valuation_sameIndex
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b ↔
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :=
  canonicalDesc_eq_iff_quotient_eq_of_valuation_index
    (M := M) ν hν hcompleteν (e := ν a) rfl
    (by simpa using hidx.symm)

theorem canonicalDesc_eq_of_quotient_eq_of_valuation_sameIndex
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b)
    (h : (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b :=
  (canonicalDesc_eq_iff_quotient_eq_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx).2 h

theorem quotient_eq_of_canonicalDesc_eq_of_valuation_sameIndex
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (hidx : ν a = ν b)
    (h : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  (canonicalDesc_eq_iff_quotient_eq_of_valuation_sameIndex
    (M := M) ν hν hcompleteν hidx).1 h

theorem connected_nf_of_canonicalDesc_nf_eq_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : canonicalDesc (M := M) (nf a) = canonicalDesc (M := M) (nf b)) :
    Nonempty (GObj (nf a) ⟶ GObj (nf b)) :=
  (canonicalDesc_nf_eq_iff_connected_nf_of_valuation
    (M := M) ν hν hcompleteν a b).1 h

theorem canonicalDesc_nf_eq_of_connected_nf_of_valuation
    (M : HyperserialModel K) (ν : HExpr → ℤ)
    (hν : ∀ {a b : HExpr}, HExpr.eval M a = HExpr.eval M b → ν a = ν b)
    (hcompleteν : RewriteCompleteFromValuation (M := M) ν)
    {a b : HExpr}
    (h : Nonempty (GObj (nf a) ⟶ GObj (nf b))) :
    canonicalDesc (M := M) (nf a) = canonicalDesc (M := M) (nf b) :=
  (canonicalDesc_nf_eq_iff_connected_nf_of_valuation
    (M := M) ν hν hcompleteν a b).2 h

end

end Category
end Hyperseries
end HeytingLean
