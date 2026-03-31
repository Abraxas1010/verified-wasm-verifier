import HeytingLean.Hyperseries.TransmonomialSemantics
import HeytingLean.Hyperseries.Category.ContractibilityStrong

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Hyperseries
open HeytingLean.Hyperseries.Transmonomial
open HeytingLean.Hyperseries.Category
open CategoryTheory

noncomputable section

local instance instHyperserialDescriptionIntValuationBridge : HyperserialDescription Int :=
  HyperserialDescription.idDescription Int

example : valuation (.exp (.log (.omegaPow 7))) = 7 := by
  simp [valuation]

example : Dominates (.omegaPow 4) (.log (.omegaPow 4)) := by
  simp [Dominates, valuation]

example : Dominates (.omegaPow 6) (.omegaPow 3) := by
  simp [Dominates, valuation]

example :
    valuation (Transmonomial.iterExp 4 (Transmonomial.omegaPow 3)) = 7 := by
  exact valuation_iterExp 4 (.omegaPow 3)

example :
    valuation (Transmonomial.iterLog 5 (Transmonomial.omegaPow 12)) = 7 := by
  exact valuation_iterLog 5 (.omegaPow 12)

example :
    valuation (Transmonomial.iterExp 3 (Transmonomial.iterLog 3 (.omegaPow 9))) = 9 := by
  exact valuation_iterExp_iterLog 3 (.omegaPow 9)

example :
    valuation (Transmonomial.iterLog 2 (Transmonomial.iterExp 2 (.omegaPow (-1)))) = -1 := by
  exact valuation_iterLog_iterExp 2 (.omegaPow (-1))

example {K : Type*} [CommRing K] {M : HyperserialModel K}
    (S : Transmonomial.Semantics K M) (m : Transmonomial) :
    Transmonomial.eval S (Transmonomial.iterExp 3 m) =
      Transmonomial.evalIterExp M 3 (Transmonomial.eval S m) := by
  exact Transmonomial.eval_iterExp (S := S) 3 m

example {K : Type*} [CommRing K] {M : HyperserialModel K}
    (S : Transmonomial.Semantics K M) (m : Transmonomial) :
    Transmonomial.eval S (Transmonomial.iterLog 4 m) =
      Transmonomial.evalIterLog M 4 (Transmonomial.eval S m) := by
  exact Transmonomial.eval_iterLog (S := S) 4 m

example (a b : Transmonomial) :
    Dominates (Transmonomial.iterExp 6 a) (Transmonomial.iterExp 6 b) ↔ Dominates a b := by
  simpa using dominates_iterExp_iff 6 a b

example (a b : Transmonomial) :
    Dominates (Transmonomial.iterLog 5 a) (Transmonomial.iterLog 5 b) ↔ Dominates a b := by
  simpa using dominates_iterLog_iff 5 a b

example (a b : Transmonomial) : Dominates a b ∨ Dominates b a := by
  exact dominates_total a b

example (A B : AsymptoticClass)
    (h : AsymptoticClass.valuation A = AsymptoticClass.valuation B) :
    asymptoticClassEquivInt A = asymptoticClassEquivInt B := by
  exact (asymptoticClass_valuation_equivInt_orderIsoIntDual_eq_of_valuation_eq h).2.1

example (A B : AsymptoticClass)
    (h : asymptoticClassOrderIsoIntDual A = asymptoticClassOrderIsoIntDual B) :
    AsymptoticClass.valuation A = AsymptoticClass.valuation B := by
  exact (asymptoticClass_valuation_equivInt_orderIsoIntDual_eq_of_orderIsoIntDual_eq h).1

example (A B : AsymptoticClass)
    (h : AsymptoticClass.valuation A = AsymptoticClass.valuation B ∧
      asymptoticClassEquivInt A = asymptoticClassEquivInt B ∧
      asymptoticClassOrderIsoIntDual A = asymptoticClassOrderIsoIntDual B) :
    A = B := by
  exact asymptoticClass_eq_of_valuation_equivInt_orderIsoIntDual_eq h

example (A B : AsymptoticClass)
    (h : AsymptoticClass.valuation B ≤ AsymptoticClass.valuation A) :
    asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B := by
  exact
    asymptoticClass_orderIsoIntDual_le_of_dominates_valuation_equivInt_orderIsoIntDual_le
      (asymptoticClass_dominates_valuation_equivInt_orderIsoIntDual_le_of_valuation_le h)

example (A B : AsymptoticClass)
    (h : asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A) :
    AsymptoticClass.valuation B ≤ AsymptoticClass.valuation A := by
  exact
    asymptoticClass_valuation_le_of_dominates_valuation_equivInt_orderIsoIntDual_le
      (asymptoticClass_dominates_valuation_equivInt_orderIsoIntDual_le_of_equivInt_le h)

example (A B : AsymptoticClass)
    (h : asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A ∧
      asymptoticClassEquivInt A ≤ asymptoticClassEquivInt B) :
    AsymptoticClass.Dominates A B ∧ AsymptoticClass.Dominates B A := by
  exact
    asymptoticClass_dominates_antisymm_of_dominates_equivInt_orderIso_antisymm
      (asymptoticClass_dominates_equivInt_orderIso_antisymm_of_equivInt_antisymm h)

example (A B : AsymptoticClass)
    (h : asymptoticClassOrderIsoIntDual A ≤ asymptoticClassOrderIsoIntDual B ∧
      asymptoticClassOrderIsoIntDual B ≤ asymptoticClassOrderIsoIntDual A) :
    asymptoticClassEquivInt B ≤ asymptoticClassEquivInt A ∧
      asymptoticClassEquivInt A ≤ asymptoticClassEquivInt B := by
  exact
    asymptoticClass_equivInt_antisymm_of_dominates_equivInt_orderIso_antisymm
      (asymptoticClass_dominates_equivInt_orderIso_antisymm_of_orderIsoIntDual_antisymm h)

example :
    Transmonomial.eval surrealTransmonomialSemantics (.exp (.log (.omegaPow 3))) = (3 : Surreal) := by
  simp [Transmonomial.eval, surrealTransmonomialSemantics]

example (M : HyperserialModel Int)
    (hcompleteν : RewriteCompleteFromValuation (M := M) (fun _ : HExpr => (0 : ℤ)))
    (a b : HExpr) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b ↔ Nonempty (GObj a ⟶ GObj b) := by
  have hν :
      ∀ {x y : HExpr},
        HExpr.eval M x = HExpr.eval M y →
          (fun _ : HExpr => (0 : ℤ)) x = (fun _ : HExpr => (0 : ℤ)) y := by
    intro x y hxy
    rfl
  simpa using
    (canonicalDesc_eq_iff_connected_of_valuation
      (M := M) (ν := fun _ : HExpr => (0 : ℤ)) (hν := hν) (hcompleteν := hcompleteν) a b)

example (M : HyperserialModel Int)
    (hcompleteν : RewriteCompleteFromValuation (M := M) (fun _ : HExpr => (0 : ℤ)))
    {a b : HExpr}
    (h : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    Nonempty (GObj a ⟶ GObj b) := by
  exact
    connected_of_canonicalDesc_eq_of_valuation
      (M := M) (ν := fun _ : HExpr => (0 : ℤ))
      (hν := by intro _ _ _; rfl) hcompleteν h

example (M : HyperserialModel Int)
    (hcompleteν : RewriteCompleteFromValuation (M := M) (fun _ : HExpr => (0 : ℤ)))
    {a b : HExpr}
    (hdesc : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    Nonempty (GObj a ⟶ GObj b) := by
  exact
    connected_of_canonicalDesc_eq_of_valuation_index
      (M := M) (ν := fun _ : HExpr => (0 : ℤ))
      hcompleteν hdesc rfl rfl

example (M : HyperserialModel Int)
    {a b : HExpr}
    (hdesc : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) =
      (Quot.mk _ b : NormalizedQuotient (M := M)) := by
  exact quotient_eq_of_canonicalDesc_eq_of_valuation_index
    (M := M) (ν := fun _ : HExpr => (0 : ℤ))
    hdesc rfl rfl

example (M : HyperserialModel Int)
    {a b : HExpr}
    (hdesc : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) := by
  exact canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_valuation_index
    (M := M) (ν := fun _ : HExpr => (0 : ℤ))
    hdesc rfl rfl

example (M : HyperserialModel Int)
    (hcompleteν : RewriteCompleteFromValuation (M := M) (fun _ : HExpr => (0 : ℤ)))
    {d : HDesc Int}
    (x y : CanonicalFiber M d) :
    Nonempty (GObj x.1 ⟶ GObj y.1) := by
  exact canonicalFiber_connected_of_valuation
    (M := M) (ν := fun _ : HExpr => (0 : ℤ))
    (hν := by intro _ _ _; rfl) hcompleteν x y

example (M : HyperserialModel Int)
    (hcompleteν : RewriteCompleteFromValuation (M := M) (fun _ : HExpr => (0 : ℤ)))
    {d : HDesc Int}
    (c : CanonicalFiber M d) :
    ∀ x : CanonicalFiber M d, Nonempty (GObj x.1 ⟶ GObj c.1) := by
  exact canonicalFiber_contractible_at_of_valuation
    (M := M) (ν := fun _ : HExpr => (0 : ℤ))
    (hν := by intro _ _ _; rfl) hcompleteν c

example (M : HyperserialModel Int)
    {d : HDesc Int} {e : ℤ}
    (x y : CanonicalValuationFiber M (fun _ : HExpr => (0 : ℤ)) d e) :
    NormalizedConnected (M := M) x.1 y.1 := by
  exact normalizedConnected_of_canonicalValuationFiber
    (M := M) (ν := fun _ : HExpr => (0 : ℤ)) x y

example (M : HyperserialModel Int)
    {d : HDesc Int} {e : ℤ}
    (x y : CanonicalValuationFiber M (fun _ : HExpr => (0 : ℤ)) d e) :
    (Quot.mk _ x.1 : NormalizedQuotient (M := M)) =
      (Quot.mk _ y.1 : NormalizedQuotient (M := M)) := by
  exact quotient_eq_of_canonicalValuationFiber
    (M := M) (ν := fun _ : HExpr => (0 : ℤ)) x y

example (M : HyperserialModel Int)
    {d : HDesc Int} {e : ℤ}
    (x y : CanonicalValuationFiber M (fun _ : HExpr => (0 : ℤ)) d e) :
    canonicalDescClass (M := M) (Quot.mk _ x.1 : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ y.1 : NormalizedQuotient (M := M)) := by
  exact canonicalDescClass_eq_of_canonicalValuationFiber
    (M := M) (ν := fun _ : HExpr => (0 : ℤ)) x y

example (M : HyperserialModel Int)
    (hcompleteν : RewriteCompleteFromValuation (M := M) (fun _ : HExpr => (0 : ℤ)))
    {a b : HExpr}
    (h : Nonempty (GObj a ⟶ GObj b)) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b := by
  exact
    canonicalDesc_eq_of_connected_of_valuation
      (M := M) (ν := fun _ : HExpr => (0 : ℤ))
      (hν := by intro _ _ _; rfl) hcompleteν h

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
    (a b : HExpr) :
    NormalizedConnected (M := M) a b ↔ Nonempty (GObj (nf a) ⟶ GObj (nf b)) := by
  simpa using
    (normalizedConnected_iff_connected_nf_of_valuation
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
    (h : Nonempty (GObj (nf a) ⟶ GObj (nf b))) :
    canonicalDesc (M := M) (nf a) = canonicalDesc (M := M) (nf b) := by
  exact
    canonicalDesc_nf_eq_of_connected_nf_of_valuation
      (M := M) (ν := fun _ : HExpr => (0 : ℤ))
      (hν := by intro _ _ _; rfl) hcompleteν h

example (M : HyperserialModel Int)
    (hcompleteν : RewriteCompleteFromValuation (M := M) (fun _ : HExpr => (0 : ℤ)))
    (a b : HExpr) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      Nonempty (GObj (nf a) ⟶ GObj (nf b)) := by
  simpa using
    (canonicalDescClass_mk_eq_iff_connected_nf_of_valuation
      (M := M) (ν := fun _ : HExpr => (0 : ℤ))
      (hν := by intro _ _ _; rfl) hcompleteν a b)

example (M : HyperserialModel Int)
    (hcompleteν : RewriteCompleteFromValuation (M := M) (fun _ : HExpr => (0 : ℤ)))
    (a b : HExpr) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      Nonempty (GObj a ⟶ GObj b) := by
  simpa using
    (canonicalDescClass_mk_eq_iff_connected_of_valuation
      (M := M) (ν := fun _ : HExpr => (0 : ℤ))
      (hν := by intro _ _ _; rfl) hcompleteν a b)

example (M : HyperserialModel Int)
    (hcompleteν : RewriteCompleteFromValuation (M := M) (fun _ : HExpr => (0 : ℤ)))
    {a b : HExpr}
    (h : canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) :
    Nonempty (GObj (nf a) ⟶ GObj (nf b)) := by
  exact
    connected_nf_of_canonicalDescClass_mk_eq_of_valuation
      (M := M) (ν := fun _ : HExpr => (0 : ℤ))
      (hν := by intro _ _ _; rfl) hcompleteν h

example (M : HyperserialModel Int)
    (hcompleteν : RewriteCompleteFromValuation (M := M) (fun _ : HExpr => (0 : ℤ)))
    {a b : HExpr}
    (h : canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) :
    Nonempty (GObj a ⟶ GObj b) := by
  exact
    connected_of_canonicalDescClass_mk_eq_of_valuation
      (M := M) (ν := fun _ : HExpr => (0 : ℤ))
      (hν := by intro _ _ _; rfl) hcompleteν h

example (M : HyperserialModel Int)
    (hcompleteν : RewriteCompleteFromValuation (M := M) (fun _ : HExpr => (0 : ℤ)))
    {a b : HExpr}
    (h : Nonempty (GObj (nf a) ⟶ GObj (nf b))) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) := by
  exact
    canonicalDescClass_mk_eq_of_connected_nf_of_valuation
      (M := M) (ν := fun _ : HExpr => (0 : ℤ))
      (hν := by intro _ _ _; rfl) hcompleteν h

example (M : HyperserialModel Int)
    (hcompleteν : RewriteCompleteFromValuation (M := M) (fun _ : HExpr => (0 : ℤ)))
    {a b : HExpr}
    (h : Nonempty (GObj a ⟶ GObj b)) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) := by
  exact
    canonicalDescClass_mk_eq_of_connected_of_valuation
      (M := M) (ν := fun _ : HExpr => (0 : ℤ))
      (hν := by intro _ _ _; rfl) hcompleteν h

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
    canonicalDesc (M := M) a = canonicalDesc (M := M) b ↔
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) := by
  exact canonicalDesc_eq_iff_quotient_eq_of_valuation_sameIndex
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
    canonicalDesc (M := M) a = canonicalDesc (M := M) b ↔
      Nonempty (GObj a ⟶ GObj b) ∧
        canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
          canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ∧
        ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) := by
  exact canonicalDesc_eq_iff_connected_class_quotient_of_valuation_sameIndex
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

section NameWiringSmoke

#check valuation
#check valuation_one
#check valuation_omegaPow
#check valuation_exp
#check valuation_log
#check valuation_iterExp
#check valuation_iterLog
#check valuation_iterExp_iterLog
#check valuation_iterLog_iterExp
#check valuation_eq_iterExp_iff
#check valuation_eq_iterLog_iff
#check valuation_eq_exp_iff
#check valuation_eq_log_iff
#check valuation_exp_log
#check valuation_log_exp
#check Dominates
#check dominates_refl
#check dominates_trans
#check dominates_total
#check valuation_eq_of_dominates_antisymm
#check valuation_eq_iff_dominates_antisymm
#check Equivalent
#check equivalent_iff
#check equivalent_refl
#check equivalent_symm
#check equivalent_trans
#check equivalent_iff_dominates_antisymm
#check equivalent_iterExp_iff
#check equivalent_iterLog_iff
#check equivalent_iterExp_iterLog_iff
#check equivalent_iterLog_iterExp_iff
#check equivalent_exp_iff
#check equivalent_log_iff
#check equivalent_exp_log_iff
#check equivalent_log_exp_iff
#check equivalent_iterExp_iterLog_of_equivalent
#check equivalent_iterLog_iterExp_of_equivalent
#check equivalent_exp_of_equivalent
#check equivalent_log_of_equivalent
#check equivalent_exp_log_of_equivalent
#check equivalent_log_exp_of_equivalent
#check AsymptoticClass
#check toAsymptoticClass
#check toAsymptoticClass_eq
#check AsymptoticClass.exp
#check AsymptoticClass.log
#check AsymptoticClass.iterExp
#check AsymptoticClass.iterLog
#check AsymptoticClass.valuation
#check asymptoticClass_exp_mk
#check asymptoticClass_log_mk
#check asymptoticClass_iterExp_mk
#check asymptoticClass_iterLog_mk
#check asymptoticClass_valuation_mk
#check asymptoticClass_valuation_exp
#check asymptoticClass_valuation_log
#check asymptoticClass_valuation_iterExp
#check asymptoticClass_valuation_iterLog
#check asymptoticClass_eq_iff_valuation_eq
#check asymptoticClass_eq_of_valuation_eq
#check asymptoticClassOfInt
#check asymptoticClass_valuation_ofInt
#check asymptoticClass_ofInt_valuation
#check asymptoticClass_eq_iff_intRep_eq
#check asymptoticClass_exists_of_valuation
#check asymptoticClass_existsUnique_of_valuation
#check asymptoticClassEquivInt
#check asymptoticClass_exp_ofInt
#check asymptoticClass_log_ofInt
#check asymptoticClass_iterExp_ofInt
#check asymptoticClass_iterLog_ofInt
#check asymptoticClassEquivInt_apply
#check asymptoticClassEquivInt_symm_apply
#check asymptoticClassEquivInt_apply_ofInt
#check asymptoticClassEquivInt_exp
#check asymptoticClassEquivInt_log
#check asymptoticClassEquivInt_iterExp
#check asymptoticClassEquivInt_iterLog
#check asymptoticClass_eq_exp_iff
#check asymptoticClass_eq_log_iff
#check asymptoticClass_eq_iterExp_iff
#check asymptoticClass_eq_iterLog_iff
#check asymptoticClass_exp_log
#check asymptoticClass_log_exp
#check asymptoticClass_iterExp_iterLog
#check asymptoticClass_iterLog_iterExp
#check AsymptoticClass.Dominates
#check asymptoticClass_dominates_mk
#check asymptoticClass_dominates_iff_valuation
#check asymptoticClass_dominates_ofInt_iff
#check asymptoticClass_dominates_refl
#check asymptoticClass_dominates_trans
#check asymptoticClass_dominates_total
#check asymptoticClass_valuation_eq_iff_dominates_antisymm
#check asymptoticClass_eq_iff_dominates_antisymm
#check asymptoticClass_eq_of_dominates_antisymm
#check (inferInstance : DecidableEq AsymptoticClass)
#check (inferInstance : DecidableLE AsymptoticClass)
#check asymptoticClass_dominates_exp_iff
#check asymptoticClass_dominates_log_iff
#check asymptoticClass_dominates_iterExp_iff
#check asymptoticClass_dominates_iterLog_iff
#check asymptoticClass_exp_monotone
#check asymptoticClass_log_monotone
#check asymptoticClass_iterExp_monotone
#check asymptoticClass_iterLog_monotone
#check asymptoticClassExpEquiv
#check asymptoticClassExpOrderIso
#check asymptoticClassLogOrderIso
#check asymptoticClassIterExpEquiv
#check asymptoticClassIterExpOrderIso
#check asymptoticClassIterLogOrderIso
#check asymptoticClassOrderIsoIntDual
#check asymptoticClassOrderIsoIntDual_apply
#check asymptoticClassOrderIsoIntDual_apply_eq_equivInt
#check asymptoticClassOrderIsoIntDual_symm_apply
#check asymptoticClassOrderIsoIntDual_symm_apply_eq_equivInt
#check asymptoticClassOrderIsoIntDual_apply_ofInt
#check asymptoticClassOrderIsoIntDual_exp
#check asymptoticClassOrderIsoIntDual_log
#check asymptoticClassOrderIsoIntDual_iterExp
#check asymptoticClassOrderIsoIntDual_iterLog
#check asymptoticClass_dominates_iff_orderIsoIntDual_le
#check asymptoticClass_eq_iff_equivInt_eq
#check asymptoticClass_dominates_iff_equivInt_le
#check asymptoticClass_dominates_of_equivInt_le
#check asymptoticClass_equivInt_le_of_dominates
#check asymptoticClass_dominates_of_orderIsoIntDual_le
#check asymptoticClass_orderIsoIntDual_le_of_dominates
#check asymptoticClass_dominates_iff_valuation_equivInt_orderIsoIntDual_le
#check asymptoticClass_dominates_valuation_equivInt_orderIsoIntDual_le_of_dominates
#check asymptoticClass_dominates_of_valuation_equivInt_orderIsoIntDual_le
#check asymptoticClass_valuation_le_of_dominates_valuation_equivInt_orderIsoIntDual_le
#check asymptoticClass_equivInt_le_of_dominates_valuation_equivInt_orderIsoIntDual_le
#check asymptoticClass_orderIsoIntDual_le_of_dominates_valuation_equivInt_orderIsoIntDual_le
#check asymptoticClass_dominates_valuation_equivInt_orderIsoIntDual_le_of_valuation_le
#check asymptoticClass_dominates_valuation_equivInt_orderIsoIntDual_le_of_equivInt_le
#check asymptoticClass_dominates_valuation_equivInt_orderIsoIntDual_le_of_orderIsoIntDual_le
#check asymptoticClass_dominates_antisymm_iff_equivInt_antisymm
#check asymptoticClass_dominates_antisymm_iff_orderIsoIntDual_antisymm
#check asymptoticClass_eq_of_equivInt_antisymm
#check asymptoticClass_eq_iff_equivInt_antisymm
#check asymptoticClass_eq_of_orderIsoIntDual_antisymm
#check asymptoticClass_eq_iff_orderIsoIntDual_antisymm
#check asymptoticClass_eq_iff_dominates_equivInt_orderIso_antisymm
#check asymptoticClass_dominates_equivInt_orderIso_antisymm_of_eq
#check asymptoticClass_eq_of_dominates_equivInt_orderIso_antisymm
#check asymptoticClass_dominates_antisymm_of_dominates_equivInt_orderIso_antisymm
#check asymptoticClass_equivInt_antisymm_of_dominates_equivInt_orderIso_antisymm
#check asymptoticClass_orderIsoIntDual_antisymm_of_dominates_equivInt_orderIso_antisymm
#check asymptoticClass_dominates_equivInt_orderIso_antisymm_of_dominates_antisymm
#check asymptoticClass_dominates_equivInt_orderIso_antisymm_of_equivInt_antisymm
#check asymptoticClass_dominates_equivInt_orderIso_antisymm_of_orderIsoIntDual_antisymm
#check asymptoticClass_eq_iff_orderIsoIntDual_eq
#check asymptoticClass_equivInt_eq_of_valuation_eq
#check asymptoticClass_valuation_eq_of_equivInt_eq
#check asymptoticClass_orderIsoIntDual_eq_of_valuation_eq
#check asymptoticClass_valuation_eq_of_orderIsoIntDual_eq
#check asymptoticClass_equivInt_eq_of_orderIsoIntDual_eq
#check asymptoticClass_orderIsoIntDual_eq_of_equivInt_eq
#check asymptoticClass_eq_iff_valuation_equivInt_orderIsoIntDual_eq
#check asymptoticClass_valuation_equivInt_orderIsoIntDual_eq_of_eq
#check asymptoticClass_eq_of_valuation_equivInt_orderIsoIntDual_eq
#check asymptoticClass_valuation_eq_of_valuation_equivInt_orderIsoIntDual_eq
#check asymptoticClass_equivInt_eq_of_valuation_equivInt_orderIsoIntDual_eq
#check asymptoticClass_orderIsoIntDual_eq_of_valuation_equivInt_orderIsoIntDual_eq
#check asymptoticClass_valuation_equivInt_orderIsoIntDual_eq_of_valuation_eq
#check asymptoticClass_valuation_equivInt_orderIsoIntDual_eq_of_equivInt_eq
#check asymptoticClass_valuation_equivInt_orderIsoIntDual_eq_of_orderIsoIntDual_eq
#check asymptoticClassEquivInt_injective
#check asymptoticClassEquivInt_surjective
#check asymptoticClassEquivInt_bijective
#check asymptoticClassOrderIsoIntDual_injective
#check asymptoticClassOrderIsoIntDual_surjective
#check asymptoticClassOrderIsoIntDual_bijective
#check asymptoticClassOrderIsoIntDual_eq_iff_equivInt_eq
#check asymptoticClassEquivInt_eq_iff
#check asymptoticClassOrderIsoIntDual_eq_iff
#check asymptoticClass_exists_eq_equivInt
#check asymptoticClass_exists_eq_orderIsoIntDual
#check asymptoticClass_existsUnique_equivInt
#check asymptoticClass_existsUnique_orderIsoIntDual
#check dominates_iterExp_iff
#check dominates_iterLog_iff
#check dominates_iterExp_iterLog_iff
#check dominates_iterLog_iterExp_iff
#check dominates_iterExp_iterLog_of_dominates
#check dominates_iterLog_iterExp_of_dominates
#check dominates_exp_log_iff
#check dominates_log_exp_iff
#check dominates_exp_log_of_dominates
#check dominates_log_exp_of_dominates
#check dominates_exp_iff
#check dominates_log_iff
#check dominates_exp_of_dominates
#check dominates_log_of_dominates
#check eval
#check eval_one
#check eval_omegaPow
#check eval_exp
#check eval_log
#check evalIterExp
#check evalIterExp_zero
#check evalIterExp_succ
#check evalIterLog
#check evalIterLog_zero
#check evalIterLog_succ
#check eval_iterExp
#check eval_iterLog
#check evalIterExp_eq_iterate
#check evalIterLog_eq_iterate
#check evalIterExp_evalIterLog
#check evalIterLog_evalIterExp
#check eval_iterExp_iterLog
#check eval_iterLog_iterExp
#check eval_exp_log
#check eval_log_exp
#check valuationStableUnderExpLog
#check valuationStableUnderExpLog_all
#check surreal_eval_omegaPow
#check eval_ofSurrealExpLog_omegaPow
#check canonicalDesc_eq_iff_connected_of_valuation
#check connected_of_canonicalDesc_eq_of_valuation
#check canonicalFiber_connected_of_valuation
#check canonicalFiber_contractible_at_of_valuation
#check CanonicalValuationFiber
#check canonicalDesc_eq_of_canonicalValuationFiber
#check valuation_eq_of_canonicalValuationFiber
#check eval_eq_of_canonicalValuationFiber
#check canonicalValuationFiber_connected
#check canonicalValuationFiber_contractible_at
#check normalizedConnected_of_canonicalValuationFiber
#check quotient_eq_of_canonicalValuationFiber
#check canonicalDescClass_eq_of_canonicalValuationFiber
#check connected_of_canonicalDesc_eq_of_valuation_index
#check quotient_eq_of_canonicalDesc_eq_of_valuation_index
#check canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_valuation_index
#check canonicalDesc_eq_iff_connected_of_valuation_index
#check canonicalDesc_eq_of_connected_of_valuation_index
#check canonicalDescClass_mk_eq_iff_canonicalDesc_eq_of_valuation_index
#check canonicalDesc_eq_of_canonicalDescClass_mk_eq_of_valuation_index
#check quotient_eq_iff_connected_of_valuation_index
#check connected_of_quotient_eq_of_valuation_index
#check quotient_eq_of_connected_of_valuation_index
#check canonicalDescClass_mk_eq_iff_connected_of_valuation_index
#check connected_of_canonicalDescClass_mk_eq_of_valuation_index
#check canonicalDescClass_mk_eq_of_connected_of_valuation_index
#check canonicalDesc_eq_iff_quotient_eq_of_valuation_index
#check canonicalDesc_eq_of_quotient_eq_of_valuation_index
#check canonicalDescClass_mk_eq_iff_quotient_eq_of_valuation_index
#check quotient_eq_of_canonicalDescClass_mk_eq_of_valuation_index
#check canonicalDescClass_mk_eq_of_quotient_eq_of_valuation_index
#check canonicalDesc_eq_iff_connected_class_quotient_of_valuation_index
#check canonicalDescClass_mk_eq_iff_connected_quotient_of_valuation_index
#check quotient_eq_iff_connected_class_of_valuation_index
#check canonicalDesc_class_quotient_connected_bundle_of_valuation_index
#check connected_class_quotient_of_canonicalDesc_eq_of_valuation_index
#check canonicalDesc_eq_of_connected_class_quotient_of_valuation_index
#check connected_quotient_of_canonicalDescClass_mk_eq_of_valuation_index
#check canonicalDescClass_mk_eq_of_connected_quotient_of_valuation_index
#check connected_class_of_quotient_eq_of_valuation_index
#check quotient_eq_of_connected_class_of_valuation_index
#check canonicalDesc_class_quotient_connected_bundle_of_valuation_sameIndex
#check connected_class_quotient_of_canonicalDesc_eq_of_valuation_sameIndex
#check canonicalDesc_eq_of_connected_class_quotient_of_valuation_sameIndex
#check connected_quotient_of_canonicalDescClass_mk_eq_of_valuation_sameIndex
#check canonicalDescClass_mk_eq_of_connected_quotient_of_valuation_sameIndex
#check connected_class_of_quotient_eq_of_valuation_sameIndex
#check quotient_eq_of_connected_class_of_valuation_sameIndex
#check canonicalDesc_eq_iff_connected_class_quotient_of_valuation_sameIndex
#check canonicalDescClass_mk_eq_iff_connected_quotient_of_valuation_sameIndex
#check quotient_eq_iff_connected_class_of_valuation_sameIndex
#check connected_of_canonicalDesc_eq_of_valuation_sameIndex_core
#check quotient_eq_of_canonicalDesc_eq_of_valuation_sameIndex_core
#check canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_valuation_sameIndex_core
#check canonicalDesc_eq_iff_connected_of_valuation_sameIndex
#check connected_of_canonicalDesc_eq_of_valuation_sameIndex
#check canonicalDesc_eq_of_connected_of_valuation_sameIndex
#check canonicalDescClass_mk_eq_iff_connected_of_valuation_sameIndex
#check connected_of_canonicalDescClass_mk_eq_of_valuation_sameIndex
#check canonicalDescClass_mk_eq_of_connected_of_valuation_sameIndex
#check quotient_eq_iff_connected_of_valuation_sameIndex
#check connected_of_quotient_eq_of_valuation_sameIndex
#check quotient_eq_of_connected_of_valuation_sameIndex
#check canonicalDescClass_mk_eq_iff_quotient_eq_of_valuation_sameIndex
#check quotient_eq_of_canonicalDescClass_mk_eq_of_valuation_sameIndex
#check canonicalDescClass_mk_eq_of_quotient_eq_of_valuation_sameIndex
#check canonicalDescClass_mk_eq_iff_canonicalDesc_eq_of_valuation_sameIndex
#check canonicalDesc_eq_of_canonicalDescClass_mk_eq_of_valuation_sameIndex
#check canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_valuation_sameIndex
#check canonicalDesc_eq_iff_quotient_eq_of_valuation_sameIndex
#check canonicalDesc_eq_of_quotient_eq_of_valuation_sameIndex
#check quotient_eq_of_canonicalDesc_eq_of_valuation_sameIndex
#check canonicalDesc_eq_of_connected_of_valuation
#check canonicalDesc_nf_eq_iff_connected_nf_of_valuation
#check normalizedConnected_iff_connected_nf_of_valuation
#check connected_nf_of_canonicalDesc_nf_eq_of_valuation
#check canonicalDesc_nf_eq_of_connected_nf_of_valuation
#check canonicalDescClass_mk_eq_iff_connected_nf
#check canonicalDescClass_mk_eq_iff_normalizedConnected_of_rewriteComplete
#check normalizedConnected_of_canonicalDescClass_mk_eq_of_rewriteComplete
#check canonicalDescClass_mk_eq_of_normalizedConnected_of_rewriteComplete
#check canonicalDescClass_mk_eq_iff_connected_nf_of_valuation
#check canonicalDescClass_mk_eq_iff_normalizedConnected_of_valuation
#check normalizedConnected_of_canonicalDescClass_mk_eq_of_valuation
#check canonicalDescClass_mk_eq_of_normalizedConnected_of_valuation
#check connected_nf_of_canonicalDescClass_mk_eq
#check canonicalDescClass_mk_eq_of_connected_nf
#check canonicalDescClass_mk_eq_iff_connected
#check connected_of_canonicalDescClass_mk_eq
#check canonicalDescClass_mk_eq_of_connected
#check quotient_eq_of_connected
#check connected_of_quotient_eq
#check quotient_eq_iff_connected
#check canonicalDesc_eq_of_quotient_eq
#check quotient_eq_of_canonicalDesc_eq
#check canonicalDesc_eq_iff_quotient_eq
#check canonicalDescClass_mk_eq_iff_quotient_eq
#check canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_rewriteComplete
#check canonicalDesc_eq_of_canonicalDescClass_mk_eq_of_rewriteComplete
#check canonicalDescClass_mk_eq_iff_canonicalDesc_eq_of_rewriteComplete
#check connected_nf_of_canonicalDescClass_mk_eq_of_valuation
#check canonicalDescClass_mk_eq_of_connected_nf_of_valuation
#check canonicalDescClass_mk_eq_iff_connected_of_valuation
#check connected_of_canonicalDescClass_mk_eq_of_valuation
#check canonicalDescClass_mk_eq_of_connected_of_valuation
#check canonicalDescClass_mk_eq_of_quotient_eq_of_valuation
#check quotient_eq_of_canonicalDescClass_mk_eq_of_valuation
#check canonicalDescClass_mk_eq_iff_quotient_eq_of_valuation
#check quotient_eq_of_connected_of_valuation
#check connected_of_quotient_eq_of_valuation
#check quotient_eq_iff_connected_of_valuation
#check canonicalDesc_eq_of_quotient_eq_of_valuation
#check quotient_eq_of_canonicalDesc_eq_of_valuation
#check canonicalDesc_eq_iff_quotient_eq_of_valuation
#check canonicalDescClass_mk_eq_of_canonicalDesc_eq_of_valuation
#check canonicalDesc_eq_of_canonicalDescClass_mk_eq_of_valuation
#check canonicalDescClass_mk_eq_iff_canonicalDesc_eq_of_valuation
#check canonicalDesc_eq_iff_connected_class_quotient_of_valuation
#check canonicalDescClass_mk_eq_iff_connected_quotient_of_valuation
#check quotient_eq_iff_connected_class_of_valuation
#check canonicalDesc_class_quotient_connected_bundle_of_valuation
#check connected_class_quotient_of_canonicalDesc_eq_of_valuation
#check canonicalDesc_eq_of_connected_class_quotient_of_valuation
#check connected_quotient_of_canonicalDescClass_mk_eq_of_valuation
#check canonicalDescClass_mk_eq_of_connected_quotient_of_valuation
#check connected_class_of_quotient_eq_of_valuation
#check quotient_eq_of_connected_class_of_valuation

end NameWiringSmoke

end
end Numbers
end Tests
end HeytingLean
