import HeytingLean.Hyperseries.Category.CanonicalizationBridge

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Hyperseries
open HeytingLean.Hyperseries.Category
open CategoryTheory

noncomputable section

local instance instHyperserialDescriptionIntBridge : HyperserialDescription Int :=
  HyperserialDescription.idDescription Int

example (M : HyperserialModel Int) (a b : HExpr) (f : GObj a ⟶ GObj b) :
    HExpr.eval M a = HExpr.eval M b :=
  eval_eq_of_groupoid_hom (M := M) f

example (M : HyperserialModel Int) (a b : HExpr)
    (h : Nonempty (GObj a ⟶ GObj b)) :
    HExpr.eval M a = HExpr.eval M b :=
  eval_eq_of_connected (M := M) h

example (M : HyperserialModel Int) (a b : HExpr) (h : HRewriteSteps a b) :
    HExpr.eval M a = HExpr.eval M b :=
  eval_eq_of_rewrite_steps (M := M) h

example (M : HyperserialModel Int) (a b : HExpr) (h : HRewriteSteps a b) :
    NormalizedConnected (M := M) a b :=
  rewrite_steps_implies_normalizedConnected (M := M) h

example (M : HyperserialModel Int) (a b : HExpr) (f : GObj a ⟶ GObj b) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b :=
  groupoid_hom_implies_canonicalDesc_eq (M := M) f

example (M : HyperserialModel Int) (a b : HExpr)
    (h : Nonempty (GObj a ⟶ GObj b)) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b :=
  connected_implies_canonicalDesc_eq (M := M) h

example (M : HyperserialModel Int) (a b : HExpr) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b ↔
      NormalizedConnected (M := M) a b := by
  simpa using canonicalDesc_eq_iff_normalizedConnected (M := M) a b

example (M : HyperserialModel Int) {a b : HExpr}
    (h : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  quotient_eq_of_canonicalDesc_eq (M := M) h

example (M : HyperserialModel Int) {a b : HExpr}
    (h : (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b :=
  canonicalDesc_eq_of_quotient_eq (M := M) h

example (M : HyperserialModel Int) (a b : HExpr) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b ↔
      ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) := by
  simpa using canonicalDesc_eq_iff_quotient_eq (M := M) a b

example (M : HyperserialModel Int) {a b : HExpr}
    (h : canonicalDesc (M := M) a = canonicalDesc (M := M) b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  canonicalDescClass_mk_eq_of_canonicalDesc_eq (M := M) h

example (M : HyperserialModel Int) {a b : HExpr}
    (h : canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) :
    canonicalDesc (M := M) a = canonicalDesc (M := M) b :=
  canonicalDesc_eq_of_canonicalDescClass_mk_eq (M := M) h

example (M : HyperserialModel Int) (a b : HExpr) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      canonicalDesc (M := M) a = canonicalDesc (M := M) b := by
  simpa using canonicalDescClass_mk_eq_iff_canonicalDesc_eq (M := M) a b

example (M : HyperserialModel Int) (a : HExpr) :
    NormalizedConnected (M := M) a a :=
  normalizedConnected_refl (M := M) a

example (M : HyperserialModel Int) {a b : HExpr}
    (h : NormalizedConnected (M := M) a b) :
    NormalizedConnected (M := M) b a :=
  normalizedConnected_symm (M := M) h

example (M : HyperserialModel Int) {a b c : HExpr}
    (hab : NormalizedConnected (M := M) a b)
    (hbc : NormalizedConnected (M := M) b c) :
    NormalizedConnected (M := M) a c :=
  normalizedConnected_trans (M := M) hab hbc

example (M : HyperserialModel Int) : Setoid HExpr :=
  normalizedConnectedSetoid (M := M)

example (M : HyperserialModel Int) : Sort _ :=
  NormalizedQuotient (M := M)

example (M : HyperserialModel Int) (a : HExpr) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDesc (M := M) (nf a) := by
  simp

example (M : HyperserialModel Int) {a b : HExpr}
    (h : NormalizedConnected (M := M) a b) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  quotient_eq_of_normalizedConnected (M := M) h

example (M : HyperserialModel Int) {a b : HExpr}
    (h : (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :
    NormalizedConnected (M := M) a b :=
  normalizedConnected_of_quotient_eq (M := M) h

example (M : HyperserialModel Int) (a b : HExpr) :
    ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) ↔
      NormalizedConnected (M := M) a b := by
  simpa using quotient_eq_iff_normalizedConnected (M := M) a b

example (M : HyperserialModel Int) {a b : HExpr}
    (h : NormalizedConnected (M := M) a b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  canonicalDescClass_eq_of_normalizedConnected (M := M) h

example (M : HyperserialModel Int) (a b : HExpr) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) ↔
      NormalizedConnected (M := M) a b := by
  simpa using canonicalDescClass_mk_eq_iff_normalizedConnected (M := M) a b

example (M : HyperserialModel Int) {a b : HExpr}
    (h : canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) :
    NormalizedConnected (M := M) a b :=
  normalizedConnected_of_canonicalDescClass_mk_eq (M := M) h

example (M : HyperserialModel Int) {a b : HExpr}
    (h : canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M))) :
    (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  quotient_eq_of_canonicalDescClass_mk_eq (M := M) h

example (M : HyperserialModel Int) {a b : HExpr}
    (h : (Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  canonicalDescClass_mk_eq_of_quotient_eq (M := M) h

example (M : HyperserialModel Int) (a b : HExpr) :
    ((Quot.mk _ a : NormalizedQuotient (M := M)) = (Quot.mk _ b : NormalizedQuotient (M := M))) ↔
      canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
        canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) := by
  simpa using quotient_eq_iff_canonicalDescClass_mk_eq (M := M) a b

example (M : HyperserialModel Int) {a b : HExpr} (h : HRewriteSteps a b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  canonicalDescClass_mk_eq_of_rewrite_steps (M := M) h

example (M : HyperserialModel Int) {a b : HExpr} (f : GObj a ⟶ GObj b) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  canonicalDescClass_mk_eq_of_groupoid_hom (M := M) f

example (M : HyperserialModel Int) {a b : HExpr}
    (h : Nonempty (GObj a ⟶ GObj b)) :
    canonicalDescClass (M := M) (Quot.mk _ a : NormalizedQuotient (M := M)) =
      canonicalDescClass (M := M) (Quot.mk _ b : NormalizedQuotient (M := M)) :=
  canonicalDescClass_mk_eq_of_connected (M := M) h

end
end Numbers
end Tests
end HeytingLean
