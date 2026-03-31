import HeytingLean.LoF.Nucleus
import Mathlib.Order.Nucleus
import Mathlib.Order.Closure
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Topos.Classifier
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import HeytingLean.Topos.LocalOperator

namespace HeytingLean
namespace Topos
namespace LTfromNucleus

open CategoryTheory

universe u v w u₀ v₀

variable (C : Type u) [Category.{v} C] [CategoryTheory.Limits.HasPullbacks C]

/-- Convenience alias for the ambient truth-values object in a category with classifier. -/
noncomputable abbrev Omega [Category C] [CategoryTheory.HasClassifier C] : C :=
  CategoryTheory.HasClassifier.Ω C

/-- A lightweight wrapper for a Lawvere–Tierney-like endomorphism on the
truth object `Ω` of a category with a subobject classifier. This scaffold
captures only the underlying arrow `j : Ω ⟶ Ω` (no axioms), to be paired
with a closure family on subobjects when constructing a `LocalOperator`.
-/
structure LawvereTierney [Category C] [CategoryTheory.HasClassifier C] where
  j : (CategoryTheory.HasClassifier.Ω C) ⟶ (CategoryTheory.HasClassifier.Ω C)

/-- Repackage a given family of closure operators on subobjects and a
pullback-stability proof into a LocalOperator. This is a convenience
constructor used by downstream bridges.
-/
def ofClosureFamily
  (cl : ∀ X : C, ClosureOperator (Subobject X))
  (pullback_stable : ∀ {X Y : C} (f : Y ⟶ X) (S : Subobject X),
      (Subobject.pullback f).obj (cl X S) = cl Y ((Subobject.pullback f).obj S)) :
  HeytingLean.Topos.LocalOperator C :=
  { cl := cl
    pullback_stable := by
      intro X Y f S
      exact (pullback_stable (X := X) (Y := Y) f S) }

/-- Reclassify a subobject `S ⊆ X` along a `j : Ω ⟶ Ω` by postcomposing the
characteristic map `χ_S : X ⟶ Ω` with `j`, then taking the corresponding
pullback of the truth arrow as a new subobject of `X`.

This is the standard way to produce the underlying endofunction on
`Subobject X` from a Lawvere–Tierney endomorphism on `Ω`.
-/
noncomputable def reclassify
  [CategoryTheory.HasClassifier C]
  (j : (CategoryTheory.HasClassifier.Ω C) ⟶ (CategoryTheory.HasClassifier.Ω C))
  {X : C} (S : Subobject X) : Subobject X :=
  let c := (CategoryTheory.HasClassifier.exists_classifier (C := C)).some
  have χS : X ⟶ c.Ω := (c.χ (m := S.arrow))
  (CategoryTheory.Classifier.representableBy (C := C) c).homEquiv (χS ≫ j)

/-- A version of `reclassify` that takes an explicit classifier `c`.
Keeping the classifier explicit makes proofs via representability more robust. -/
noncomputable def reclassifyWith
  [CategoryTheory.HasClassifier C]
  (c : CategoryTheory.Classifier C)
  (j : c.Ω ⟶ c.Ω)
  {X : C} (S : Subobject X) : Subobject X :=
  (CategoryTheory.Classifier.representableBy (C := C) c).homEquiv ((c.χ (m := S.arrow)) ≫ j)

-- (Helper lemmas for `reclassify` (identity and pullback-naturality) will be
-- added in a follow-up proof pass.)

-- (Helper lemmas for `reclassify` (identity and pullback-naturality) will be
-- added in a follow-up proof pass.)

/-- Reclassifying along the identity on `Ω` does nothing. -/
@[simp]
theorem reclassify_id
  [CategoryTheory.HasClassifier C]
  {X : C} (S : Subobject X) :
  reclassify (C := C) (𝟙 (CategoryTheory.HasClassifier.Ω C)) S = S := by
  classical
  -- Directly via the classifier representation equivalence.
  simp [reclassify, Category.comp_id, CategoryTheory.Classifier.representableBy]

/-! ### Helpers -/

/-- Characteristic maps commute with pullback: the χ of the pulled-back subobject
is the composition of the original χ with the pullback morphism. -/
@[simp]
theorem chi_pullback_char
  [CategoryTheory.HasClassifier C]
  (c : CategoryTheory.Classifier C)
  {X Y : C} (f : Y ⟶ X) (S : Subobject X) :
  c.χ ((Subobject.pullback f).obj S).arrow = f ≫ (c.χ (m := S.arrow)) := by
  classical
  let h := (CategoryTheory.Classifier.representableBy (C := C) c)
  have H :=
    (CategoryTheory.Functor.RepresentableBy.comp_homEquiv_symm (e := h) (x := S) (f := f))
  -- `H`: `f ≫ h.homEquiv.symm S = h.homEquiv.symm ((Subobject.pullback f).obj S)`.
  -- Rewrite `h.homEquiv.symm` via the classifier representation.
  simpa [CategoryTheory.Classifier.representableBy] using H.symm

/-- Pullback commutes with `reclassifyWith` (explicit classifier version). -/
@[simp]
theorem reclassifyWith_pullback_naturality
  [CategoryTheory.HasClassifier C]
  (c : CategoryTheory.Classifier C)
  {X Y : C} (f : Y ⟶ X)
  (j : c.Ω ⟶ c.Ω)
  (S : Subobject X) :
  (Subobject.pullback f).obj (reclassifyWith (C := C) c j S)
    = reclassifyWith (C := C) c j ((Subobject.pullback f).obj S) := by
  classical
  -- Shorthand for the representability equivalence
  let h := (CategoryTheory.Classifier.representableBy (C := C) c)
  -- Move pullback across `homEquiv` and use the χ-pullback lemma.
  calc
    (Subobject.pullback f).obj (reclassifyWith (C := C) c j S)
        = (Subobject.pullback f).obj (h.homEquiv ((c.χ (m := S.arrow)) ≫ j)) := rfl
    _   = h.homEquiv ((f ≫ (c.χ (m := S.arrow))) ≫ j) := by
            simpa [reclassifyWith, Category.assoc] using
              (h.homEquiv_comp (f) ((c.χ (m := S.arrow)) ≫ j)).symm
    _   = h.homEquiv ((c.χ ((Subobject.pullback f).obj S).arrow) ≫ j) := by
            simp [Category.assoc, chi_pullback_char (C := C) c f S]
    _   = reclassifyWith (C := C) c j ((Subobject.pullback f).obj S) := rfl

@[simp]
theorem reclassify_pullback_naturality
  [CategoryTheory.HasClassifier C]
  {X Y : C} (f : Y ⟶ X)
  (j : (CategoryTheory.HasClassifier.Ω C) ⟶ (CategoryTheory.HasClassifier.Ω C))
  (S : Subobject X) :
  (Subobject.pullback f).obj (reclassify (C := C) j S)
    = reclassify (C := C) j ((Subobject.pullback f).obj S) := by
  classical
  -- Choose an explicit classifier and reuse the explicit lemma.
  let c := (CategoryTheory.HasClassifier.exists_classifier (C := C)).some
  simpa [reclassify, reclassifyWith] using
    reclassifyWith_pullback_naturality (C := C) c f j S

-- (A pullback-naturality lemma for `reclassify` will be added in a
-- subsequent proof pass; it follows from representability and the
-- canonical presentation of subobjects via characteristic maps.)
/-- A packaging of a Lawvere–Tierney arrow `j : Ω ⟶ Ω` together with the
key axioms required to build a `ClosureOperator` on each `Subobject X`
via `reclassify (χ_S ≫ j)`, and the naturality of this construction under
pullback. This keeps the heavy proof obligations out of the core and lets
downstream code assemble a `LocalOperator` from a trusted kit.
-/
structure LawvereTierneyKit [Category C] [CategoryTheory.Limits.HasPullbacks C]
  [CategoryTheory.HasClassifier C] where
  j : (CategoryTheory.HasClassifier.Ω C) ⟶ (CategoryTheory.HasClassifier.Ω C)
  extensive : ∀ {X : C}, ∀ (S : Subobject X), S ≤ reclassify (C := C) j S
  minimal : ∀ {X : C} (x y : Subobject X), x ≤ reclassify (C := C) j y →
    reclassify (C := C) j x ≤ reclassify (C := C) j y
  pullback_stable : ∀ {X Y : C} (f : Y ⟶ X) (S : Subobject X),
    (Subobject.pullback f).obj (reclassify (C := C) j S)
      = reclassify (C := C) j ((Subobject.pullback f).obj S)

/-! #### Basic properties from a `LawvereTierneyKit` -/

/-- Monotonicity helper: if `x ≤ y` then `reclassify j x ≤ reclassify j y`,
deduced from `extensive` and the `minimal` rule in the kit. -/
theorem reclassify_le_of_le
  [CategoryTheory.HasClassifier C]
  (kit : LawvereTierneyKit (C := C))
  {X : C} {x y : Subobject X} (hxy : x ≤ y) :
  reclassify (C := C) kit.j x ≤ reclassify (C := C) kit.j y := by
  have hy : y ≤ reclassify (C := C) kit.j y := kit.extensive y
  exact kit.minimal x y (le_trans hxy hy)

/-- The map `S ↦ reclassify j S` is monotone for any `LawvereTierneyKit`. -/
theorem reclassify_monotone
  [CategoryTheory.HasClassifier C]
  (kit : LawvereTierneyKit (C := C))
  {X : C} :
  Monotone (fun S : Subobject X => reclassify (C := C) kit.j S) := by
  intro x y hxy; exact reclassify_le_of_le (C := C) kit (X := X) hxy

/-- Idempotence helper: applying `reclassify j` twice is the same as once,
deduced from `extensive` and `minimal`. -/
theorem reclassify_idem
  [CategoryTheory.HasClassifier C]
  (kit : LawvereTierneyKit (C := C))
  {X : C} (S : Subobject X) :
  reclassify (C := C) kit.j (reclassify (C := C) kit.j S)
    = reclassify (C := C) kit.j S := by
  apply le_antisymm
  · -- `reclassify (reclassify S) ≤ reclassify S` by `minimal` and reflexivity
    have h : reclassify (C := C) kit.j S ≤ reclassify (C := C) kit.j S := le_rfl
    simpa using kit.minimal (X := X) (x := reclassify (C := C) kit.j S) (y := S) h
  · -- `reclassify S ≤ reclassify (reclassify S)` by `extensive`
    simpa using kit.extensive (X := X) (S := reclassify (C := C) kit.j S)

-- (A naturality lemma for `reclassify` under pullback can be established via
-- `Classifier.representableBy.homEquiv_comp` and naturality of characteristic
-- maps. We keep this as a future extension when wiring full LT axioms.)

/-- Package a `LocalOperator` from a Lawvere–Tierney scaffold together with a
closure family and its naturality under pullback. This keeps the type-level
bridge explicit without committing to proof obligations here. The intended
use is that `cl` acts on a subobject `S` of `X` by reclassifying `j ∘ χ_S`.
-/
def ofLawvereTierney
  [CategoryTheory.HasClassifier C]
  (_lt : LawvereTierney (C := C))
  (cl : ∀ X : C, ClosureOperator (Subobject X))
  (pullback_stable : ∀ {X Y : C} (f : Y ⟶ X) (S : Subobject X),
      (Subobject.pullback f).obj (cl X S) = cl Y ((Subobject.pullback f).obj S)) :
  HeytingLean.Topos.LocalOperator C :=
  ofClosureFamily (C := C) cl pullback_stable

/-- Assemble a `LocalOperator` from a `LawvereTierneyKit` by packaging
the `reclassify` action into a `ClosureOperator` on each `Subobject X`.
This uses `ClosureOperator.mk₂` with the `extensive` and `minimal` fields
from the kit, and naturality from `pullback_stable`.
-/
noncomputable def ofLawvereTierneyKit
  [CategoryTheory.Limits.HasPullbacks C]
  [CategoryTheory.HasClassifier C]
  (kit : LawvereTierneyKit (C := C)) :
  HeytingLean.Topos.LocalOperator C :=
  let cl : ∀ X : C, ClosureOperator (Subobject X) := fun _X =>
    ClosureOperator.mk₂ (fun S => reclassify (C := C) kit.j S)
      (fun S => kit.extensive S)
      (fun {x y} h => kit.minimal x y h)
  ofClosureFamily (C := C) cl (fun f S => kit.pullback_stable f S)

/-- For a `LocalOperator` built from a `LawvereTierneyKit`, closed subobjects
are exactly the fixed points of `reclassify j` on each `Subobject X`. -/
@[simp] theorem ofLawvereTierneyKit_isClosed_iff
  [CategoryTheory.HasClassifier C]
  (kit : LawvereTierneyKit (C := C))
  {X : C} (S : Subobject X) :
  HeytingLean.Topos.LocalOperator.IsClosed
      (C := C) (ofLawvereTierneyKit (C := C) kit) S
    ↔ reclassify (C := C) kit.j S = S := by
  -- Unfold `IsClosed` and the `LocalOperator` built from the kit.
  rfl

/-- The trivial Lawvere–Tierney kit given by the identity on `Ω`. -/
noncomputable def idLawvereTierneyKit
  [CategoryTheory.Limits.HasPullbacks C]
  [CategoryTheory.HasClassifier C] :
  LawvereTierneyKit (C := C) :=
  { j := 𝟙 (CategoryTheory.HasClassifier.Ω C)
    extensive := by
      intro X S
      -- For `j = 𝟙 Ω`, `reclassify` is definitionally the identity.
      simp [reclassify_id (C := C)]
    minimal := by
      intro X x y h
      -- Under `j = 𝟙 Ω`, minimality reduces to monotonicity of the identity.
      simpa [reclassify_id (C := C)] using h
    pullback_stable := by
      intro X Y f S
      -- Use the general pullback-naturality lemma specialized to `j = 𝟙 Ω`.
      exact reclassify_pullback_naturality (C := C) f
        (𝟙 (CategoryTheory.HasClassifier.Ω C)) S }

/-- The identity local operator on subobjects, induced by the identity
Lawvere–Tierney arrow on `Ω`. -/
noncomputable def idLocalOperator
  [CategoryTheory.Limits.HasPullbacks C]
  [CategoryTheory.HasClassifier C] :
  HeytingLean.Topos.LocalOperator C :=
  ofLawvereTierneyKit (C := C) (idLawvereTierneyKit (C := C))

/-- The identity `LocalOperator` acts as the identity closure on every subobject. -/
@[simp] theorem idLocalOperator_cl
  [CategoryTheory.HasClassifier C]
  (X : C) (S : Subobject X) :
  (idLocalOperator (C := C)).cl X S = S := by
  classical
  -- Expand the definition of the identity local operator and use `reclassify_id`.
  simp [idLocalOperator, ofLawvereTierneyKit, ofClosureFamily,
        idLawvereTierneyKit, reclassify_id]

/-- A classifier-oriented alias identical to `ofLawvereTierney`. Provided for
symmetry with documentation that derives the closure family via characteristic
maps and the endomorphism `j` on `Ω`.
-/
def ofClassifier
  [CategoryTheory.HasClassifier C]
  (_j : (CategoryTheory.HasClassifier.Ω C) ⟶ (CategoryTheory.HasClassifier.Ω C))
  (cl : ∀ X : C, ClosureOperator (Subobject X))
  (pullback_stable : ∀ {X Y : C} (f : Y ⟶ X) (S : Subobject X),
      (Subobject.pullback f).obj (cl X S) = cl Y ((Subobject.pullback f).obj S)) :
  HeytingLean.Topos.LocalOperator C :=
  ofClosureFamily (C := C) cl pullback_stable

/-- Assemble a `LocalOperator` directly from a classifier arrow `j : Ω ⟶ Ω`
and a proof kit carrying the `extensive/minimal/pullback_stable` axioms with
respect to `reclassify`. This is a convenience alias around
`ofLawvereTierneyKit`.
-/
noncomputable def ofClassifierKit
  [CategoryTheory.Limits.HasPullbacks C]
  [CategoryTheory.HasClassifier C]
  (kit : LawvereTierneyKit (C := C)) :
  HeytingLean.Topos.LocalOperator C :=
  ofLawvereTierneyKit (C := C) kit

/-- Default builder that constructs a `LocalOperator` directly from a
Lawvere–Tierney arrow `j : Ω ⟶ Ω`, given the three standard closure
properties for the reclassification action:

- `extensive`: each subobject is contained in its reclassification,
- `minimal`: the monotone/idempotent form used by `ClosureOperator.mk₂`, and
- `pullback_stable`: the construction commutes with pullback.

It packages the provided facts into a `LawvereTierneyKit` and delegates
to `ofLawvereTierneyKit`. With the kit established, you can use
`reclassify_monotone` and `reclassify_idem` to obtain monotonicity and
idempotence of the closure `S ↦ reclassify j S` in any `Subobject X`.

Usage (kit-derived helpers):
  Given `kit : LawvereTierneyKit (C := C)`, for any object `X`:
  - Monotone: `reclassify_monotone (C := C) kit (X := X)`.
  - Idempotent: for `S : Subobject X`,
      `reclassify_idem (C := C) kit (X := X) S`.
These facts are convenient when reasoning about the closure behavior in
downstream code that uses this builder.
-/
noncomputable def ofLawvereTierneyDefault
  [CategoryTheory.Limits.HasPullbacks C]
  [CategoryTheory.HasClassifier C]
  (j : (CategoryTheory.HasClassifier.Ω C) ⟶ (CategoryTheory.HasClassifier.Ω C))
  (extensive : ∀ {X : C}, ∀ (S : Subobject X), S ≤ reclassify (C := C) j S)
  (minimal : ∀ {X : C} (x y : Subobject X), x ≤ reclassify (C := C) j y →
    reclassify (C := C) j x ≤ reclassify (C := C) j y)
  (pullback_stable : ∀ {X Y : C} (f : Y ⟶ X) (S : Subobject X),
    (Subobject.pullback f).obj (reclassify (C := C) j S)
      = reclassify (C := C) j ((Subobject.pullback f).obj S)) :
  HeytingLean.Topos.LocalOperator C :=
  let kit : LawvereTierneyKit (C := C) :=
    { j := j
      extensive := by intro X S; simp [extensive (X := X) S]
      minimal := by intro X x y h; simp [minimal (X := X) x y h]
      pullback_stable := by intro X Y f S; exact (pullback_stable (X := X) (Y := Y) f S) }
  ofLawvereTierneyKit (C := C) kit

/-- Reverse direction (skeleton): obtain a closure operator on subobjects
of the truth object `Ω C` from a `LocalOperator`. This captures the
"nucleus on truth values" intuition at the Subobject level. -/
noncomputable def closureAtOmega
  [CategoryTheory.HasClassifier C]
  (J : HeytingLean.Topos.LocalOperator C) :
  ClosureOperator (Subobject (CategoryTheory.HasClassifier.Ω C)) :=
  J.cl (CategoryTheory.HasClassifier.Ω C)

/-- A minimal data sketch showing how a LoF `Reentry` on truth values
can be seen as a nucleus on subobjects of `Ω`, via the `closureAtOmega`
construction applied to a suitable `LocalOperator`.

This stays type-level only: it does not pick a concrete category `C` or
classifier, but makes the intended LoF↔Topos bridge explicit. -/
structure FromReentrySpec
  (Ωα : Type _) [HeytingLean.LoF.PrimaryAlgebra Ωα]
  (C : Type _) [CategoryTheory.Category C]
  [CategoryTheory.Limits.HasPullbacks C] [CategoryTheory.HasClassifier C] where
  R : HeytingLean.LoF.Reentry Ωα
  J : HeytingLean.Topos.LocalOperator C
  Ωobj : C := CategoryTheory.HasClassifier.Ω C
  ΩSubNucleus :
    ClosureOperator (Subobject Ωobj)

/-- Backward-compatible alias for earlier naming in scaffolding/tests. -/
abbrev ToReentrySpec := FromReentrySpec

/-- Canonical builder for `FromReentrySpec` pairing a LoF reentry on
truth values with a chosen categorical local operator. The subobject
closure on `Ω` is obtained via `closureAtOmega J`. -/
noncomputable def FromReentrySpec.build
  (Ωα : Type _) [HeytingLean.LoF.PrimaryAlgebra Ωα]
  (C : Type _) [CategoryTheory.Category C]
  [CategoryTheory.Limits.HasPullbacks C] [CategoryTheory.HasClassifier C]
  (R : HeytingLean.LoF.Reentry Ωα)
  (J : HeytingLean.Topos.LocalOperator C) :
  FromReentrySpec Ωα C :=
  { R := R
    J := J
    Ωobj := CategoryTheory.HasClassifier.Ω C
    ΩSubNucleus := closureAtOmega (C := C) J }

/-- A trivial instance of `FromReentrySpec` pairing a given LoF
`Reentry Ωα` with the identity local operator on a category `C`
with pullbacks and a subobject classifier. This does not assert
any identification between the LoF nucleus and the categorical
closure on `Ω`; it simply records the data needed to talk about
both at once in a single bridge structure. -/
noncomputable def FromReentrySpec.idLocal
  (Ωα : Type _) [HeytingLean.LoF.PrimaryAlgebra Ωα]
  (C : Type _) [CategoryTheory.Category C]
  [CategoryTheory.Limits.HasPullbacks C] [CategoryTheory.HasClassifier C]
  (R : HeytingLean.LoF.Reentry Ωα) :
  FromReentrySpec Ωα C :=
  FromReentrySpec.build (Ωα := Ωα) (C := C) R (idLocalOperator (C := C))


end LTfromNucleus
end Topos
end HeytingLean
