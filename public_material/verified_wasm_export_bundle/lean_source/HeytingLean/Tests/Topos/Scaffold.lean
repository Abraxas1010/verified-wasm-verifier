import HeytingLean.Topos.LocalOperator
import HeytingLean.Topos.LTfromNucleus
import HeytingLean.Topos.SheafBridges
import HeytingLean.LoF.Instances
import Mathlib.CategoryTheory.Topos.Classifier

open CategoryTheory

namespace HeytingLean
namespace Tests
namespace Topos

/-! Smoke checks for Topos scaffolding. -/

-- LocalOperator type is available and accepts a closure family
section
  universe u v
  variable (C : Type u) [Category.{v} C] [CategoryTheory.Limits.HasPullbacks C]

  #check HeytingLean.Topos.LocalOperator C
  #check HeytingLean.Topos.LocalOperator.IsClosed
  #check HeytingLean.Topos.LocalOperator.isClosed_pullback

  -- Packaging a closure family into a LocalOperator (signature only)
  variable (cl : ∀ X : C, ClosureOperator (Subobject X))
  variable (pull : ∀ {X Y : C} (f : Y ⟶ X) (S : Subobject X),
      (Subobject.pullback f).obj (cl X S) = cl Y ((Subobject.pullback f).obj S))
  #check HeytingLean.Topos.LTfromNucleus.ofClosureFamily (C := C) cl pull
  -- Lawvere–Tierney scaffolds (type-level only)
  variable [CategoryTheory.HasClassifier C]
  #check HeytingLean.Topos.LTfromNucleus.LawvereTierney (C := C)
  #check HeytingLean.Topos.LTfromNucleus.ofLawvereTierney (C := C)
  #check HeytingLean.Topos.LTfromNucleus.ofClassifier (C := C)
  #check HeytingLean.Topos.LTfromNucleus.reclassify (C := C)
  #check HeytingLean.Topos.LTfromNucleus.LawvereTierneyKit (C := C)
  #check HeytingLean.Topos.LTfromNucleus.ofLawvereTierneyKit (C := C)
  #check HeytingLean.Topos.LTfromNucleus.ofClassifierKit (C := C)
  #check HeytingLean.Topos.LTfromNucleus.ofLawvereTierneyDefault (C := C)
  -- Monotonicity/idempotence helpers for `reclassify` (type-level checks)
  variable (kit : HeytingLean.Topos.LTfromNucleus.LawvereTierneyKit (C := C))
  variable {X : C}
  #check (Monotone fun S : Subobject X => HeytingLean.Topos.LTfromNucleus.reclassify (C := C) kit.j S)
  #check (HeytingLean.Topos.LTfromNucleus.reclassify_monotone (C := C) kit (X := X))
  #check (HeytingLean.Topos.LTfromNucleus.reclassify_le_of_le (C := C) kit (X := X))
  variable (S : Subobject X)
  #check (HeytingLean.Topos.LTfromNucleus.reclassify_idem (C := C) kit (X := X) S)

  -- Explicit-classifier API and naturality (type-level only)
  variable (c : CategoryTheory.Classifier C)
  #check HeytingLean.Topos.LTfromNucleus.reclassifyWith (C := C) c
  variable (f : X ⟶ X)
  variable (jc : c.Ω ⟶ c.Ω)
  #check (HeytingLean.Topos.LTfromNucleus.reclassifyWith_pullback_naturality (C := C) c (f := f) jc (S := S))
  -- Derived naturality for implicit-classifier flavor
  variable (j' : CategoryTheory.HasClassifier.Ω C ⟶ CategoryTheory.HasClassifier.Ω C)
  #check (HeytingLean.Topos.LTfromNucleus.reclassify_pullback_naturality (C := C) (f := f) j' (S := S))
  -- Composition shape (explicit classifier flavor)
  #check ((fun (S : Subobject X) =>
            HeytingLean.Topos.LTfromNucleus.reclassifyWith (C := C) c (jc ≫ jc) S)
          =
          (fun (S : Subobject X) =>
            HeytingLean.Topos.LTfromNucleus.reclassifyWith (C := C) c jc
              (HeytingLean.Topos.LTfromNucleus.reclassifyWith (C := C) c jc S)))
  -- Reverse skeleton: closure at Ω from LocalOperator
  variable (Jop : HeytingLean.Topos.LocalOperator C)
  #check HeytingLean.Topos.LTfromNucleus.closureAtOmega (C := C) Jop
  -- Provide a concrete `Ωα` so the `PrimaryAlgebra` instance is not an inference error.
  #check HeytingLean.Topos.LTfromNucleus.ToReentrySpec (Ωα := Set Bool) (C := C)
  -- Advanced classifier-kit bridges deferred; basic checks only

  -- Identity-case and composition shapes (type-level only)
  variable [CategoryTheory.HasClassifier C]
  variable {X : C}
  variable (S : Subobject X)
  #check (HeytingLean.Topos.LTfromNucleus.reclassify (C := C) (𝟙 (CategoryTheory.HasClassifier.Ω C)) S = S)
  variable (j : CategoryTheory.HasClassifier.Ω C ⟶ CategoryTheory.HasClassifier.Ω C)
  #check ((fun (S : Subobject X) =>
            HeytingLean.Topos.LTfromNucleus.reclassify (C := C) (j ≫ j) S)
          =
          (fun (S : Subobject X) =>
            HeytingLean.Topos.LTfromNucleus.reclassify (C := C) j
              (HeytingLean.Topos.LTfromNucleus.reclassify (C := C) j S)))
end

-- Subobject classifier APIs exist
section
  universe u v
  variable (C : Type u) [Category.{v} C]
  variable [CategoryTheory.HasClassifier C]

  #check CategoryTheory.HasClassifier.Ω C
  #check CategoryTheory.HasClassifier.truth (C := C)
end

-- Sheafification adjunction aliases
section
  universe u v w
  variable (C : Type u) [Category.{v} C]
  variable (A : Type w) [Category.{max v w} A]
  variable (J : GrothendieckTopology C)

  variable [CategoryTheory.HasWeakSheafify J A]
  #check HeytingLean.Topos.SheafBridges.presheafToSheaf (C := C) (A := A) J
  #check HeytingLean.Topos.SheafBridges.sheafificationAdjunction (C := C) (A := A) J
  -- Names exposed by mathlib through our facade
  #check CategoryTheory.sheafificationAdjunction J A
  #check CategoryTheory.presheafToSheaf J A
end

end Topos
end Tests
end HeytingLean
