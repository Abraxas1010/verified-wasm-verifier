import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.Quotient
import HeytingLean.IteratedVirtual.GlobularIndex

/-!
# IteratedVirtual.GlobeCategoryPresented

A “standard presentation” of the **globe category**:

- Objects: natural numbers (dimensions).
- Generators: `σₙ, τₙ : n ⟶ n+1`.
- Relations (globular identities):
  - `σₙ ≫ σₙ₊₁ = σₙ ≫ τₙ₊₁`
  - `τₙ ≫ σₙ₊₁ = τₙ ≫ τₙ₊₁`

Implementation strategy (Mathlib reuse):
- Start from the free path category on the generating quiver (`CategoryTheory.Paths`).
- Quotient by the above relations using `CategoryTheory.Quotient`.

We also provide a canonical functor from this presented category into HeytingLean’s existing
strict encoding `GlobularIndex`.
-/

namespace HeytingLean
namespace IteratedVirtual

open CategoryTheory

namespace GlobeCategoryPresented

/-!
## Objects and generators (as a quiver)
-/

/-- Objects of the presented globe category: just a wrapper around `Nat` to avoid instance clashes. -/
structure Obj where
  n : Nat
deriving DecidableEq, Repr

abbrev ofNat (n : Nat) : Obj := ⟨n⟩

/-- Generating arrows `σₙ, τₙ : n ⟶ n+1`. -/
inductive Gen : Obj → Obj → Type
  | sigma (n : Nat) : Gen (ofNat n) (ofNat (n + 1))
  | tau (n : Nat) : Gen (ofNat n) (ofNat (n + 1))

instance : Quiver Obj where
  Hom := Gen

abbrev PathsCat : Type :=
  CategoryTheory.Paths Obj

namespace PathsCat

instance : Category PathsCat :=
  CategoryTheory.Paths.categoryPaths (V := Obj)

/-- The generating morphism `σₙ : n ⟶ n+1` in the path category. -/
def sigma (n : Nat) : Quiver.Path (ofNat n) (ofNat (n + 1)) :=
  Quiver.Hom.toPath (Gen.sigma n)

/-- The generating morphism `τₙ : n ⟶ n+1` in the path category. -/
def tau (n : Nat) : Quiver.Path (ofNat n) (ofNat (n + 1)) :=
  Quiver.Hom.toPath (Gen.tau n)

end PathsCat

/-!
## Relations (as a `HomRel` on the path category)
-/

inductive Rel : HomRel PathsCat
  | sigma_sigma_eq_sigma_tau (n : Nat) :
      Rel (PathsCat.sigma n ≫ PathsCat.sigma (n + 1)) (PathsCat.sigma n ≫ PathsCat.tau (n + 1))
  | tau_sigma_eq_tau_tau (n : Nat) :
      Rel (PathsCat.tau n ≫ PathsCat.sigma (n + 1)) (PathsCat.tau n ≫ PathsCat.tau (n + 1))

/-- The presented globe category as a quotient of the free path category by the globular relations. -/
abbrev GlobeCat : Type :=
  CategoryTheory.Quotient Rel

namespace GlobeCat

instance : Category GlobeCat :=
  inferInstanceAs (Category (CategoryTheory.Quotient Rel))

/-- The quotient functor `PathsCat ⥤ GlobeCat`. -/
abbrev quotientFunctor : PathsCat ⥤ GlobeCat :=
  CategoryTheory.Quotient.functor Rel

/-- The object (dimension) `n` in `GlobeCat`. -/
abbrev obj (n : Nat) : GlobeCat :=
  quotientFunctor.obj (ofNat n)

/-- The generating `σₙ` in the presented globe category. -/
abbrev sigma (n : Nat) : obj n ⟶ obj (n + 1) :=
  quotientFunctor.map (PathsCat.sigma n)

/-- The generating `τₙ` in the presented globe category. -/
abbrev tau (n : Nat) : obj n ⟶ obj (n + 1) :=
  quotientFunctor.map (PathsCat.tau n)

theorem sigma_sigma_eq_sigma_tau (n : Nat) :
    sigma n ≫ sigma (n + 1) = sigma n ≫ tau (n + 1) := by
  simpa [sigma, tau, quotientFunctor] using
    (CategoryTheory.Quotient.sound (r := Rel) (Rel.sigma_sigma_eq_sigma_tau n))

theorem tau_sigma_eq_tau_tau (n : Nat) :
    tau n ≫ sigma (n + 1) = tau n ≫ tau (n + 1) := by
  simpa [sigma, tau, quotientFunctor] using
    (CategoryTheory.Quotient.sound (r := Rel) (Rel.tau_sigma_eq_tau_tau n))

end GlobeCat

/-!
## Connection to the existing strict `GlobularIndex`

We map the generators to `GlobularIndex.src` / `GlobularIndex.tgt` and lift through the quotient.
-/

namespace ToGlobularIndex

/-- Generator-level prefunctor from the globe quiver to `GlobularIndex`. -/
def genPrefunctor : Obj ⥤q GlobularIndex.Obj where
  obj o := GlobularIndex.ofNat o.n
  map := fun {_ _} g =>
    match g with
    | Gen.sigma n => GlobularIndex.src n
    | Gen.tau n => GlobularIndex.tgt n

/-- The induced functor from the path category to `GlobularIndex`. -/
def pathsFunctor : PathsCat ⥤ GlobularIndex.Obj :=
  CategoryTheory.Paths.lift genPrefunctor

@[simp] theorem pathsFunctor_map_sigma (n : Nat) :
    pathsFunctor.map (PathsCat.sigma n) = GlobularIndex.src n := by
  simp [pathsFunctor, PathsCat.sigma, genPrefunctor]

@[simp] theorem pathsFunctor_map_tau (n : Nat) :
    pathsFunctor.map (PathsCat.tau n) = GlobularIndex.tgt n := by
  simp [pathsFunctor, PathsCat.tau, genPrefunctor]

/-- The induced functor from the presented globe category to `GlobularIndex`. -/
def functor : GlobeCat ⥤ GlobularIndex.Obj :=
  CategoryTheory.Quotient.lift (r := Rel) pathsFunctor (by
    intro x y f₁ f₂ h
    cases h with
    | sigma_sigma_eq_sigma_tau n =>
        -- In `GlobularIndex` this relation is definitional due to left-biased composition.
        simpa [pathsFunctor, PathsCat.sigma, PathsCat.tau, genPrefunctor, GlobularIndex.src, GlobularIndex.tgt] using
          (GlobularIndex.src_src_eq_src_tgt n)
    | tau_sigma_eq_tau_tau n =>
        simpa [pathsFunctor, PathsCat.sigma, PathsCat.tau, genPrefunctor, GlobularIndex.src, GlobularIndex.tgt] using
          (GlobularIndex.tgt_src_eq_tgt_tgt n))

end ToGlobularIndex

end GlobeCategoryPresented

end IteratedVirtual
end HeytingLean
