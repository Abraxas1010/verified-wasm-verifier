import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.Order.Filter.Cofinite
import HeytingLean.Embeddings.GenericLensData

/-!
# Embeddings.Adelic

An “adelic-like” multi-lens carrier for proofs/programs.

Key design choice: reuse Mathlib’s `RestrictedProduct` with the **cofinite** filter:
an element is a dependent function `∀ ℓ, Completion ℓ` together with the property that
“for all but finitely many lenses ℓ, the component is integral/canonical”.

This matches the classical adele definition pattern and avoids reimplementing the
restricted-product infrastructure.

**Migration note:** `LensData` is now a compatibility alias to
`GenericLensData LensID`; new development should use `GenericLensData` directly.
-/

namespace HeytingLean
namespace Embeddings

/-- Lens identifiers aligned with the repo’s existing exported “views”. -/
inductive LensID where
  | omega
  | region
  | graph
  | clifford
  | tensor
  | topology
  | matula
deriving DecidableEq, Repr

/-- Legacy compatibility alias to generic lens data at the 7-lens index type. -/
abbrev LensData := GenericLensData.GenericLensData LensID

open scoped RestrictedProduct

/-- Generic restricted-product carrier over any perspective index type. -/
abbrev GenericAdelicRep {τ : Type*} (data : GenericLensData.GenericLensData τ) : Type _ :=
  RestrictedProduct (R := data.Completion) (A := data.Integral) Filter.cofinite

/-- Legacy compatibility alias for lens-indexed restricted products. -/
abbrev AdelicRep (data : LensData) : Type _ :=
  GenericAdelicRep data

/-- Generic per-tag precision assignment. -/
abbrev GenericPrecision (τ : Type*) : Type _ := GenericLensData.GenericPrecision τ

/-- Legacy per-lens precision assignment. -/
abbrev Precision : Type := GenericPrecision LensID

/-- Generic truncation-based approximation relation. -/
def GenericApprox {τ : Type*} (data : GenericLensData.GenericLensData τ) (prec : GenericPrecision τ)
    (x y : GenericAdelicRep data) : Prop :=
  ∀ tag, data.truncate tag (prec tag) (x.1 tag) = data.truncate tag (prec tag) (y.1 tag)

/-- Legacy truncation-based approximation over `LensID`. -/
def Approx (data : LensData) (prec : Precision) (x y : AdelicRep data) : Prop :=
  ∀ lens,
    data.truncate lens (prec lens) (x.1 lens) =
      data.truncate lens (prec lens) (y.1 lens)

/-! ## A finite-support constructor (computationally friendly) -/

/-- A finitely-supported adelic element: only finitely many lenses may be non-integral. -/
structure FinSupport (data : LensData) where
  support : Finset LensID
  value : ∀ lens, data.Completion lens
  integral_outside : ∀ lens, lens ∉ support → value lens ∈ data.Integral lens

namespace FinSupport

/-- Convert a finitely-supported value into the Mathlib `RestrictedProduct` carrier. -/
def toAdelic {data : LensData} (fs : FinSupport data) : AdelicRep data :=
  ⟨fs.value, by
    -- `∀ᶠ lens in cofinite, fs.value lens ∈ Integral lens` ⇔ finitely many exceptions.
    refine (Filter.eventually_cofinite.2 ?_)
    refine fs.support.finite_toSet.subset ?_
    intro lens hNotIntegral
    by_cases hMem : lens ∈ fs.support
    · exact hMem
    · exfalso
      exact hNotIntegral (fs.integral_outside lens hMem)⟩

end FinSupport

namespace GenericLensData

/-- Specialize generic lens data back to the legacy `LensData` alias. -/
def toLensData (gld : GenericLensData LensID) : LensData :=
  gld

/-- Lift legacy `LensData` to generic lens data (definitional identity). -/
def ofLensData (ld : LensData) : GenericLensData LensID :=
  ld

@[simp] theorem toLensData_ofLensData (ld : LensData) :
    toLensData (ofLensData ld) = ld := rfl

@[simp] theorem ofLensData_toLensData (gld : GenericLensData LensID) :
    ofLensData (toLensData gld) = gld := rfl

end GenericLensData

end Embeddings
end HeytingLean
