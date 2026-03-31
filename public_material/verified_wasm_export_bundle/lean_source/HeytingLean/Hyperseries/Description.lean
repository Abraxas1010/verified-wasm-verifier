import Mathlib.Logic.Equiv.Basic

namespace HeytingLean
namespace Hyperseries

/--
Canonical hyperserial description interface.

For `K := Surreal`, this is the abstraction point for the
"every surreal has a unique hyperserial description" theorem.
-/
class HyperserialDescription (K : Type*) where
  HS : Type*
  describe : K → HS
  realize : HS → K
  realize_describe : ∀ k : K, realize (describe k) = k
  describe_realize : ∀ h : HS, describe (realize h) = h

/-- Canonical hyperserial-description carrier associated to a target `K`. -/
abbrev HDesc (K : Type*) [HyperserialDescription K] : Type* :=
  HyperserialDescription.HS (K := K)

namespace HyperserialDescription

/--
Bootstrap constructor: use `K` itself as the description carrier.
This is useful for concrete smoke tests while richer description objects are developed.
-/
def idDescription (K : Type*) : HyperserialDescription K where
  HS := K
  describe := fun k => k
  realize := fun h => h
  realize_describe := by
    intro k
    rfl
  describe_realize := by
    intro h
    rfl

variable {K : Type*} [HyperserialDescription K]

@[simp] theorem realize_describe' (k : K) :
    HyperserialDescription.realize (K := K) (HyperserialDescription.describe (K := K) k) = k :=
  HyperserialDescription.realize_describe (K := K) k

@[simp] theorem describe_realize' (h : HDesc K) :
    HyperserialDescription.describe (K := K) (HyperserialDescription.realize (K := K) h) = h :=
  HyperserialDescription.describe_realize (K := K) h

/-- Canonical equivalence between descriptions and values. -/
noncomputable def equiv : HDesc K ≃ K where
  toFun := HyperserialDescription.realize (K := K)
  invFun := HyperserialDescription.describe (K := K)
  left_inv := by
    intro h
    exact describe_realize' (K := K) h
  right_inv := by
    intro k
    exact realize_describe' (K := K) k

theorem ext {h₁ h₂ : HDesc K}
    (hh :
      HyperserialDescription.realize (K := K) h₁ =
        HyperserialDescription.realize (K := K) h₂) : h₁ = h₂ := by
  have :
      HyperserialDescription.describe (K := K)
          (HyperserialDescription.realize (K := K) h₁) =
        HyperserialDescription.describe (K := K)
          (HyperserialDescription.realize (K := K) h₂) :=
    congrArg (HyperserialDescription.describe (K := K)) hh
  simpa [HyperserialDescription.describe_realize] using this

/-- Existence+uniqueness of a hyperserial description for each `a : K`. -/
theorem existsUnique (a : K) :
    ∃! h : HDesc K, HyperserialDescription.realize (K := K) h = a := by
  refine ⟨HyperserialDescription.describe (K := K) a, by simp, ?_⟩
  intro h hh
  apply ext (K := K)
  calc
    HyperserialDescription.realize (K := K) h = a := hh
    _ = HyperserialDescription.realize (K := K) (HyperserialDescription.describe (K := K) a) := by
      exact (HyperserialDescription.realize_describe (K := K) a).symm

end HyperserialDescription
end Hyperseries
end HeytingLean
